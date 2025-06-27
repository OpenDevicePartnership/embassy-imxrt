/// I2C Master Driver
use core::future::poll_fn;
use core::marker::PhantomData;
use core::sync::atomic::Ordering;
use core::task::Poll;

use embassy_futures::select::{select, Either};
use embassy_hal_internal::drop::OnDrop;
use itertools::Itertools;

use super::{
    force_clear_remediation, wait_remediation_complete, Async, Blocking, Error, Info, Instance, InterruptHandler,
    MasterDma, Mode, Result, SclPin, SdaPin, TransferError, I2C_REMEDIATION, I2C_WAKERS, REMEDIATON_MASTER_STOP,
    TEN_BIT_PREFIX,
};
use crate::flexcomm::FlexcommRef;
use crate::interrupt::typelevel::Interrupt;
use crate::pac::i2c0::msttime::{Mstsclhigh, Mstscllow};
use crate::{dma, interrupt, Peri};

/// Bus speed (nominal SCL, no clock stretching)
#[derive(Clone, Copy)]
pub enum Speed {
    /// 100 kbit/s
    Standard,

    /// 400 kbit/s
    Fast,

    /// 1 Mbit/s
    FastPlus,

    /// 3.4Mbit/s only available for slave devices
    High,
}

/// Divide integers rounding to the nearest whole number rather than always down
fn rounded_divide(numerator: u32, denominator: u32) -> u32 {
    (numerator + denominator / 2) / denominator
}

fn get_duty_cycle(hi_clocks: u8, lo_clocks: u8) -> u8 {
    let total_clocks = u16::from(hi_clocks + lo_clocks);
    (100 * u16::from(hi_clocks) / total_clocks) as u8
}

fn get_freq_hz(hi_clocks: u8, lo_clocks: u8, clock_div_multiplier: u16, clock_speed_hz: u32) -> u32 {
    clock_speed_hz / (u32::from(hi_clocks + lo_clocks) * u32::from(clock_div_multiplier))
}

// We need to be able to convert back to the clocks representation, but can't implement From/Into because
// neither the type nor the trait are defined in our crate.  Therefore, we define this Into-like trait and
// use that instead.
//
trait ToClocksEnum<DestT> {
    fn to_clocks_enum(&self) -> DestT;
}

const MIN_CLOCKS: u8 = 2;
const MAX_CLOCKS: u8 = 9;

impl ToClocksEnum<Mstscllow> for u8 {
    fn to_clocks_enum(&self) -> Mstscllow {
        match *self {
            2 => Mstscllow::Clocks2,
            3 => Mstscllow::Clocks3,
            4 => Mstscllow::Clocks4,
            5 => Mstscllow::Clocks5,
            6 => Mstscllow::Clocks6,
            7 => Mstscllow::Clocks7,
            8 => Mstscllow::Clocks8,
            9 => Mstscllow::Clocks9,
            _ => panic!("Invalid value for Mstscllow"),
        }
    }
}

impl ToClocksEnum<Mstsclhigh> for u8 {
    fn to_clocks_enum(&self) -> Mstsclhigh {
        match *self {
            2 => Mstsclhigh::Clocks2,
            3 => Mstsclhigh::Clocks3,
            4 => Mstsclhigh::Clocks4,
            5 => Mstsclhigh::Clocks5,
            6 => Mstsclhigh::Clocks6,
            7 => Mstsclhigh::Clocks7,
            8 => Mstsclhigh::Clocks8,
            9 => Mstsclhigh::Clocks9,
            _ => panic!("Invalid value for Mstsclhigh"),
        }
    }
}

struct SpeedRegisterSettings {
    scl_high_clocks: Mstsclhigh,
    scl_low_clocks: Mstscllow,
    clock_div_multiplier: u16,

    _actual_freq_hz: u32,
}

impl SpeedRegisterSettings {
    fn new(duty_cycle: DutyCycle, speed: Speed) -> Result<Self> {
        const SFRO_CLOCK_SPEED_HZ: u32 = 16_000_000;

        let target_freq_hz: u32 = match speed {
            Speed::Standard => 100_000,   // 100 KHz
            Speed::Fast => 400_000,       // 400 KHz
            Speed::FastPlus => 1_000_000, // 1 MHz

            _ => return Err(Error::UnsupportedConfiguration),
        };

        // Figure out what we need to set the clock divider to in order to hit the I2C speed the user requested.  Again, we may not
        // be able to be exact, so we need to find the closest viable option.
        //
        let (result_clocks_hi, result_clocks_lo, result_div_multiplier) = (MIN_CLOCKS..=MAX_CLOCKS)
            .cartesian_product(MIN_CLOCKS..=MAX_CLOCKS)
            .filter(|(hi_clocks, lo_clocks)| get_duty_cycle(*hi_clocks, *lo_clocks) == duty_cycle.value)
            .map(|(hi_clocks, lo_clocks)| {
                // As speeds increase, clock_div_multiplier will approach 1, so rounding to the nearest whole number (rather than always down
                // as normal integer division does) can meaningfully reduce error in the actual speed in cases where the remainder is high.
                let clock_div_multiplier =
                    rounded_divide(SFRO_CLOCK_SPEED_HZ, target_freq_hz * u32::from(hi_clocks + lo_clocks)) as u16;
                (hi_clocks, lo_clocks, clock_div_multiplier)
            })
            .min_by(|a, b| {
                let (hi_a, lo_a, div_a) = a;
                let (hi_b, lo_b, div_b) = b;
                let freq_a = get_freq_hz(*hi_a, *lo_a, *div_a, SFRO_CLOCK_SPEED_HZ);
                let freq_b = get_freq_hz(*hi_b, *lo_b, *div_b, SFRO_CLOCK_SPEED_HZ);

                target_freq_hz.abs_diff(freq_a).cmp(&target_freq_hz.abs_diff(freq_b))
            })
            .ok_or(Error::UnsupportedConfiguration)?;

        // A clock divider of 1 means 'divide clocks by 2', not 'divide clocks by 1', so we need to account for that.
        //
        const CLOCK_DIV_MULTIPLIER_OFFSET: u16 = 1;
        Ok(Self {
            scl_high_clocks: result_clocks_hi.to_clocks_enum(),
            scl_low_clocks: result_clocks_lo.to_clocks_enum(),
            clock_div_multiplier: result_div_multiplier - CLOCK_DIV_MULTIPLIER_OFFSET,
            _actual_freq_hz: SFRO_CLOCK_SPEED_HZ
                / (u32::from(result_clocks_hi + result_clocks_lo) * u32::from(result_div_multiplier)),
        })
    }
}

/// use `FCn` as I2C Master controller
pub struct I2cMaster<'a, M: Mode> {
    info: Info,
    _flexcomm: FlexcommRef,
    _phantom: PhantomData<M>,
    dma_ch: Option<dma::channel::Channel<'a>>,
}

/// Represents a duty cycle (percentage of time to hold the SCL line high per bit).  Fitting is best-effort / not exact.
#[derive(Clone, Copy)]
pub struct DutyCycle {
    value: u8,
}

impl DutyCycle {
    /// Determines and represents the closest possible duty cycle to the requested duty cycle that the hardware can support.
    pub fn new(target_duty_cycle: u8) -> Result<Self> {
        if target_duty_cycle < 100 * MIN_CLOCKS / (MIN_CLOCKS + MAX_CLOCKS)
            || target_duty_cycle > (100 * MAX_CLOCKS as u16 / (MIN_CLOCKS + MAX_CLOCKS) as u16 + 1) as u8
        {
            Err(Error::UnsupportedConfiguration)
        } else {
            // The hardware only has 6 bits of configurability for duty cycle and some of those represent duplicate duty cycles,
            // so we may not be able to accommodate the exact duty cycle the user has requested.  We need to find the closest
            // viable option.
            //
            let closest_supported_duty_cycle = (MIN_CLOCKS..=MAX_CLOCKS)
                .cartesian_product(MIN_CLOCKS..=MAX_CLOCKS)
                .map(|(hi_clocks, lo_clocks)| get_duty_cycle(hi_clocks, lo_clocks))
                .min_by(|duty_cycle_a, duty_cycle_b| {
                    duty_cycle_a
                        .abs_diff(target_duty_cycle)
                        .cmp(&duty_cycle_b.abs_diff(target_duty_cycle))
                })
                .ok_or(Error::UnsupportedConfiguration)?;

            Ok(Self {
                value: closest_supported_duty_cycle,
            })
        }
    }

    /// Retreives the actual selected duty cycle, which may be slightly different from the requested duty cycle due to hardware limitations.
    pub fn actual_value(&self) -> u8 {
        self.value
    }
}

impl Default for DutyCycle {
    fn default() -> Self {
        DutyCycle::new(40).unwrap()
    }
}

/// Configuration for I2C Master
#[derive(Clone, Copy)]
pub struct Config {
    /// Bus speed (nominal SCL, no clock stretching)
    pub speed: Speed,

    /// The target duty cycle (percentage of time to hold the SCL line high per bit).
    pub duty_cycle: DutyCycle,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            speed: Speed::Standard,
            duty_cycle: Default::default(),
        }
    }
}

impl<'a, M: Mode> I2cMaster<'a, M> {
    fn new_inner<T: Instance>(
        _bus: Peri<'a, T>,
        scl: Peri<'a, impl SclPin<T>>,
        sda: Peri<'a, impl SdaPin<T>>,
        // TODO - integrate clock APIs to allow dynamic freq selection | clock: crate::flexcomm::Clock,
        config: Config,
        dma_ch: Option<dma::channel::Channel<'a>>,
    ) -> Result<Self> {
        // TODO - clock integration
        let clock = crate::flexcomm::Clock::Sfro;
        let flexcomm = T::enable(clock);
        T::into_i2c();

        sda.as_sda();
        scl.as_scl();

        let info = T::info();
        let regs = info.regs;

        let speed_settings = SpeedRegisterSettings::new(config.duty_cycle, config.speed)?;

        regs.msttime().write(|w| {
            w.mstsclhigh()
                .variant(speed_settings.scl_high_clocks)
                .mstscllow()
                .variant(speed_settings.scl_low_clocks)
        });

        regs.clkdiv().write(|w| {
            // SAFETY: only unsafe due to .bits usage.
            unsafe { w.divval().bits(speed_settings.clock_div_multiplier) }
        });

        regs.intenset().reset();

        regs.cfg().write(|w| w.msten().set_bit());

        Ok(Self {
            info,
            _flexcomm: flexcomm,
            _phantom: PhantomData,
            dma_ch,
        })
    }

    fn check_for_bus_errors(&self) -> Result<()> {
        let i2cregs = self.info.regs;

        if i2cregs.stat().read().mstarbloss().is_arbitration_loss() {
            Err(TransferError::ArbitrationLoss.into())
        } else if i2cregs.stat().read().mstststperr().is_error() {
            Err(TransferError::StartStopError.into())
        } else {
            Ok(())
        }
    }
}

impl<'a> I2cMaster<'a, Blocking> {
    /// use flexcomm fc with Pins scl, sda as an I2C Master bus, configuring to speed and pull
    pub fn new_blocking<T: Instance>(
        fc: Peri<'a, T>,
        scl: Peri<'a, impl SclPin<T>>,
        sda: Peri<'a, impl SdaPin<T>>,
        // TODO - integrate clock APIs to allow dynamic freq selection | clock: crate::flexcomm::Clock,
        config: Config,
    ) -> Result<Self> {
        force_clear_remediation(&T::info());
        Self::new_inner::<T>(fc, scl, sda, config, None)
    }

    fn start(&mut self, address: u16, is_read: bool) -> Result<()> {
        // check if the address is 10-bit
        let is_10bit = address > 0x7F;

        // start with the correct address
        if is_10bit {
            self.start_10bit(address, is_read)
        } else {
            self.start_7bit(address as u8, is_read)
        }
    }

    fn start_7bit(&mut self, address: u8, is_read: bool) -> Result<()> {
        let i2cregs = self.info.regs;

        self.poll_ready()?;

        // cannot start if the the bus is already busy
        if i2cregs.stat().read().mstpending().is_in_progress() {
            return Err(TransferError::OtherBusError.into());
        }

        i2cregs.mstdat().write(|w|
            // SAFETY: only unsafe due to .bits usage
            unsafe { w.data().bits(address << 1 | u8::from(is_read)) });

        i2cregs.mstctl().write(|w| w.mststart().set_bit());

        self.poll_ready()?;

        if i2cregs.stat().read().mststate().is_nack_address() {
            // STOP bit to complete the attempted transfer
            self.stop()?;

            return Err(TransferError::AddressNack.into());
        }

        if is_read && !i2cregs.stat().read().mststate().is_receive_ready() {
            return Err(TransferError::ReadFail.into());
        }

        if !is_read && !i2cregs.stat().read().mststate().is_transmit_ready() {
            return Err(TransferError::WriteFail.into());
        }

        self.check_for_bus_errors()
    }

    fn start_10bit(&mut self, address: u16, is_read: bool) -> Result<()> {
        // check if the address is 10-bit and within the valid range
        if address > 0x3FF {
            return Err(Error::UnsupportedConfiguration);
        }
        let i2cregs = self.info.regs;

        self.poll_ready()?;

        // cannot start if the the bus is already busy
        if i2cregs.stat().read().mstpending().is_in_progress() {
            return Err(TransferError::OtherBusError.into());
        }

        // The first byte of a 10-bit address is 11110XXX,
        // where XXX are the 2 most significant bits of the 10-bit address
        // followed by the read/write bit
        let addr_high = TEN_BIT_PREFIX | (((address >> 8) as u8) << 1);
        i2cregs.mstdat().write(|w|
            // SAFETY: only unsafe due to .bits usage
            unsafe { w.data().bits(addr_high) });
        i2cregs.mstctl().write(|w| w.mststart().set_bit());

        self.poll_ready()?;
        self.check_for_bus_errors()?;

        // Send the second part of the 10-bit address
        let addr_low = (address & 0xFF) as u8;
        i2cregs.mstdat().write(|w|
            // SAFETY: only unsafe due to .bits usage
            unsafe { w.data().bits(addr_low) });
        i2cregs.mstctl().write(|w| w.mstcontinue().set_bit());

        self.poll_ready()?;
        self.check_for_bus_errors()?;

        // If this is a read operation, send a repeated start with the read bit set
        if is_read {
            let addr_high_read = addr_high | 0b1;
            i2cregs.mstdat().write(|w| unsafe { w.data().bits(addr_high_read) });
            i2cregs.mstctl().write(|w| w.mststart().set_bit());

            self.poll_ready()?;
            self.check_for_bus_errors()?;
        }

        if is_read && !i2cregs.stat().read().mststate().is_receive_ready() {
            return Err(TransferError::ReadFail.into());
        }

        if !is_read && !i2cregs.stat().read().mststate().is_transmit_ready() {
            return Err(TransferError::WriteFail.into());
        }

        Ok(())
    }

    fn read_no_stop(&mut self, address: u16, read: &mut [u8]) -> Result<()> {
        let i2cregs = self.info.regs;

        // read of 0 size is not allowed according to i2c spec
        if read.is_empty() {
            return Err(TransferError::OtherBusError.into());
        }

        self.start(address, true)?;

        let read_len = read.len();

        for (i, r) in read.iter_mut().enumerate() {
            self.poll_ready()?;

            // check transmission continuity
            if !i2cregs.stat().read().mststate().is_receive_ready() {
                return Err(TransferError::ReadFail.into());
            }

            self.check_for_bus_errors()?;

            *r = i2cregs.mstdat().read().data().bits();

            // continue after ACK until last byte
            if i < read_len - 1 {
                i2cregs.mstctl().write(|w| w.mstcontinue().set_bit());
            }
        }

        Ok(())
    }

    fn write_no_stop(&mut self, address: u16, write: &[u8]) -> Result<()> {
        // Procedure from 24.3.1.1 pg 545
        let i2cregs = self.info.regs;

        self.start(address, false)?;

        for byte in write {
            i2cregs.mstdat().write(|w|
                // SAFETY: unsafe only due to .bits usage
                unsafe { w.data().bits(*byte) });

            i2cregs.mstctl().write(|w| w.mstcontinue().set_bit());

            self.poll_ready()?;
            self.check_for_bus_errors()?;
        }

        Ok(())
    }

    fn stop(&mut self) -> Result<()> {
        // Procedure from 24.3.1.1 pg 545
        let i2cregs = self.info.regs;

        i2cregs.mstctl().write(|w| w.mststop().set_bit());
        self.poll_ready()?;
        self.check_for_bus_errors()?;

        // ensure return to idle state for bus (no stuck SCL/SDA lines)
        if i2cregs.stat().read().mststate().is_idle() {
            Ok(())
        } else {
            Err(TransferError::OtherBusError.into())
        }
    }

    fn poll_ready(&mut self) -> Result<()> {
        while self.info.regs.stat().read().mstpending().is_in_progress() {}

        Ok(())
    }
}

impl<'a> I2cMaster<'a, Async> {
    /// use flexcomm fc with Pins scl, sda as an I2C Master bus, configuring to speed and pull
    pub fn new_async<T: Instance>(
        fc: Peri<'a, T>,
        scl: Peri<'a, impl SclPin<T>>,
        sda: Peri<'a, impl SdaPin<T>>,
        _irq: impl interrupt::typelevel::Binding<T::Interrupt, InterruptHandler<T>> + 'a,
        // TODO - integrate clock APIs to allow dynamic freq selection | clock: crate::flexcomm::Clock,
        config: Config,
        dma_ch: Peri<'a, impl MasterDma<T>>,
    ) -> Result<Self> {
        force_clear_remediation(&T::info());
        let ch = dma::Dma::reserve_channel(dma_ch);
        let this = Self::new_inner::<T>(fc, scl, sda, config, ch)?;

        T::Interrupt::unpend();
        unsafe { T::Interrupt::enable() };

        Ok(this)
    }

    async fn start(&mut self, address: u16, is_read: bool, guard: Option<StartStopGuard>) -> Result<StartStopGuard> {
        // check if the address is 10-bit
        let is_10bit = address > 0x7F;

        // start with the correct address
        if is_10bit {
            self.start_10bit(address, is_read, guard).await
        } else {
            self.start_7bit(address as u8, is_read, guard).await
        }
    }

    async fn start_7bit(
        &mut self,
        address: u8,
        is_read: bool,
        guard: Option<StartStopGuard>,
    ) -> Result<StartStopGuard> {
        let i2cregs = self.info.regs;

        // If there was a previous cancellation, wait for the remediation step by the
        // interrupt to complete.
        wait_remediation_complete(&self.info).await;

        self.wait_on(
            |me| {
                let stat = me.info.regs.stat().read();

                if stat.mstpending().is_pending() {
                    Poll::Ready(Ok::<(), Error>(()))
                } else if stat.mstarbloss().is_arbitration_loss() {
                    Poll::Ready(Err(TransferError::ArbitrationLoss.into()))
                } else if stat.mstststperr().is_error() {
                    Poll::Ready(Err(TransferError::StartStopError.into()))
                } else {
                    Poll::Pending
                }
            },
            |me| {
                me.info.regs.intenset().write(|w| {
                    w.mstpendingen()
                        .set_bit()
                        .mstarblossen()
                        .set_bit()
                        .mstststperren()
                        .set_bit()
                });
            },
        )
        .await?;

        // Sentinel to perform corrective action if future is dropped
        let on_drop = OnDrop::new(|| {
            // Disable and re-enable master mode to clear out stalled HW state
            // if we failed to complete sending of the address
            // In practice, this seems to be only way to recover. Engaging with
            // NXP to see if there is better way to handle this.
            i2cregs.cfg().write(|w| w.msten().disabled());
            i2cregs.cfg().write(|w| w.msten().enabled());
        });

        i2cregs.mstdat().write(|w|
            // SAFETY: only unsafe due to .bits usage
            unsafe { w.data().bits(address << 1 | u8::from(is_read)) });

        i2cregs.mstctl().write(|w| w.mststart().set_bit());

        // We have now sent a start, create a guard to ensure that a stop is sent
        let guard = guard.unwrap_or_else(|| StartStopGuard { info: self.info });

        // Did that go well?
        let res = self.poll_for_ready(is_read).await;

        // Defuse the sentinel if future is not dropped
        on_drop.defuse();

        res?;

        Ok(guard)
    }

    async fn start_10bit(
        &mut self,
        address: u16,
        is_read: bool,
        guard: Option<StartStopGuard>,
    ) -> Result<StartStopGuard> {
        // check if the address is 10-bit and within the valid range
        if address > 0x3FF {
            return Err(Error::UnsupportedConfiguration);
        }
        let i2cregs = self.info.regs;

        // If there was a previous cancellation, wait for the remediation step by the
        // interrupt to complete.
        wait_remediation_complete(&self.info).await;

        self.wait_on(
            |me| {
                let stat = me.info.regs.stat().read();

                if stat.mstpending().is_pending() {
                    Poll::Ready(Ok::<(), Error>(()))
                } else if stat.mstarbloss().is_arbitration_loss() {
                    Poll::Ready(Err(TransferError::ArbitrationLoss.into()))
                } else if stat.mstststperr().is_error() {
                    Poll::Ready(Err(TransferError::StartStopError.into()))
                } else {
                    Poll::Pending
                }
            },
            |me| {
                me.info.regs.intenset().write(|w| {
                    w.mstpendingen()
                        .set_bit()
                        .mstarblossen()
                        .set_bit()
                        .mstststperren()
                        .set_bit()
                });
            },
        )
        .await?;

        // Sentinel to perform corrective action if future is dropped
        let on_drop = OnDrop::new(|| {
            // Disable and re-enable master mode to clear out stalled HW state
            // if we failed to complete sending of the address
            // In practice, this seems to be only way to recover. Engaging with
            // NXP to see if there is better way to handle this.
            i2cregs.cfg().write(|w| w.msten().disabled());
            i2cregs.cfg().write(|w| w.msten().enabled());
        });

        // The first byte of a 10-bit address is 11110XXX,
        // where XXX are the 2 most significant bits of the 10-bit address
        // followed by the read/write bit
        let addr_high = TEN_BIT_PREFIX | (((address >> 8) as u8) << 1);
        i2cregs.mstdat().write(|w| unsafe { w.data().bits(addr_high) });
        i2cregs.mstctl().write(|w| w.mststart().set_bit());
        let guard = guard.unwrap_or_else(|| StartStopGuard { info: self.info });

        // 10-bit address mode requires the two address bytes to be sent as a write operation
        self.poll_for_ready(false).await?;

        // Send the second part of the 10-bit address
        let addr_low = (address & 0xFF) as u8;
        i2cregs.mstdat().write(|w| unsafe { w.data().bits(addr_low) });
        i2cregs.mstctl().write(|w| w.mstcontinue().set_bit());

        // 10-bit address mode requires the two address bytes to be sent as a write operation
        self.poll_for_ready(false).await?;

        // If this is a read operation, send a repeated start with the read bit set
        if is_read {
            let addr_high_read = addr_high | 0b1;
            i2cregs.mstdat().write(|w| unsafe { w.data().bits(addr_high_read) });
            i2cregs.mstctl().write(|w| w.mststart().set_bit());

            self.poll_for_ready(is_read).await?;
        }
        // Defuse the sentinel if future is not dropped
        on_drop.defuse();
        Ok(guard)
    }

    async fn read_no_stop(
        &mut self,
        address: u16,
        read: &mut [u8],
        guard: Option<StartStopGuard>,
    ) -> Result<StartStopGuard> {
        let i2cregs = self.info.regs;

        // read of 0 size is not allowed according to i2c spec
        //
        // These are used in the DMA branch, but also checks implicitly
        // if the slice is empty, so we do it here anyway
        let Some((last_byte, dma_read)) = read.split_last_mut() else {
            return Err(TransferError::OtherBusError.into());
        };

        let guard = self.start(address, true, guard).await?;

        if self.dma_ch.is_some() {
            if !dma_read.is_empty() {
                let transfer = dma::transfer::Transfer::new_read(
                    self.dma_ch.as_mut().unwrap(),
                    i2cregs.mstdat().as_ptr() as *mut u8,
                    dma_read,
                    Default::default(),
                );

                // According to sections 24.7.7.1 and 24.7.7.2, we should
                // first program the DMA channel for carrying out a transfer
                // and only then set MSTDMA bit.
                //
                // Additionally, at this point we know the slave has
                // acknowledged the address.
                i2cregs.mstctl().write(|w| w.mstdma().enabled());

                // Use drop guard to ensure that DMA is disabled when we exit
                // scope, successful or not.
                let _dma_guard = OnDrop::new(|| {
                    i2cregs.mstctl().modify(|_r, w| w.mstdma().disabled());
                });

                let res = select(
                    transfer,
                    poll_fn(|cx| {
                        I2C_WAKERS[self.info.index].register(cx.waker());

                        i2cregs.intenset().write(|w| {
                            w.mstpendingen()
                                .set_bit()
                                .mstarblossen()
                                .set_bit()
                                .mstststperren()
                                .set_bit()
                        });

                        let stat = i2cregs.stat().read();

                        if stat.mstarbloss().is_arbitration_loss() {
                            Poll::Ready(Err::<(), Error>(TransferError::ArbitrationLoss.into()))
                        } else if stat.mstststperr().is_error() {
                            Poll::Ready(Err::<(), Error>(TransferError::StartStopError.into()))
                        } else {
                            Poll::Pending
                        }
                    }),
                )
                .await;

                if let Either::Second(e) = res {
                    e?;
                }
            }

            self.wait_on(
                |me| {
                    let stat = me.info.regs.stat().read();

                    if stat.mstpending().is_pending() {
                        Poll::Ready(Ok::<(), Error>(()))
                    } else if stat.mstarbloss().is_arbitration_loss() {
                        Poll::Ready(Err(TransferError::ArbitrationLoss.into()))
                    } else if stat.mstststperr().is_error() {
                        Poll::Ready(Err(TransferError::StartStopError.into()))
                    } else {
                        Poll::Pending
                    }
                },
                |me| {
                    me.info.regs.intenset().write(|w| {
                        w.mstpendingen()
                            .set_bit()
                            .mstarblossen()
                            .set_bit()
                            .mstststperren()
                            .set_bit()
                    });
                },
            )
            .await?;

            // Read the last byte
            *last_byte = i2cregs.mstdat().read().data().bits();
        } else {
            // No DMA recv, we must manually recv one byte at a time.
            let read_len = read.len();

            for (i, r) in read.iter_mut().enumerate() {
                self.wait_on(
                    |me| {
                        let stat = me.info.regs.stat().read();

                        if stat.mstpending().is_pending() {
                            Poll::Ready(Ok::<(), Error>(()))
                        } else if stat.mstarbloss().is_arbitration_loss() {
                            Poll::Ready(Err(TransferError::ArbitrationLoss.into()))
                        } else if stat.mstststperr().is_error() {
                            Poll::Ready(Err(TransferError::StartStopError.into()))
                        } else {
                            Poll::Pending
                        }
                    },
                    |me| {
                        me.info.regs.intenset().write(|w| {
                            w.mstpendingen()
                                .set_bit()
                                .mstarblossen()
                                .set_bit()
                                .mstststperren()
                                .set_bit()
                        });
                    },
                )
                .await?;

                // check transmission continuity
                if !i2cregs.stat().read().mststate().is_receive_ready() {
                    return Err(TransferError::ReadFail.into());
                }

                self.check_for_bus_errors()?;

                *r = i2cregs.mstdat().read().data().bits();

                // continue after ACK until last byte
                if i < read_len - 1 {
                    i2cregs.mstctl().write(|w| w.mstcontinue().set_bit());
                }
            }
        }
        Ok(guard)
    }

    async fn write_no_stop(
        &mut self,
        address: u16,
        write: &[u8],
        guard: Option<StartStopGuard>,
    ) -> Result<StartStopGuard> {
        // Procedure from 24.3.1.1 pg 545
        let i2cregs = self.info.regs;

        let guard = self.start(address, false, guard).await?;

        if write.is_empty() {
            return Ok(guard);
        }

        if self.dma_ch.is_some() {
            let transfer = dma::transfer::Transfer::new_write(
                self.dma_ch.as_mut().unwrap(),
                write,
                i2cregs.mstdat().as_ptr() as *mut u8,
                Default::default(),
            );

            // According to sections 24.7.7.1 and 24.7.7.2, we should
            // first program the DMA channel for carrying out a transfer
            // and only then set MSTDMA bit.
            //
            // Additionally, at this point we know the slave has
            // acknowledged the address.
            i2cregs.mstctl().write(|w| w.mstdma().enabled());

            // Use drop guard to ensure that DMA is disabled when we exit
            // scope, successful or not.
            let dma_guard = OnDrop::new(|| {
                i2cregs.mstctl().modify(|_r, w| w.mstdma().disabled());
            });

            let res = select(
                transfer,
                poll_fn(|cx| {
                    I2C_WAKERS[self.info.index].register(cx.waker());

                    i2cregs.intenset().write(|w| {
                        w.mstpendingen()
                            .set_bit()
                            .mstarblossen()
                            .set_bit()
                            .mstststperren()
                            .set_bit()
                    });

                    let stat = i2cregs.stat().read();

                    if stat.mstarbloss().is_arbitration_loss() {
                        Poll::Ready(Err::<(), Error>(TransferError::ArbitrationLoss.into()))
                    } else if stat.mstststperr().is_error() {
                        Poll::Ready(Err::<(), Error>(TransferError::StartStopError.into()))
                    } else {
                        Poll::Pending
                    }
                }),
            )
            .await;

            // trigger drop guard to disable DMA flag
            drop(dma_guard);

            if let Either::Second(e) = res {
                e?;
            }

            self.wait_on(
                |me| {
                    let stat = me.info.regs.stat().read();

                    if stat.mstpending().is_pending() {
                        Poll::Ready(Ok::<(), Error>(()))
                    } else if stat.mstarbloss().is_arbitration_loss() {
                        Poll::Ready(Err(TransferError::ArbitrationLoss.into()))
                    } else if stat.mstststperr().is_error() {
                        Poll::Ready(Err(TransferError::StartStopError.into()))
                    } else {
                        Poll::Pending
                    }
                },
                |me| {
                    me.info.regs.intenset().write(|w| {
                        w.mstpendingen()
                            .set_bit()
                            .mstarblossen()
                            .set_bit()
                            .mstststperren()
                            .set_bit()
                    });
                },
            )
            .await?;
            Ok(guard)
        } else {
            for byte in write.iter() {
                i2cregs.mstdat().write(|w|
                    // SAFETY: unsafe only due to .bits usage
                    unsafe { w.data().bits(*byte) });

                i2cregs.mstctl().write(|w| w.mstcontinue().set_bit());

                self.wait_on(
                    |me| {
                        let stat = me.info.regs.stat().read();

                        if stat.mstpending().is_pending() {
                            Poll::Ready(Ok::<(), Error>(()))
                        } else if stat.mstarbloss().is_arbitration_loss() {
                            Poll::Ready(Err(TransferError::ArbitrationLoss.into()))
                        } else if stat.mstststperr().is_error() {
                            Poll::Ready(Err(TransferError::StartStopError.into()))
                        } else {
                            Poll::Pending
                        }
                    },
                    |me| {
                        me.info.regs.intenset().write(|w| {
                            w.mstpendingen()
                                .set_bit()
                                .mstarblossen()
                                .set_bit()
                                .mstststperren()
                                .set_bit()
                        });
                    },
                )
                .await?;

                self.check_for_bus_errors()?;
            }
            Ok(guard)
        }
    }

    async fn stop(&mut self) -> Result<()> {
        // Procedure from 24.3.1.1 pg 545
        let i2cregs = self.info.regs;

        if i2cregs.stat().read().mstpending().is_in_progress() {
            return Err(TransferError::StartStopError.into());
        }

        i2cregs.mstctl().write(|w| w.mststop().set_bit());

        self.wait_on(
            |me| {
                let stat = me.info.regs.stat().read();

                if stat.mstpending().is_pending() && stat.mststate().is_idle() {
                    Poll::Ready(Ok(()))
                } else if stat.mstarbloss().is_arbitration_loss() {
                    Poll::Ready(Err(TransferError::ArbitrationLoss.into()))
                } else if stat.mstststperr().is_error() {
                    Poll::Ready(Err(TransferError::StartStopError.into()))
                } else {
                    Poll::Pending
                }
            },
            |me| {
                me.info.regs.intenset().write(|w| {
                    w.mstpendingen()
                        .set_bit()
                        .mstarblossen()
                        .set_bit()
                        .mstststperren()
                        .set_bit()
                });
            },
        )
        .await
    }

    /// Calls `f` to check if we are ready or not.
    /// If not, `g` is called once the waker is set (to eg enable the required interrupts).
    async fn wait_on<F, U, G>(&mut self, mut f: F, mut g: G) -> U
    where
        F: FnMut(&mut Self) -> Poll<U>,
        G: FnMut(&mut Self),
    {
        poll_fn(|cx| {
            // Register waker before checking condition, to ensure that wakes/interrupts
            // aren't lost between f() and g()
            I2C_WAKERS[self.info.index].register(cx.waker());
            let r = f(self);

            if r.is_pending() {
                g(self);
            }

            r
        })
        .await
    }

    /// During i2c start, poll for ready state and check for errors
    async fn poll_for_ready(&mut self, is_read: bool) -> Result<()> {
        self.wait_on(
            |me| {
                let stat = me.info.regs.stat().read();

                if stat.mstpending().is_pending() {
                    if is_read && stat.mststate().is_receive_ready() || !is_read && stat.mststate().is_transmit_ready()
                    {
                        Poll::Ready(Ok::<(), Error>(()))
                    } else if stat.mststate().is_nack_address() {
                        Poll::Ready(Err(TransferError::AddressNack.into()))
                    } else if is_read && !stat.mststate().is_receive_ready() {
                        Poll::Ready(Err(TransferError::ReadFail.into()))
                    } else if !is_read && !stat.mststate().is_transmit_ready() {
                        Poll::Ready(Err(TransferError::WriteFail.into()))
                    } else {
                        Poll::<Result<()>>::Pending
                    }
                } else if stat.mstarbloss().is_arbitration_loss() {
                    Poll::Ready(Err(TransferError::ArbitrationLoss.into()))
                } else if stat.mstststperr().is_error() {
                    Poll::Ready(Err(TransferError::StartStopError.into()))
                } else {
                    Poll::<Result<()>>::Pending
                }
            },
            |me| {
                me.info.regs.intenset().write(|w| {
                    w.mstpendingen()
                        .set_bit()
                        .mstarblossen()
                        .set_bit()
                        .mstststperren()
                        .set_bit()
                });
            },
        )
        .await
    }
}

/// Error Types for I2C communication
impl embedded_hal_1::i2c::Error for Error {
    fn kind(&self) -> embedded_hal_1::i2c::ErrorKind {
        match *self {
            Self::UnsupportedConfiguration => embedded_hal_1::i2c::ErrorKind::Other,
            Self::Transfer(e) => match e {
                TransferError::Timeout => embedded_hal_1::i2c::ErrorKind::Other,
                TransferError::ReadFail | TransferError::WriteFail => {
                    embedded_hal_1::i2c::ErrorKind::NoAcknowledge(embedded_hal_1::i2c::NoAcknowledgeSource::Data)
                }
                TransferError::AddressNack => {
                    embedded_hal_1::i2c::ErrorKind::NoAcknowledge(embedded_hal_1::i2c::NoAcknowledgeSource::Address)
                }
                TransferError::ArbitrationLoss => embedded_hal_1::i2c::ErrorKind::ArbitrationLoss,
                TransferError::StartStopError => embedded_hal_1::i2c::ErrorKind::Bus,
                TransferError::OtherBusError => embedded_hal_1::i2c::ErrorKind::Bus,
            },
        }
    }
}

impl<M: Mode> embedded_hal_1::i2c::ErrorType for I2cMaster<'_, M> {
    type Error = Error;
}

// implement generic i2c interface for peripheral master type
impl<A: embedded_hal_1::i2c::AddressMode + Into<u16>> embedded_hal_1::i2c::I2c<A> for I2cMaster<'_, Blocking> {
    fn read(&mut self, address: A, read: &mut [u8]) -> Result<()> {
        self.read_no_stop(address.into(), read)?;
        self.stop()
    }

    fn write(&mut self, address: A, write: &[u8]) -> Result<()> {
        self.write_no_stop(address.into(), write)?;
        self.stop()
    }

    fn write_read(&mut self, address: A, write: &[u8], read: &mut [u8]) -> Result<()> {
        let address = address.into();
        self.write_no_stop(address, write)?;
        self.read_no_stop(address, read)?;
        self.stop()
    }

    fn transaction(&mut self, address: A, operations: &mut [embedded_hal_1::i2c::Operation<'_>]) -> Result<()> {
        let needs_stop = !operations.is_empty();
        let address = address.into();

        for op in operations {
            match op {
                embedded_hal_1::i2c::Operation::Read(read) => {
                    self.read_no_stop(address, read)?;
                }
                embedded_hal_1::i2c::Operation::Write(write) => {
                    self.write_no_stop(address, write)?;
                }
            }
        }

        if needs_stop {
            self.stop()?;
        }

        Ok(())
    }
}

impl<A: embedded_hal_1::i2c::AddressMode + Into<u16>> embedded_hal_async::i2c::I2c<A> for I2cMaster<'_, Async> {
    async fn read(&mut self, address: A, read: &mut [u8]) -> Result<()> {
        let guard = self.read_no_stop(address.into(), read, None).await?;
        self.stop().await?;
        guard.defuse();
        Ok(())
    }

    async fn write(&mut self, address: A, write: &[u8]) -> Result<()> {
        let guard = self.write_no_stop(address.into(), write, None).await?;
        self.stop().await?;
        guard.defuse();
        Ok(())
    }

    async fn write_read(&mut self, address: A, write: &[u8], read: &mut [u8]) -> Result<()> {
        let address = address.into();
        let guard = self.write_no_stop(address, write, None).await?;
        let guard = self.read_no_stop(address, read, Some(guard)).await?;
        self.stop().await?;
        guard.defuse();
        Ok(())
    }

    async fn transaction(&mut self, address: A, operations: &mut [embedded_hal_1::i2c::Operation<'_>]) -> Result<()> {
        let address = address.into();
        let mut guard = None;

        for op in operations {
            match op {
                embedded_hal_1::i2c::Operation::Read(read) => {
                    guard = Some(self.read_no_stop(address, read, guard).await?);
                }
                embedded_hal_1::i2c::Operation::Write(write) => {
                    guard = Some(self.write_no_stop(address, write, guard).await?);
                }
            }
        }

        if let Some(guard) = guard {
            self.stop().await?;
            guard.defuse();
        }

        Ok(())
    }
}

/// This guard represents that a START has been sent, but no matching STOP has
/// been sent. If this guard is dropped without calling [`StartStopGuard::defuse()`],
/// then we will signal the interrupt handler to send a STOP the next time that the
/// I2C peripheral engine is in the PENDING state.
///
/// According to 24.6.2 Table 566 of the reference manual, if the I2C peripheral is
/// NOT in the PENDING state, then it will not accept commands, including the STOP
/// command. Rather than busy-spin in the drop function for this state to be reached,
/// or leaving the bus in the un-stopped state, we ask the interrupt handler to do
/// it for us.
#[must_use]
struct StartStopGuard {
    info: Info,
}

impl StartStopGuard {
    fn defuse(self) {
        core::mem::forget(self);
    }
}

impl Drop for StartStopGuard {
    fn drop(&mut self) {
        // This is done in a critical section to ensure that we don't race with the
        // I2C interrupt. This could potentially be done without a critical section,
        // however the duration is extremely short, and doesn't require a loop to do
        // so.
        critical_section::with(|_| {
            // Ensure the MST pending enable interrupt is active, in case we need it
            self.info.regs.intenset().write(|w| w.mstpendingen().set_bit());
            // Check if the i2c engine is in a pending state, ready to accept commands
            let is_pending = self.info.regs.stat().read().mstpending().is_pending();

            if is_pending {
                // We are pending, we can issue the stop immediately
                self.info.regs.mstctl().write(|w| w.mststop().set_bit());
            } else {
                // We are NOT pending, we need to ask the interrupt to send a stop the next
                // time the engine is pending. We ensured that the interrupt is active above
                I2C_REMEDIATION[self.info.index].fetch_or(REMEDIATON_MASTER_STOP, Ordering::AcqRel);
            }
        })
    }
}
