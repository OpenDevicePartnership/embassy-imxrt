//! SPI Serial Peripheral Interface over flexcomm

use core::future::poll_fn;
use core::marker::PhantomData;
use core::task::Poll;

//use crate::pac::Spi0;
//use embassy_futures::join::join;

use embassy_hal_internal::{into_ref,Peripheral,PeripheralRef};
use embassy_sync::waitqueue::AtomicWaker;
use fixed::traits::LossyInto;
use paste::paste;

pub use embedded_hal_02::spi::{Phase, Polarity};
use sealed::Sealed;

use crate::interrupts::interrupt::typelevel::Interrupt;
use crate::{dma, interrupt};
use crate::iopctl::{AnyPin, IopctlPin as Pin};

/// shorthand for -> Result<T>
pub type Result<T> = core::result::Result<T, Error>;

// rt6x high-speed spi sclk can clock up to 50M Hz
const SPI_MAX_SCLK_FREQ: u32 = 50_000_000;

/// SPI configuration.
#[non_exhaustive]
#[derive(Clone, Copy)]
pub struct Config {
    /// Frequency.
    pub frequency: u32,
    /// Phase.
    pub phase: Phase,
    /// Polarity.
    pub polarity: Polarity,
    // todo: add config item for chip select polarities
    // todo: add config item for msb/lsb first
    // todo: add config items for frame, pre, post-delay.
}

impl Default for Config {
    fn default() -> Self {
        Self {
            frequency: 1_000_000,
            phase: Phase::CaptureOnFirstTransition,
            polarity: Polarity::IdleLow,
        }
    }
}

/// Error information type
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[non_exhaustive]
pub enum Error {
    /// configuration requested is not supported
    UnsupportedSclkFrequency,
    /// configuration requested is not supported
    UnsupportedConfiguration,
    /// The peripheral receive buffer was overrun.
    Overrun,
    /// Multiple devices on the SPI bus are trying to drive the slave select pin, e.g. in a multi-master setup.
    ModeFault,
    /// Received data does not conform to the peripheral configuration.
    FrameFormat,
    /// An error occurred while asserting or deasserting the Chip Select pin.
    ChipSelectFault,
    /// A different error occurred. The original error may contain more information.
    Other,
}

mod sealed {
    /// simply seal a trait
    pub trait Sealed {}
}

impl<T: Pin> sealed::Sealed for T {}

struct Info {
    regs: &'static crate::pac::spi0::RegisterBlock,
    index: usize,
}

trait SealedInstance {
    fn info() -> Info;
    fn index() -> usize;
}

/// SPI instance trait.
/// shared functions between Controller and Target operation
#[allow(private_bounds)]
pub trait Instance: crate::flexcomm::IntoSpi + SealedInstance + Peripheral<P = Self> + 'static + Send {
    /// Interrupt for this SPI instance.
    type Interrupt: interrupt::typelevel::Interrupt;
}

macro_rules! impl_instance {
    ($($n:expr),*) => {
	$(
	    paste!{
		impl SealedInstance for crate::peripherals::[<FLEXCOMM $n>] {
		    fn info() -> Info {
			Info {
			    regs: unsafe { &*crate::pac::[<Spi $n>]::ptr() },
			    index: $n,
			}
		    }

		    #[inline]
		    fn index() -> usize {
			$n
		    }
		}

		impl Instance for crate::peripherals::[<FLEXCOMM $n>] {
		    type Interrupt = crate::interrupt::typelevel::[<FLEXCOMM $n>];
		}
	    }
	)*
    };
}

impl_instance!(0, 1, 2, 3, 4, 5, 6, 7);

const SPI_WAKER_COUNT: usize = 8;
static SPI_WAKERS: [AtomicWaker; SPI_WAKER_COUNT] = [const { AtomicWaker::new() }; SPI_WAKER_COUNT];

/// Spi interrupt handler.
pub struct InterruptHandler<T: Instance> {
    _phantom: PhantomData<T>,
}

impl<T: Instance> interrupt::typelevel::Handler<T::Interrupt> for InterruptHandler<T> {
    unsafe fn on_interrupt() {
        let waker = &SPI_WAKERS[T::index()];

        let spi = T::info().regs;

        // todo: manage spi int status

        waker.wake();
    }
}

/// io configuration trait for Mosi
pub trait MosiPin<Instance>: Pin + sealed::Sealed + crate::Peripheral {
    /// convert the pin to appropriate function for mosi usage
    fn as_mosi(&self);
}

/// io configuration trait for Miso
pub trait MisoPin<Instance>: Pin + sealed::Sealed + crate::Peripheral {
    /// convert the pin to appropriate function for miso usage
    fn as_miso(&self);
}

/// io configuration trait for Sclk (serial clock)
pub trait SclkPin<Instance>: Pin + sealed::Sealed + crate::Peripheral {
    /// convert the pin to appropriate function for sclk usage
    fn as_sclk(&self);
}

/// io configuration trait for Ssel n (chip select n)
pub trait SselPin<Instance>: Pin + sealed::Sealed + crate::Peripheral {
    /// convert the pin to appropriate function for ssel usage
    fn as_ssel(&self);
}

fn calc_div(source_freq:u32, target_sclk_freq: u32) -> u16 {
    return 8 as u16;
    // todo
    //todo!();
}

/// Driver mode.
#[allow(private_bounds)]
pub trait Mode: Sealed {}

/// Blocking mode.
pub struct Blocking;
impl Sealed for Blocking {}
impl Mode for Blocking {}

/// Async mode.
pub struct Async;
impl Sealed for Async {}
impl Mode for Async {}

// flexcomm <-> Pin function map
macro_rules! impl_miso {
    ($piom_n:ident, $fn:ident, $fcn:ident) => {
        impl MisoPin<crate::peripherals::$fcn> for crate::peripherals::$piom_n {
            fn as_miso(&self) {
                // UM11147 table 299 pg 262+, and table 530, pg 518+
                self.set_pull(crate::gpio::Pull::None)
                    .set_slew_rate(crate::gpio::SlewRate::Standard)
                    .set_drive_strength(crate::gpio::DriveStrength::Normal)
                    .set_drive_mode(crate::gpio::DriveMode::PushPull)
                    .set_input_inverter(crate::gpio::Inverter::Disabled)
                    .enable_input_buffer()
                    .set_function(crate::iopctl::Function::$fn);
            }
        }
    };
}
macro_rules! impl_mosi {
    ($piom_n:ident, $fn:ident, $fcn:ident) => {
        impl MosiPin<crate::peripherals::$fcn> for crate::peripherals::$piom_n {
            fn as_mosi(&self) {
                // UM11147 table 299 pg 262+, and table 530, pg 518+
                self.set_pull(crate::gpio::Pull::None)
                    .set_slew_rate(crate::gpio::SlewRate::Standard)
                    .set_drive_strength(crate::gpio::DriveStrength::Normal)
                    .set_drive_mode(crate::gpio::DriveMode::PushPull)
                    .set_input_inverter(crate::gpio::Inverter::Disabled)
                    .enable_input_buffer()
                    .set_function(crate::iopctl::Function::$fn);
            }
        }
    };
}
macro_rules! impl_sclk {
    ($piom_n:ident, $fn:ident, $fcn:ident) => {
        impl SclkPin<crate::peripherals::$fcn> for crate::peripherals::$piom_n {
            fn as_sclk(&self) {
                // UM11147 table 299 pg 262+, and table 530, pg 518+
                self.set_pull(crate::gpio::Pull::None)
                    .set_slew_rate(crate::gpio::SlewRate::Standard)
                    .set_drive_strength(crate::gpio::DriveStrength::Normal)
                    .set_drive_mode(crate::gpio::DriveMode::PushPull)
                    .set_input_inverter(crate::gpio::Inverter::Disabled)
                    .enable_input_buffer()
                    .set_function(crate::iopctl::Function::$fn);
            }
        }
    };
}
macro_rules! impl_ssel {
    ($piom_n:ident, $fn:ident, $fcn:ident) => {
        impl SselPin<crate::peripherals::$fcn> for crate::peripherals::$piom_n {
            fn as_ssel(&self) {
                // UM11147 table 299 pg 262+, and table 530, pg 518+
                self.set_pull(crate::gpio::Pull::None)
                    .set_slew_rate(crate::gpio::SlewRate::Standard)
                    .set_drive_strength(crate::gpio::DriveStrength::Normal)
                    .set_drive_mode(crate::gpio::DriveMode::PushPull)
                    .set_input_inverter(crate::gpio::Inverter::Disabled)
                    .enable_input_buffer()
                    .set_function(crate::iopctl::Function::$fn);
            }
        }
    };
}

// note that signals can be optionally mapped to one of multiple pins

// Flexcomm0 SPI GPIO options -
impl_miso!(PIO0_1, F1, FLEXCOMM0);
impl_mosi!(PIO0_2, F1, FLEXCOMM0);
impl_sclk!(PIO0_0, F1, FLEXCOMM0);
impl_ssel!(PIO0_3, F1, FLEXCOMM0); // SSEL0
impl_ssel!(PIO0_4, F1, FLEXCOMM0); // SSEL1
impl_ssel!(PIO0_5, F1, FLEXCOMM0); // SSEL2
impl_ssel!(PIO0_6, F1, FLEXCOMM0); // SSEL3
impl_ssel!(PIO0_10, F5, FLEXCOMM0); // SSEL2
impl_ssel!(PIO0_11, F5, FLEXCOMM0); // SSEL3

impl_miso!(PIO3_0, F5, FLEXCOMM0);
impl_mosi!(PIO3_1, F5, FLEXCOMM0);
impl_sclk!(PIO3_2, F5, FLEXCOMM0);
impl_ssel!(PIO3_3, F5, FLEXCOMM0); // SSEL0
impl_ssel!(PIO3_4, F5, FLEXCOMM0); // SSEL1
impl_ssel!(PIO3_5, F5, FLEXCOMM0); // SSEL2
impl_ssel!(PIO3_6, F5, FLEXCOMM0); // SSEL3

// Flexcomm1 SPI GPIO options -
impl_ssel!(PIO0_3, F5, FLEXCOMM1); // SSEL2
impl_ssel!(PIO0_4, F5, FLEXCOMM1); // SSEL3
impl_sclk!(PIO0_7, F1, FLEXCOMM1);
impl_miso!(PIO0_8, F1, FLEXCOMM1);
impl_mosi!(PIO0_9, F1, FLEXCOMM1);
impl_ssel!(PIO0_10, F1, FLEXCOMM1); // SSEL0
impl_ssel!(PIO0_11, F1, FLEXCOMM1); // SSEL1
impl_ssel!(PIO0_12, F1, FLEXCOMM1); // SSEL2
impl_ssel!(PIO0_13, F1, FLEXCOMM1); // SSEL3

impl_sclk!(PIO7_25, F1, FLEXCOMM1);
impl_miso!(PIO7_26, F1, FLEXCOMM1);
impl_mosi!(PIO7_27, F1, FLEXCOMM1);
impl_ssel!(PIO7_28, F1, FLEXCOMM1); // SSEL0
impl_ssel!(PIO7_29, F1, FLEXCOMM1); // SSEL1
impl_ssel!(PIO7_30, F1, FLEXCOMM1); // SSEL2
impl_ssel!(PIO7_31, F1, FLEXCOMM1); // SSEL3

// Flexcomm2 SPI GPIO options -
impl_sclk!(PIO0_14, F1, FLEXCOMM2);
impl_miso!(PIO0_15, F1, FLEXCOMM2);
impl_mosi!(PIO0_16, F1, FLEXCOMM2);
impl_ssel!(PIO0_17, F1, FLEXCOMM2); // SSEL0
impl_ssel!(PIO0_18, F1, FLEXCOMM2); // SSEL1
impl_ssel!(PIO0_19, F1, FLEXCOMM2); // SSEL2
impl_ssel!(PIO0_20, F1, FLEXCOMM2); // SSEL3
impl_ssel!(PIO0_24, F5, FLEXCOMM2); // SSEL2
impl_ssel!(PIO0_25, F5, FLEXCOMM2); // SSEL3

impl_ssel!(PIO4_8, F5, FLEXCOMM2); // SSEL2

impl_sclk!(PIO7_24, F5, FLEXCOMM2);
impl_miso!(PIO7_30, F5, FLEXCOMM2);
impl_mosi!(PIO7_31, F5, FLEXCOMM2);

// todo: impls for other fcn channels...
// Flexcomm3 SPI GPIO options -

// Flexcomm4 SPI GPIO options -

// Flexcomm5 SPI GPIO options -
impl_sclk!(PIO1_3, F1, FLEXCOMM5);
impl_miso!(PIO1_4, F1, FLEXCOMM5);
impl_mosi!(PIO1_5, F1, FLEXCOMM5);
impl_ssel!(PIO1_6, F1, FLEXCOMM5);
impl_ssel!(PIO1_7, F1, FLEXCOMM5);
impl_ssel!(PIO1_8, F1, FLEXCOMM5);
impl_ssel!(PIO1_9, F1, FLEXCOMM5);

// Flexcomm6 SPI GPIO options -

// Flexcomm7 SPI GPIO options -

// Flexcomm14 SPI GPIO options -
//impl_sclk!(PIO1_11, F1, FLEXCOMM14);
//impl_miso!(PIO1_12, F1, FLEXCOMM14);
//impl_mosi!(PIO1_13, F1, FLEXCOMM14);
//impl_ssel!(PIO1_14, F1, FLEXCOMM14);
//impl_ssel!(PIO1_15, F1, FLEXCOMM14);
//impl_ssel!(PIO1_16, F1, FLEXCOMM14);
//impl_ssel!(PIO1_17, F1, FLEXCOMM14);

// Flexcomm15 SPI GPIO options -

/// use FCn as SPI controller
pub struct SpiController<'d, M: Mode> {
    info: Info,
    _phantom: PhantomData<M>,
    config: Config,
    //ssel0: Option<PeripheralRef<'d, AnyPin>>,
    //ssel1: Option<PeripheralRef<'d, AnyPin>>,
    //ssel2: Option<PeripheralRef<'d, AnyPin>>,
    //ssel3: Option<PeripheralRef<'d, AnyPin>>,
    dma_ch_rx: Option<dma::channel::Channel<'d>>,
    dma_ch_tx: Option<dma::channel::Channel<'d>>,
}


impl<'d, M: Mode> SpiController<'d, M> {
    fn new_inner<T: Instance>(
        _bus: impl Peripheral<P = T> + 'd,
        configuration: Config,
        sclk: impl Peripheral<P = impl SclkPin<T>> + 'd,
        miso: impl Peripheral<P = impl MisoPin<T>> + 'd,
        mosi: impl Peripheral<P = impl MosiPin<T>> + 'd,
        ssel0: Option<impl Peripheral<P = impl SselPin<T>> + 'd>,
        //ssel1: Option<impl Peripheral<P = impl SselPin<T>> + 'd>,
        //ssel2: Option<impl Peripheral<P = impl SselPin<T>> + 'd>,
        //ssel3: Option<impl Peripheral<P = impl SselPin<T>> + 'd>,
        dma_ch_rx: Option<dma::channel::Channel<'d>>,
        dma_ch_tx: Option<dma::channel::Channel<'d>>,
    ) -> Result<Self> {

        // TODO - clock integration. Assuming 16M Hz for sfro
        let clock = crate::flexcomm::Clock::Sfro;
        let source_clock_freq: u32 = 16_000_000;

        // enable clock source in flexcomm
        T::enable(clock);
        // set flexcomm channel to SPI
        T::into_spi();

        if configuration.frequency > SPI_MAX_SCLK_FREQ {
            return Err(Error::UnsupportedSclkFrequency);
        }

        into_ref!(_bus);
        into_ref!(sclk);
        into_ref!(miso);
        into_ref!(mosi);

        let spi_instance = Self {
            info: T::info(),
            _phantom: PhantomData,
            config: configuration,
            //ssel0: None,
            //ssel1: None,
            //ssel2: None,
            //ssel3: None,
            dma_ch_rx: dma_ch_rx,
            dma_ch_tx: dma_ch_tx,
        };

        // first, make sure it is disabled
        spi_instance.info.regs.cfg().modify(|_, w| w.enable().disabled());

        // set controller mode
        spi_instance.info.regs.cfg().modify(|_, w| w.master().master_mode());

        // todo: add config item for msb/lsb first. current implementation assumes standard lsb first
        spi_instance.info.regs.cfg().modify(|_, w| w.lsbf().standard());

        // set phase
        spi_instance.info.regs.cfg().modify(|_, w| match configuration.phase {
            Phase::CaptureOnFirstTransition => w.cpha().change(),
            Phase::CaptureOnSecondTransition => w.cpha().capture(),
        });

        // set polarity
        spi_instance
            .info
            .regs
            .cfg()
            .modify(|_, w| match configuration.polarity {
                Polarity::IdleLow => w.cpol().low(),
                Polarity::IdleHigh => w.cpol().high(),
            });

        // todo: add config items for chip select polarity. current implementation: active low
        spi_instance.info.regs.cfg().modify(|_, w| w.spol0().low());
        spi_instance.info.regs.cfg().modify(|_, w| w.spol1().low());
        spi_instance.info.regs.cfg().modify(|_, w| w.spol2().low());
        spi_instance.info.regs.cfg().modify(|_, w| w.spol3().low());

        // todo: calculate post divider
        let divider = calc_div(source_clock_freq, configuration.frequency);
        spi_instance.info.regs.div().write(|w| 
            // SAFETY: only unsafe due to .bits usage
            unsafe {w.divval().bits(divider)});

        // todo: add config items for delay. currently assuming 0 delay per typical legacy fw implementation
        spi_instance.info.regs.dly().write(|w| 
            // SAFETY: only unsafe due to .bits usage
            unsafe {w.frame_delay().bits(0).pre_delay().bits(0).post_delay().bits(0).transfer_delay().bits(0)});

        // todo: enable dma in fifo config when dma support is added to async mode
        spi_instance.info.regs.fifocfg().write(|w| 
            w.enablerx().enabled().enabletx().enabled().emptyrx().set_bit().emptytx().set_bit());

        // spi is disabled, so this just clears the chip selects, and does not initiate fifo transfers
        //spi_instance.info.regs.fifowr().write(|w| 
            // SAFETY: only unsafe due to .bits usage
        //    unsafe {w.len().bits(7).txssel0_n().set_bit().txssel1_n().set_bit().txssel2_n().set_bit().txssel3_n().set_bit() });

        // fifo status: clear status bits
        spi_instance.info.regs.fifostat().write(|w| 
            w.txerr().set_bit().rxerr().set_bit());
    
        // fifotrg: disable all triggers. Triggers will be enabled when initiating transfers
        spi_instance.info.regs.fifotrig().write(|w| 
            // SAFETY: only unsafe due to .bits usage
            unsafe {w.bits(0)});

        // configure spi pins
        sclk.as_sclk();
        miso.as_miso();
        mosi.as_mosi();
        // only enable required chip selects 
        if ssel0.is_some() {
            let mut ssel0 = ssel0.unwrap(); 
            let mut ssel0 = ssel0.into_ref(); 
            ssel0.as_ssel();
            //let ssel: PeripheralRef<'_, AnyPin> = ssel0.map_into();
            //spi_instance.ssel0 = Some(ssel);
        } 
        /*
        if ssel1.is_some() {
            let mut ssel1 = ssel1.unwrap(); 
            let mut ssel1 = ssel1.into_ref(); 
            ssel1.as_ssel();
            spi_instance.ssel1 = Some(ssel1);
        } 
        if ssel2.is_some() {
            let mut ssel2 = ssel2.unwrap(); 
            let mut ssel2 = ssel2.into_ref(); 
            ssel2.as_ssel();
        } 
        if ssel3.is_some() {
            let mut ssel3 = ssel3.unwrap(); 
            let mut ssel3 = ssel3.into_ref(); 
            ssel3.as_ssel();
        } 
        */

        // enable spi
        spi_instance.info.regs.cfg().modify(|_, w| w.enable().enabled());

        Ok(spi_instance)
    }

}

impl<'d> SpiController<'d, Blocking> {
    /// Create an SPI driver in blocking mode.
    pub fn new_blocking<T: Instance>(
        fc: impl Peripheral<P = T> + 'd,
        config: Config,
        sclk: impl Peripheral<P = impl SclkPin<T>> + 'd,
        miso: impl Peripheral<P =impl MisoPin<T>> + 'd,
        mosi: impl Peripheral<P =impl MosiPin<T>> + 'd,
        ssel0: Option<impl Peripheral<P =impl SselPin<T>> + 'd>,
        //ssel1: Option<impl Peripheral<P =impl SselPin<T>> + 'd>,
        //ssel2: Option<impl Peripheral<P =impl SselPin<T>> + 'd>,
        //ssel3: Option<impl Peripheral<P =impl SselPin<T>> + 'd>,
    ) -> Result<Self> {

        let this = Self::new_inner::<T>(
            fc,
            config,
            sclk,
            miso,
            mosi,
            ssel0,
            //ssel1,
            //ssel2,
            //ssel3,
            None,
            None,
        )?;

        Ok(this)
    }

    /// Read data from SPI blocking execution until done.
    fn blocking_read(&mut self, data: &mut [u8]) -> Result<()> {
        // todo
        /*
        for b in data {
            while !p.sr().read().tnf() {}
            p.dr().write(|w| w.set_data(0));
            while !p.sr().read().rne() {}
            *b = p.dr().read().data() as u8;
        }
        */
        self.blocking_flush()?;
        Ok(())
    }

    /// Write data to SPI blocking execution until done.
    fn blocking_write(&mut self, data: &[u8]) -> Result<()> {
        //let _p = self.bus.spi();
        // todo
        /*
        for &b in data {
            while !p.stat().read().mstidle() {}
            p.dr().write(|w| w.set_data(b as _));
            while !p.sr().read().rne() {}
            let _ = p.dr().read();
        }
        */
        self.blocking_flush()?;
        Ok(())
    }

    /// Transfer data to SPI blocking execution until done.
    fn blocking_transfer(&mut self, read: &mut [u8], write: &[u8]) -> Result<()> {
        let p = self.info.regs;
        let len = read.len().max(write.len());

        // todo: add chip select management. currenly assuming ssel0 is asserted for the entire transfer
        
        for i in 0..len {
            let wb: u8 = write.get(i).copied().unwrap_or(0);
            // wait until txfifo is not full
            while p.fifostat().read().txnotfull().bit_is_clear() {}
            // write 1 byte to txfifo

            if (i < len - 1) {
                // continue to tx, keep ssel asserted 
                p.fifowr().write(|w| 
                    // SAFETY: only unsafe due to .bits usage
                    unsafe { w.txdata().bits(wb.into()).
                        // 8 bit data = len 7 
                        len().bits(7).
                        // not eot. keep ssel asserted
                        eot().clear_bit().
                        // not eof 
                        eof().clear_bit().
                        // assert ssel0
                        txssel0_n().clear_bit() });
            } else {
                // clear ssel after this, last tx 
                p.fifowr().write(|w| 
                    // SAFETY: only unsafe due to .bits usage
                    unsafe { w.txdata().bits(wb.into()).
                        // 8 bit data = len 7 
                        len().bits(7).
                        // eot. clear ssel after this byte
                        eot().set_bit().
                        // not eof 
                        eof().clear_bit().
                        // assert ssel0
                        txssel0_n().clear_bit() });
            }
            
            // wait for rx data available
            while p.fifostat().read().rxnotempty().bit_is_clear() {}
            // read rxfifo, one 8 bit only
            let rd: u8 = p.fiford().read().rxdata().bits().try_into().unwrap();
            // only buffer rx data if requested, and not full
            if (read.len() != 0) && (i < read.len())  {
                read[i] = rd;
            }
        }

        self.blocking_flush()?;
        Ok(())
    }

    /// Transfer data in place to SPI blocking execution until done.
    fn blocking_transfer_in_place(&mut self, data: &mut [u8]) -> Result<()> {
        //let _p = self.bus.spi();
        // todo
        /*
        for b in data {
            while !p.sr().read().tnf() {}
            p.dr().write(|w| w.set_data(*b as _));
            while !p.sr().read().rne() {}
            *b = p.dr().read().data() as u8;
        }
        */
        self.blocking_flush()?;
        Ok(())
    }

    /// Block execution until SPI is done.
    fn blocking_flush(&mut self) -> Result<()> {
        //let _p = self.bus.spi();
        // todo
        // confirm spi bus is idle
        // while p.sr().read().bsy() {}
        Ok(())
    }
}

impl<'d> SpiController<'d, Async> {
    /// Create an SPI driver in async mode.
    pub async fn new_async<T: Instance, D: dma::Instance, E: dma::Instance>(
        fc: impl Peripheral<P = T> + 'd,
        config: Config,
        sclk: impl Peripheral<P = impl SclkPin<T>> + 'd,
        miso: impl Peripheral<P =impl MisoPin<T>> + 'd,
        mosi: impl Peripheral<P =impl MosiPin<T>> + 'd,
        ssel0: Option<impl Peripheral<P =impl SselPin<T>> + 'd>,
        //ssel1: Option<impl Peripheral<P =impl SselPin<T>> + 'd>,
        //ssel2: Option<impl Peripheral<P =impl SselPin<T>> + 'd>,
        //ssel3: Option<impl Peripheral<P =impl SselPin<T>> + 'd>,
        dma_ch_rx: impl Peripheral<P = D> + 'd,
        dma_ch_tx: impl Peripheral<P = E> + 'd,
    ) -> Result<Self> {

        let res_dm_ch_rx = dma::Dma::reserve_channel(dma_ch_rx);
        let res_dm_ch_tx = dma::Dma::reserve_channel(dma_ch_tx);
        let this = Self::new_inner::<T>(
            fc,
            config,
            sclk,
            miso,
            mosi,
            ssel0,
            //ssel1,
            //ssel2,
            //ssel3,
            Some(res_dm_ch_rx),
            Some(res_dm_ch_tx),
        )?;

        T::Interrupt::unpend();
        unsafe { T::Interrupt::enable() };

        Ok(this)
    }

    /// Read data from SPI async execution until done.
    async fn async_read(&mut self, _data: &mut [u8]) -> Result<()> {
        let _cfg = self.info.regs.cfg().read();
        // todo
        Ok(())
    }

    /// Write data to SPI async execution until done.
    async fn async_write(&mut self, _data: &[u8]) -> Result<()> {
        let _cfg = self.info.regs.cfg().read();
        // todo
        Ok(())
    }

    /// Transfer data to SPI async execution until done.
    async fn async_transfer(&mut self, _read: &mut [u8], _write: &[u8]) -> Result<()> {
        let _cfg = self.info.regs.cfg().read();
        // todo
        Ok(())
    }

    /// Transfer data in place SPI async execution until done.
    async fn async_transfer_in_place(&mut self, _data: &mut [u8]) -> Result<()> {
        let _cfg = self.info.regs.cfg().read();
        // todo
        Ok(())
    }

    /// Block execution until SPI is done.
    async fn async_flush(&mut self) -> Result<()> {
        let _cfg = self.info.regs.cfg().read();
        // todo
        Ok(())
    }
}


/// Error Types for SPI communication
impl embedded_hal_1::spi::Error for Error {
    fn kind(&self) -> embedded_hal_1::spi::ErrorKind {
        match *self {
            Self::UnsupportedSclkFrequency => embedded_hal_1::spi::ErrorKind::Other,
            Self::UnsupportedConfiguration => embedded_hal_1::spi::ErrorKind::Other,
            Self::Overrun => embedded_hal_1::spi::ErrorKind::Overrun,
            Self::ModeFault => embedded_hal_1::spi::ErrorKind::ModeFault,
            Self::FrameFormat => embedded_hal_1::spi::ErrorKind::FrameFormat,
            Self::ChipSelectFault => embedded_hal_1::spi::ErrorKind::ChipSelectFault,
            Self::Other => embedded_hal_1::spi::ErrorKind::Other,
        }
    }
}

impl<M: Mode> embedded_hal_1::spi::ErrorType for SpiController<'_, M> {
    type Error = Error;
}

impl embedded_hal_1::spi::SpiBus for SpiController<'_, Blocking> {
    fn read(&mut self, data: &mut [u8]) -> Result<()> {
        self.blocking_read(data)
    }

    fn write(&mut self, data: &[u8]) -> Result<()> {
        self.blocking_write(data)
    }

    fn transfer(&mut self, read: &mut [u8], write: &[u8]) -> Result<()> {
        self.blocking_transfer(read, write)
    }

    fn transfer_in_place(&mut self, data: &mut [u8]) -> Result<()> {
        self.blocking_transfer_in_place(data)
    }

    fn flush(&mut self) -> Result<()> {
        self.blocking_flush()
    }
}

impl embedded_hal_async::spi::SpiBus for SpiController<'_, Async> {
    async fn read(&mut self, data: &mut [u8]) -> Result<()> {
        self.async_read(data).await
    }

    async fn write(&mut self, data: &[u8]) -> Result<()> {
        self.async_write(data).await
    }

    async fn transfer(&mut self, read: &mut [u8], write: &[u8]) -> Result<()> {
        self.async_transfer(read, write).await
    }

    async fn transfer_in_place(&mut self, data: &mut [u8]) -> Result<()> {
        self.async_transfer_in_place(data).await
    }

    async fn flush(&mut self) -> Result<()> {
        self.async_flush().await
    }
}



// ====================
