//! Implements I2C function support over flexcomm + gpios
//!
//! # Target trait impls
//!
//! Besides the inherent [`I2cSlave::listen`] / [`I2cSlave::respond_to_write`] /
//! [`I2cSlave::respond_to_read`] API that returns [`Command`] / [`Response`],
//! this driver also implements the [`embedded_mcu_hal::i2c::target`] traits:
//!
//! - [`embedded_mcu_hal::i2c::target::blocking::I2c`] for `I2cSlave<'_, Blocking>`
//! - [`embedded_mcu_hal::i2c::target::asynch::I2c`] for `I2cSlave<'_, Async>`
//!
//! Both flavours are implemented twice — once for `SevenBitAddress` and once
//! for `TenBitAddress`. The implementation that matches the address mode
//! configured at construction time succeeds; the mismatched implementation
//! returns [`Error::UnsupportedConfiguration`], which maps to
//! [`ErrorKind::Other`](embedded_mcu_hal::i2c::target::ErrorKind::Other).
//!
//! The trait API surfaces extra information that the inherent API collapses:
//! the matched address payload on every event, restart and stop edges as
//! distinct [`Request`](embedded_mcu_hal::i2c::target::Request) variants, and
//! a `recover` method to re-baseline the peripheral after a cancelled
//! `respond_*` future. Probes (zero-byte writes) surface as
//! [`Request::Stop`](embedded_mcu_hal::i2c::target::Request::Stop) directly,
//! with no preceding `Write` event — the strict interpretation that a probe
//! is just an address-then-STOP on the wire.

use core::future::{Future, poll_fn};
use core::marker::PhantomData;
use core::sync::atomic::Ordering;
use core::task::Poll;

use embassy_hal_internal::Peri;
use embassy_hal_internal::drop::OnDrop;
use embedded_mcu_hal::i2c::{SevenBitAddress, TenBitAddress, target as mcu_target};

use super::{
    Async, Blocking, Error, Info, Instance, InterruptHandler, Mode, REMEDIATON_NONE, REMEDIATON_SLAVE_NAK, Result,
    SclPin, SdaPin, SlaveDma, TEN_BIT_PREFIX, TransferError,
};
use crate::flexcomm::FlexcommRef;
use crate::interrupt::typelevel::Interrupt;
use crate::pac::i2c0::stat::Slvstate;
use crate::{dma, interrupt};

/// Address errors
#[derive(Copy, Clone, Debug)]
pub enum AddressError {
    /// Invalid address conversion
    InvalidConversion,
}

/// I2C address type
#[derive(Copy, Clone, Debug)]
pub enum Address {
    /// 7-bit address
    SevenBit(u8),
    /// 10-bit address
    TenBit(u16),
}

impl Address {
    /// Construct a 7-bit address type
    #[must_use]
    pub const fn new(addr: u8) -> Option<Self> {
        match addr {
            0x08..=0x77 => Some(Self::SevenBit(addr)),
            _ => None,
        }
    }

    /// Construct a 10-bit address type
    #[must_use]
    pub const fn new_10bit(addr: u16) -> Option<Self> {
        match addr {
            0x080..=0x3FF => Some(Self::TenBit(addr)),
            _ => None,
        }
    }

    /// interpret address as a read command
    #[must_use]
    pub fn read(&self) -> [u8; 2] {
        match self {
            Self::SevenBit(addr) => [(addr << 1) | 1, 0],
            Self::TenBit(addr) => [(((addr >> 8) as u8) << 1) | TEN_BIT_PREFIX | 1, (addr & 0xFF) as u8],
        }
    }

    /// interpret address as a write command
    #[must_use]
    pub fn write(&self) -> [u8; 2] {
        match self {
            Self::SevenBit(addr) => [addr << 1, 0],
            Self::TenBit(addr) => [(((addr >> 8) as u8) << 1) | TEN_BIT_PREFIX, (addr & 0xFF) as u8],
        }
    }
}

impl TryFrom<Address> for u8 {
    type Error = AddressError;

    fn try_from(value: Address) -> core::result::Result<Self, Self::Error> {
        match value {
            Address::SevenBit(addr) => Ok(addr),
            Address::TenBit(_) => Err(AddressError::InvalidConversion),
        }
    }
}

impl TryFrom<Address> for u16 {
    type Error = AddressError;

    fn try_from(value: Address) -> core::result::Result<Self, Self::Error> {
        match value {
            Address::SevenBit(addr) => Ok(addr as u16),
            Address::TenBit(addr) => Ok(addr),
        }
    }
}

#[derive(Copy, Clone, Debug)]
struct TenBitAddressInfo {
    first_byte: u8,
    second_byte: u8,
}

impl TenBitAddressInfo {
    fn new(address: u16) -> Self {
        Self {
            first_byte: (((address >> 8) as u8) << 1) | TEN_BIT_PREFIX,
            second_byte: (address & 0xFF) as u8,
        }
    }
}

/// Command from master
pub enum Command {
    /// I2C probe with no data
    Probe,

    /// I2C Read
    Read,

    /// I2C Write
    Write,
}

/// Result of response functions
pub enum Response {
    /// I2C transaction complete with this amount of bytes
    Complete(usize),

    /// I2C transaction pending with this amount of bytes completed so far
    Pending(usize),
}

/// Bus event observed by the internal `listen` helpers.
///
/// Richer than the public [`Command`] — it preserves the matched address
/// so the trait-impl wrapper can populate
/// [`Request`](embedded_mcu_hal::i2c::target::Request)'s `A` payload, and it
/// distinguishes the probe (address-only, terminated by STOP) from a
/// data-bearing write/read.
#[derive(Copy, Clone, Debug)]
enum InternalEvent {
    /// 0-byte write transaction (address-only ACK then STOP).
    Probe { addr: AddressKind },
    /// Controller is about to read from this target.
    Read { addr: AddressKind },
    /// Controller is about to write to this target.
    Write { addr: AddressKind },
}

/// Concrete address (7- or 10-bit) that just matched on the bus.
#[derive(Copy, Clone, Debug)]
enum AddressKind {
    Seven(u8),
    Ten(u16),
}

/// Reason a `respond_to_*` inner helper returned.
///
/// Richer than the public [`Response`] — distinguishes Stop vs Restart vs
/// BufferFull vs NeedMore vs EarlyStop, all observable from the existing
/// `slvdesel` / `slvstate` / buffer-exhaustion signals.
#[derive(Copy, Clone, Debug)]
enum InternalTermination {
    /// Controller issued a `STOP`. `n` = bytes moved.
    Stopped(usize),
    /// Controller issued a repeated `START`. `n` = bytes moved.
    Restarted(usize),
    /// Supplied buffer was exhausted, controller still expects more
    /// (writing more bytes / clocking more reads). `n` = buffer length.
    Continued(usize),
    /// Read-only: buffer fully consumed at exactly the moment the
    /// controller NACK+STOPped. `n` = buffer length.
    ReadComplete(usize),
    /// Read-only: controller terminated with STOP (or Sr) before the
    /// buffer ran out. `n` = bytes moved.
    ReadEarlyStop(usize),
}

/// Edge event queued by a previous `respond_to_*` for the next `listen` call.
///
/// Only used by the trait impls — the inherent `listen` ignores this field.
/// Today only `RepeatedStart` is ever queued; a `STOP` terminator is folded
/// into the `WriteStatus::Stopped` / `ReadStatus::Complete` payload of the
/// preceding `respond_to_*` call rather than synthesised as a separate
/// `listen` event.
#[derive(Copy, Clone, Debug)]
enum EdgeKind {
    /// Surface a [`Request::RepeatedStart`](mcu_target::Request::RepeatedStart)
    /// at the next `listen`, then resume hardware polling for the next
    /// addressed event.
    RepeatedStart,
}

/// Per-driver pending-edge bookkeeping for the target trait impls.
///
/// Tracks the address that matched on the most recent addressed event and
/// any restart/stop edge that should be surfaced before the next hardware
/// poll. Populated only by the target trait helpers.
#[derive(Copy, Clone, Debug, Default)]
struct PendingEdge {
    last_addr: Option<AddressKind>,
    pending: Option<EdgeKind>,
}

/// use `FCn` as I2C Slave controller
pub struct I2cSlave<'a, M: Mode> {
    info: Info,
    _flexcomm: FlexcommRef,
    _phantom: PhantomData<M>,
    dma_ch: Option<dma::channel::Channel<'a>>,
    ten_bit_info: Option<TenBitAddressInfo>,
    /// Address configured at construction time. Used by the target trait
    /// impls to populate the `A` payload on
    /// [`Request`](mcu_target::Request) variants and to enforce the
    /// runtime address-mode check.
    configured_address: Address,
    /// Pending edge bookkeeping for the target trait impls. The inherent
    /// API does not touch this field.
    pending: core::cell::Cell<PendingEdge>,
}

impl<'a, M: Mode> I2cSlave<'a, M> {
    /// use flexcomm fc with Pins scl, sda as an I2C Master bus, configuring to speed and pull
    fn new_inner<T: Instance>(
        _bus: Peri<'a, T>,
        scl: Peri<'a, impl SclPin<T>>,
        sda: Peri<'a, impl SdaPin<T>>,
        // TODO - integrate clock APIs to allow dynamic freq selection | clock: crate::flexcomm::Clock,
        address: Address,
        dma_ch: Option<dma::channel::Channel<'a>>,
    ) -> Result<Self> {
        // TODO - clock integration
        let clock = crate::flexcomm::Clock::Sfro;
        let flexcomm = T::enable(clock);
        T::into_i2c();

        sda.as_sda();
        scl.as_scl();

        // this check should be redundant with T::set_mode()? above
        let info = T::info();
        let i2c = info.regs;
        let mut ten_bit_info = None;

        // rates taken assuming SFRO:
        //
        //  7 => 403.3 kHz
        //  9 => 322.6 kHz
        // 12 => 247.8 kHz
        // 16 => 198.2 kHz
        // 18 => 166.6 Khz
        // 22 => 142.6 kHz
        // 30 => 100.0 kHz
        // UM10204 pg.44 rev7
        // tSU;DAT >= 250ns -> < 250MHz
        i2c.clkdiv().write(|w|
            // SAFETY: only unsafe due to .bits usage
            unsafe { w.divval().bits(0) });

        match address {
            Address::SevenBit(addr) => {
                // address 0 match = addr, per UM11147 24.3.2.1
                i2c.slvadr(0).modify(|_, w|
                        // note: shift is omitted as performed via w.slvadr() 
                        // SAFETY: unsafe only required due to use of unnamed "bits" field
                        unsafe{w.slvadr().bits(addr)}.sadisable().enabled());
            }
            Address::TenBit(addr) => {
                // Save the 10 bit address to use later
                let ten_bit_address = TenBitAddressInfo::new(addr);

                // address 0 match = addr first byte, per UM11147 24.7.4
                i2c.slvadr(0).modify(|_, w|
                    // note: byte needs to be adjusted for shift performed via w.slvadr()
                    // SAFETY: unsafe only required due to use of unnamed "bits" field
                    unsafe{w.slvadr().bits(ten_bit_address.first_byte >> 1)}.sadisable().enabled());

                ten_bit_info = Some(ten_bit_address);
            }
        }

        // SLVEN = 1, per UM11147 24.3.2.1
        i2c.cfg().write(|w| w.slven().enabled());

        Ok(Self {
            info,
            _flexcomm: flexcomm,
            _phantom: PhantomData,
            dma_ch,
            ten_bit_info,
            configured_address: address,
            pending: core::cell::Cell::new(PendingEdge::default()),
        })
    }
}

impl<'a> I2cSlave<'a, Blocking> {
    /// use flexcomm fc with Pins scl, sda as an I2C Master bus, configuring to speed and pull
    pub fn new_blocking<T: Instance>(
        _bus: Peri<'a, T>,
        scl: Peri<'a, impl SclPin<T>>,
        sda: Peri<'a, impl SdaPin<T>>,
        // TODO - integrate clock APIs to allow dynamic freq selection | clock: crate::flexcomm::Clock,
        address: Address,
    ) -> Result<Self> {
        Self::new_inner::<T>(_bus, scl, sda, address, None)
    }

    fn poll(&self) -> Result<()> {
        let i2c = self.info.regs;

        while i2c.stat().read().slvpending().is_in_progress() && i2c.stat().read().slvdesel().is_not_deselected() {}

        Ok(())
    }

    fn block_until_addressed(&self) -> Result<()> {
        self.poll()?;

        let i2c = self.info.regs;
        if !i2c.stat().read().slvstate().is_slave_address() {
            return Err(TransferError::AddressNack.into());
        }

        i2c.slvctl().write(|w| w.slvcontinue().continue_());
        Ok(())
    }
}

impl<'a> I2cSlave<'a, Async> {
    /// use flexcomm fc with Pins scl, sda as an I2C Master bus, configuring to speed and pull
    pub fn new_async<T: Instance>(
        _bus: Peri<'a, T>,
        scl: Peri<'a, impl SclPin<T>>,
        sda: Peri<'a, impl SdaPin<T>>,
        _irq: impl interrupt::typelevel::Binding<T::Interrupt, InterruptHandler<T>> + 'a,
        // TODO - integrate clock APIs to allow dynamic freq selection | clock: crate::flexcomm::Clock,
        address: Address,
        dma_ch: Peri<'a, impl SlaveDma<T>>,
    ) -> Result<Self> {
        let ch = dma::Dma::reserve_channel(dma_ch);

        if let Some(ch) = ch {
            let this = Self::new_inner::<T>(_bus, scl, sda, address, Some(ch))?;

            T::Interrupt::unpend();
            unsafe { T::Interrupt::enable() };

            Ok(this)
        } else {
            Err(super::Error::UnsupportedConfiguration)
        }
    }
}

impl I2cSlave<'_, Blocking> {
    /// Listen for commands from the I2C Master.
    pub fn listen(&self) -> Result<Command> {
        let i2c = self.info.regs;

        self.block_until_addressed()?;

        // Block until we know it is read or write
        self.poll()?;

        if let Some(ten_bit_address) = self.ten_bit_info {
            // For 10 bit address, the first byte received is the second byte of the address
            if i2c.slvdat().read().data().bits() == ten_bit_address.second_byte {
                i2c.slvctl().write(|w| w.slvcontinue().continue_());
                self.poll()?;
            } else {
                // If the second byte of the 10 bit address is not received, then nack the address.
                i2c.slvctl().write(|w| w.slvnack().nack());
                return Ok(Command::Probe);
            }

            // Check slave is still selected, master has not sent a stop
            if i2c.stat().read().slvsel().is_selected() {
                // Check for a restart
                if i2c.stat().read().slvstate().is_slave_address() {
                    // Check if first byte of 10 bit address is received again with read bit set
                    if i2c.slvdat().read().data().bits() == ten_bit_address.first_byte | 1 {
                        i2c.slvctl().write(|w| w.slvcontinue().continue_());
                        self.poll()?;
                    } else {
                        // If the first byte of the 10 bit address is not received again, then nack the address.
                        i2c.slvctl().write(|w| w.slvnack().nack());
                        return Ok(Command::Probe);
                    }
                    // Check slave is ready for transmit
                    if !i2c.stat().read().slvstate().is_slave_transmit() {
                        return Err(TransferError::WriteFail.into());
                    }
                } else {
                    // Check slave is ready to receive
                    if !i2c.stat().read().slvstate().is_slave_receive() {
                        return Err(TransferError::ReadFail.into());
                    }
                }
            }
        }

        // We are already deselected, so it must be an 0 byte write transaction
        if i2c.stat().read().slvdesel().is_deselected() {
            // Clear the deselected bit
            i2c.stat().write(|w| w.slvdesel().deselected());
            return Ok(Command::Probe);
        }

        let state = i2c.stat().read().slvstate().variant();
        match state {
            Some(Slvstate::SlaveReceive) => Ok(Command::Write),
            Some(Slvstate::SlaveTransmit) => Ok(Command::Read),
            _ => Err(TransferError::OtherBusError.into()),
        }
    }

    /// Respond to write command from  master
    pub fn respond_to_write(&self, buf: &mut [u8]) -> Result<Response> {
        let i2c = self.info.regs;
        let mut xfer_count: usize = 0;

        for b in buf {
            //poll until something happens
            self.poll()?;

            let stat = i2c.stat().read();
            // if master send stop, we are done
            if stat.slvdesel().is_deselected() {
                break;
            }
            // if master send a restart, we are done
            if stat.slvstate().is_slave_address() {
                break;
            }

            if !stat.slvstate().is_slave_receive() {
                return Err(TransferError::ReadFail.into());
            }

            // Now we can safely read the next byte
            *b = i2c.slvdat().read().data().bits();
            i2c.slvctl().write(|w| w.slvcontinue().continue_());
            xfer_count += 1;
        }

        let stat = i2c.stat().read();
        if stat.slvdesel().is_deselected() {
            // Clear the deselect bit
            i2c.stat().write(|w| w.slvdesel().deselected());
            return Ok(Response::Complete(xfer_count));
        } else if stat.slvstate().is_slave_address() {
            // Handle restart
            return Ok(Response::Complete(xfer_count));
        } else if stat.slvstate().is_slave_receive() {
            // Master still wants to send more data, transaction incomplete
            return Ok(Response::Pending(xfer_count));
        }

        // We should not get here
        Err(TransferError::ReadFail.into())
    }

    /// Respond to read command from  master
    pub fn respond_to_read(&self, buf: &[u8]) -> Result<Response> {
        let i2c = self.info.regs;
        let mut xfer_count: usize = 0;

        for b in buf {
            // Block until something happens
            self.poll()?;

            let stat = i2c.stat().read();
            // if master send nack or stop, we are done
            if stat.slvdesel().is_deselected() {
                break;
            }
            // if master send restart, we are done
            if stat.slvstate().is_slave_address() {
                break;
            }

            // Verify that we are ready for write
            if !stat.slvstate().is_slave_transmit() {
                return Err(TransferError::WriteFail.into());
            }

            i2c.slvdat().write(|w|
                // SAFETY: unsafe only here due to use of bits()
                unsafe{w.data().bits(*b)});
            i2c.slvctl().write(|w| w.slvcontinue().continue_());
            xfer_count += 1;
        }

        let stat = i2c.stat().read();
        if stat.slvdesel().is_deselected() {
            // clear the deselect bit
            i2c.stat().write(|w| w.slvdesel().deselected());
            return Ok(Response::Complete(xfer_count));
        } else if stat.slvstate().is_slave_address() {
            // Handle restart after read
            return Ok(Response::Complete(xfer_count));
        } else if stat.slvstate().is_slave_transmit() {
            // Master is still expecting data, transaction incomplete
            return Ok(Response::Pending(xfer_count));
        }

        // We should not get here
        Err(TransferError::WriteFail.into())
    }
}

impl I2cSlave<'_, Async> {
    /// Listen for commands from the I2C Master asynchronously
    pub async fn listen(&mut self) -> Result<Command> {
        let i2c = self.info.regs;

        // Disable DMA
        i2c.slvctl().write(|w| w.slvdma().disabled());

        // Check whether we already have a matched address and just waiting
        // for software ack/nack
        if !i2c.stat().read().slvpending().is_pending() {
            self.poll_sw_action().await;
        }

        if i2c.stat().read().slvstate().is_slave_address() {
            i2c.slvctl().write(|w| w.slvcontinue().continue_());
        } else {
            // If we are already past the addressed phase and in transmit or receive, that means we are already in the
            // next state, most likely due to calling listen() before the previous transaction is completed and leading
            // to state transition out of order. We can tolerate that, so we just move onto the next state.
        }

        // Poll for HW to transitioning from addressed to receive/transmit
        self.poll_sw_action().await;

        if let Some(ten_bit_address) = self.ten_bit_info {
            // For 10 bit address, the first byte received is the second byte of the address
            if i2c.slvdat().read().data().bits() == ten_bit_address.second_byte {
                i2c.slvctl().write(|w| w.slvcontinue().continue_());
                self.poll_sw_action().await;
            } else {
                // If the second byte of the 10 bit address is not received, then nack the address.
                i2c.slvctl().write(|w| w.slvnack().nack());
                return Ok(Command::Probe);
            }

            // Check slave is still selected, master has not sent a stop
            if i2c.stat().read().slvsel().is_selected() {
                // Check for a restart
                if i2c.stat().read().slvstate().is_slave_address() {
                    // Check if first byte of 10 bit address is received again with read bit set
                    if i2c.slvdat().read().data().bits() == ten_bit_address.first_byte | 1 {
                        i2c.slvctl().write(|w| w.slvcontinue().continue_());
                        self.poll_sw_action().await;
                    } else {
                        // If the first byte of the 10 bit address is not received again, then nack the address.
                        i2c.slvctl().write(|w| w.slvnack().nack());
                        return Ok(Command::Probe);
                    }
                    // Check slave is ready for transmit
                    if !i2c.stat().read().slvstate().is_slave_transmit() {
                        return Err(TransferError::WriteFail.into());
                    }
                } else {
                    // Check slave is ready to receive
                    if !i2c.stat().read().slvstate().is_slave_receive() {
                        return Err(TransferError::ReadFail.into());
                    }
                }
            }
        }

        // We are deselected, so it must be an 0 byte write transaction
        if i2c.stat().read().slvdesel().is_deselected() {
            // Clear the deselected bit
            i2c.stat().write(|w| w.slvdesel().deselected());
            return Ok(Command::Probe);
        }

        let state = i2c.stat().read().slvstate().variant();
        match state {
            Some(Slvstate::SlaveReceive) => Ok(Command::Write),
            Some(Slvstate::SlaveTransmit) => Ok(Command::Read),
            _ => Err(TransferError::OtherBusError.into()),
        }
    }

    /// Respond to write command from master
    pub async fn respond_to_write(&mut self, buf: &mut [u8]) -> Result<Response> {
        let i2c = self.info.regs;
        let buf_len = buf.len();

        // Verify that we are ready for write
        let stat = i2c.stat().read();
        if !stat.slvstate().is_slave_receive() {
            // 0 byte write
            if stat.slvdesel().is_deselected() {
                return Ok(Response::Complete(0));
            }
            return Err(TransferError::ReadFail.into());
        }

        let dma_channel = self.dma_ch.as_ref().ok_or(Error::UnsupportedConfiguration)?;

        // Enable DMA
        i2c.slvctl().write(|w| w.slvdma().enabled());

        // Enable interrupt
        i2c.intenset()
            .write(|w| w.slvpendingen().enabled().slvdeselen().enabled());

        let options = dma::transfer::TransferOptions::default();
        // Keep a reference to Transfer so it does not get dropped and aborted the DMA transfer
        let _transfer = dma_channel.read_from_peripheral(i2c.slvdat().as_ptr() as *mut u8, buf, options);

        // Hold guard to make sure that we send a NAK on cancellation
        // Since drop order is reverse, this comes BEFORE the dma guard,
        // so the DMA guard will be dropped FIRST, then the NAK guard.
        let nak_guard = NakGuard { info: self.info };
        // Hold guard to disable on cancellation or completion
        let _dma_guard = OnDrop::new(|| {
            i2c.slvctl().modify(|_r, w| w.slvdma().disabled());
        });

        poll_fn(|cx| {
            let i2c = self.info.regs;

            self.info.waker.register(cx.waker());
            dma_channel.get_waker().register(cx.waker());

            let stat = i2c.stat().read();
            // Did master send a stop?
            if stat.slvdesel().is_deselected() {
                return Poll::Ready(());
            }
            // Does SW need to intervene?
            if stat.slvpending().is_pending() {
                return Poll::Ready(());
            }
            // Did we complete the DMA transfer and does the master still have more data for us?
            if !dma_channel.is_active() && stat.slvstate().is_slave_receive() {
                return Poll::Ready(());
            }

            Poll::Pending
        })
        .await;

        // Complete DMA transaction and get transfer count
        nak_guard.defuse();
        let xfer_count = self.abort_dma(buf_len)?;
        let stat = i2c.stat().read();
        // We got a stop from master, either way this transaction is
        // completed
        if stat.slvdesel().is_deselected() {
            // Clear the deselected bit
            i2c.stat().write(|w| w.slvdesel().deselected());

            return Ok(Response::Complete(xfer_count));
        } else if stat.slvstate().is_slave_address() {
            // We are addressed again, so this must be a restart
            return Ok(Response::Complete(xfer_count));
        } else if stat.slvstate().is_slave_receive() {
            // That was a partial transaction, the master wants to send more
            // data
            return Ok(Response::Pending(xfer_count));
        }

        Err(TransferError::ReadFail.into())
    }

    /// Respond to read command from master
    /// User must provide enough data to complete the transaction or else
    ///    we will get stuck in this function
    pub async fn respond_to_read(&mut self, buf: &[u8]) -> Result<Response> {
        let i2c = self.info.regs;

        // Verify that we are ready for transmit
        if !i2c.stat().read().slvstate().is_slave_transmit() {
            return Err(TransferError::WriteFail.into());
        }

        // Enable DMA
        i2c.slvctl().write(|w| w.slvdma().enabled());

        // Enable interrupts
        i2c.intenset()
            .write(|w| w.slvpendingen().enabled().slvdeselen().enabled());

        let options = dma::transfer::TransferOptions::default();
        let dma_channel = self.dma_ch.as_ref().ok_or(Error::UnsupportedConfiguration)?;

        // Keep a reference to Transfer so it does not get dropped and aborted the DMA transfer
        let _transfer = dma_channel.write_to_peripheral(buf, i2c.slvdat().as_ptr() as *mut u8, options);

        // Hold guard to disable on cancellation or completion
        let _dma_guard = OnDrop::new(|| {
            i2c.slvctl().modify(|_r, w| w.slvdma().disabled());
        });

        poll_fn(|cx| {
            let i2c = self.info.regs;

            self.info.waker.register(cx.waker());
            dma_channel.get_waker().register(cx.waker());

            let stat = i2c.stat().read();
            // Master sent a stop or nack
            if stat.slvdesel().is_deselected() {
                return Poll::Ready(());
            }
            // We need SW intervention
            if stat.slvpending().is_pending() {
                return Poll::Ready(());
            }

            Poll::Pending
        })
        .await;

        // Complete DMA transaction and get transfer count
        let xfer_count = self.abort_dma(buf.len())?;
        let stat = i2c.stat().read();

        // we got a nack or a stop from master, either way this transaction is
        // completed
        if stat.slvdesel().is_deselected() {
            // clear the deselect bit
            i2c.stat().write(|w| w.slvdesel().deselected());
            return Ok(Response::Complete(xfer_count));
        } else if stat.slvpending().is_pending() || stat.slvstate().is_slave_address() {
            // Handle restart after read as well as the cases where
            // slave deselected is not set in response to a master nack
            // then the next transaction starts the slave state goes into
            // pending + addressed.
            return Ok(Response::Complete(xfer_count));
        }

        // We should not get here
        Err(TransferError::WriteFail.into())
    }

    fn poll_sw_action(&self) -> impl Future<Output = ()> + use<'_> {
        let i2c = self.info.regs;

        i2c.intenset()
            .write(|w| w.slvpendingen().enabled().slvdeselen().enabled());

        poll_fn(move |cx: &mut core::task::Context<'_>| {
            self.info.waker.register(cx.waker());

            let stat = i2c.stat().read();
            if stat.slvdesel().is_deselected() {
                return Poll::Ready(());
            }
            if stat.slvpending().is_pending() {
                return Poll::Ready(());
            }

            Poll::Pending
        })
    }

    /// Complete DMA and return bytes transfer
    fn abort_dma(&self, xfer_size: usize) -> Result<usize> {
        // abort DMA if DMA is not completed
        let dma = self.dma_ch.as_ref().ok_or(Error::UnsupportedConfiguration)?;
        let remain_xfer_count = dma.get_xfer_count();
        let mut xfer_count = xfer_size;
        if dma.is_active() && remain_xfer_count != 0x3FF {
            xfer_count -= remain_xfer_count as usize + 1;
            dma.abort();
        }

        Ok(xfer_count)
    }
}

/// This guard represents that we have started being written to, but without completing
/// the write. If this guard is dropped without calling [`NakGuard::defuse()`],
/// then we will signal the interrupt handler to send a NAK the next time that the
/// I2C peripheral engine is in the PENDING state.
///
/// According to 24.6.11 Table 577 of the reference manual, if the I2C peripheral is
/// NOT in the PENDING state, then it will not accept commands, including the NAK
/// command. Rather than busy-spin in the drop function for this state to be reached,
/// or leaving the bus in the un-stopped state, we ask the interrupt handler to do
/// it for us.
#[must_use]
struct NakGuard {
    info: Info,
}

impl NakGuard {
    fn defuse(self) {
        core::mem::forget(self);
    }
}

impl Drop for NakGuard {
    fn drop(&mut self) {
        // This is done in a critical section to ensure that we don't race with the
        // I2C interrupt. This could potentially be done without a critical section,
        // however the duration is extremely short, and doesn't require a loop to do
        // so.
        critical_section::with(|_| {
            // Ensure the SLV pending enable interrupt is active, in case we need it
            self.info.regs.intenset().write(|w| w.slvpendingen().set_bit());
            // Check if the i2c engine is in a pending state, ready to accept commands
            let is_pending = self.info.regs.stat().read().slvpending().is_pending();

            if is_pending {
                // We are pending, we can issue the NAK immediately
                self.info.regs.slvctl().write(|w| w.slvnack().set_bit());
            } else {
                // We are NOT pending, we need to ask the interrupt to send a NAK the next
                // time the engine is pending. We ensured that the interrupt is active above.
                self.info.remediation.fetch_or(REMEDIATON_SLAVE_NAK, Ordering::AcqRel);
            }
        })
    }
}

// ---------------------------------------------------------------------------
// embedded-mcu-hal::i2c::target trait impls
// ---------------------------------------------------------------------------
//
// The traits are layered on top of the existing inherent API. They preserve
// the inherent API verbatim and add:
//
// - A `recover` method to re-baseline the peripheral after a cancelled or
//   wedged transfer.
// - A `Request<A>` shape that carries the matched address and surfaces
//   `RepeatedStart` / `Stop` as their own events (synthesised from the
//   peripheral's `slvdesel` / `slvstate` bits).
// - `ReadStatus` / `WriteStatus` enums that distinguish the three possible
//   terminators per direction.
//
// The address-mode generic is handled by writing two separate trait impl
// blocks per flavour (one for `SevenBitAddress`, one for `TenBitAddress`).
// At runtime the impl checks the address type configured at construction
// time and returns `ErrorKind::Other` from `listen` if the wrong impl was
// invoked.

impl AddressKind {
    fn as_u8(self) -> Option<u8> {
        match self {
            Self::Seven(a) => Some(a),
            Self::Ten(_) => None,
        }
    }

    fn as_u16(self) -> u16 {
        match self {
            Self::Seven(a) => a as u16,
            Self::Ten(a) => a,
        }
    }
}

impl<M: Mode> I2cSlave<'_, M> {
    /// Snapshot of the configured address as an [`AddressKind`].
    fn matched_address(&self) -> AddressKind {
        match self.configured_address {
            Address::SevenBit(a) => AddressKind::Seven(a),
            Address::TenBit(a) => AddressKind::Ten(a),
        }
    }

    /// Update the pending-edge bookkeeping with the address that just
    /// matched on the bus. Called from every successful inner-listen.
    fn note_match(&self, addr: AddressKind) {
        let mut p = self.pending.get();
        p.last_addr = Some(addr);
        self.pending.set(p);
    }

    /// Queue an edge to be surfaced at the next trait-level `listen`.
    fn queue_edge(&self, edge: EdgeKind) {
        let mut p = self.pending.get();
        p.pending = Some(edge);
        self.pending.set(p);
    }

    /// Drain any queued edge, returning the matching
    /// [`mcu_target::Request`]. Returns `None` if there is no queued edge.
    fn drain_edge<A>(&self, addr_for: fn(AddressKind) -> A) -> Option<mcu_target::Request<A>>
    where
        A: embedded_hal_1::i2c::AddressMode,
    {
        let mut p = self.pending.get();
        let edge = p.pending.take()?;
        let addr = p.last_addr.unwrap_or_else(|| self.matched_address());
        self.pending.set(p);
        Some(match edge {
            EdgeKind::RepeatedStart => mcu_target::Request::RepeatedStart(addr_for(addr)),
        })
    }

    /// Address-mode runtime guard. Returns `Err(UnsupportedConfiguration)`
    /// when the trait impl being driven does not match the configured
    /// address type — for example, calling the
    /// `I2c<SevenBitAddress>` impl on a slave constructed with a 10-bit
    /// address.
    fn require_address_kind(&self, want_ten_bit: bool) -> Result<()> {
        let is_ten_bit = self.ten_bit_info.is_some();
        if is_ten_bit == want_ten_bit {
            Ok(())
        } else {
            Err(Error::UnsupportedConfiguration)
        }
    }
}

/// Convert a [`InternalTermination`] coming out of a write helper to the
/// corresponding [`mcu_target::WriteStatus`], queuing any edge that needs
/// to be surfaced at the next `listen`.
fn write_termination_to_status<M: Mode>(slave: &I2cSlave<'_, M>, term: InternalTermination) -> mcu_target::WriteStatus {
    match term {
        InternalTermination::Stopped(n) => {
            // Stopped is implicit in the WriteStatus itself; no edge to queue.
            mcu_target::WriteStatus::Stopped(n)
        }
        InternalTermination::Restarted(n) => {
            slave.queue_edge(EdgeKind::RepeatedStart);
            mcu_target::WriteStatus::Restarted(n)
        }
        InternalTermination::Continued(n) => mcu_target::WriteStatus::BufferFull(n),
        // Read-only terminators should never come out of a write helper.
        InternalTermination::ReadComplete(n) | InternalTermination::ReadEarlyStop(n) => {
            mcu_target::WriteStatus::Stopped(n)
        }
    }
}

/// Convert a [`InternalTermination`] coming out of a read helper to the
/// corresponding [`mcu_target::ReadStatus`], queuing any edge that needs to
/// be surfaced at the next `listen`.
fn read_termination_to_status<M: Mode>(slave: &I2cSlave<'_, M>, term: InternalTermination) -> mcu_target::ReadStatus {
    match term {
        InternalTermination::ReadComplete(n) => mcu_target::ReadStatus::Complete(n),
        InternalTermination::ReadEarlyStop(n) => mcu_target::ReadStatus::EarlyStop(n),
        InternalTermination::Continued(n) => mcu_target::ReadStatus::NeedMore(n),
        InternalTermination::Restarted(n) => {
            slave.queue_edge(EdgeKind::RepeatedStart);
            mcu_target::ReadStatus::EarlyStop(n)
        }
        InternalTermination::Stopped(n) => mcu_target::ReadStatus::EarlyStop(n),
    }
}

// ----- Internal helpers: Blocking --------------------------------------------

impl I2cSlave<'_, Blocking> {
    /// Trait-internal `listen` for the blocking flavour. Mirrors the
    /// inherent `listen` but tracks the matched address.
    fn listen_internal(&self) -> Result<InternalEvent> {
        let i2c = self.info.regs;

        self.block_until_addressed()?;

        // Block until we know it is read or write
        self.poll()?;

        if let Some(ten_bit_address) = self.ten_bit_info {
            // For 10 bit address, the first byte received is the second byte of the address
            if i2c.slvdat().read().data().bits() == ten_bit_address.second_byte {
                i2c.slvctl().write(|w| w.slvcontinue().continue_());
                self.poll()?;
            } else {
                // If the second byte of the 10 bit address is not received, then nack the address.
                i2c.slvctl().write(|w| w.slvnack().nack());
                let addr = self.matched_address();
                self.note_match(addr);
                return Ok(InternalEvent::Probe { addr });
            }

            // Check slave is still selected, master has not sent a stop
            if i2c.stat().read().slvsel().is_selected() {
                // Check for a restart
                if i2c.stat().read().slvstate().is_slave_address() {
                    // Check if first byte of 10 bit address is received again with read bit set
                    if i2c.slvdat().read().data().bits() == ten_bit_address.first_byte | 1 {
                        i2c.slvctl().write(|w| w.slvcontinue().continue_());
                        self.poll()?;
                    } else {
                        // If the first byte of the 10 bit address is not received again, then nack the address.
                        i2c.slvctl().write(|w| w.slvnack().nack());
                        let addr = self.matched_address();
                        self.note_match(addr);
                        return Ok(InternalEvent::Probe { addr });
                    }
                    // Check slave is ready for transmit
                    if !i2c.stat().read().slvstate().is_slave_transmit() {
                        return Err(TransferError::WriteFail.into());
                    }
                } else {
                    // Check slave is ready to receive
                    if !i2c.stat().read().slvstate().is_slave_receive() {
                        return Err(TransferError::ReadFail.into());
                    }
                }
            }
        }

        // We are already deselected, so it must be an 0 byte write transaction
        if i2c.stat().read().slvdesel().is_deselected() {
            // Clear the deselected bit
            i2c.stat().write(|w| w.slvdesel().deselected());
            let addr = self.matched_address();
            self.note_match(addr);
            return Ok(InternalEvent::Probe { addr });
        }

        let state = i2c.stat().read().slvstate().variant();
        let addr = self.matched_address();
        self.note_match(addr);
        match state {
            Some(Slvstate::SlaveReceive) => Ok(InternalEvent::Write { addr }),
            Some(Slvstate::SlaveTransmit) => Ok(InternalEvent::Read { addr }),
            _ => Err(TransferError::OtherBusError.into()),
        }
    }

    /// Trait-internal `respond_to_write` for the blocking flavour.
    fn respond_to_write_internal(&self, buf: &mut [u8]) -> Result<InternalTermination> {
        let i2c = self.info.regs;
        let mut xfer_count: usize = 0;
        let buf_len = buf.len();

        for b in buf {
            //poll until something happens
            self.poll()?;

            let stat = i2c.stat().read();
            // if master send stop, we are done
            if stat.slvdesel().is_deselected() {
                break;
            }
            // if master send a restart, we are done
            if stat.slvstate().is_slave_address() {
                break;
            }

            if !stat.slvstate().is_slave_receive() {
                return Err(TransferError::ReadFail.into());
            }

            // Now we can safely read the next byte
            *b = i2c.slvdat().read().data().bits();
            i2c.slvctl().write(|w| w.slvcontinue().continue_());
            xfer_count += 1;
        }

        let stat = i2c.stat().read();
        if stat.slvdesel().is_deselected() {
            // Clear the deselect bit
            i2c.stat().write(|w| w.slvdesel().deselected());
            return Ok(InternalTermination::Stopped(xfer_count));
        } else if stat.slvstate().is_slave_address() {
            // Handle restart
            return Ok(InternalTermination::Restarted(xfer_count));
        } else if stat.slvstate().is_slave_receive() {
            // Buffer exhausted; master is still sending — treat as
            // "continue with more buffer" (BufferFull at trait level,
            // Pending at the inherent-API level).
            debug_assert_eq!(xfer_count, buf_len);
            return Ok(InternalTermination::Continued(xfer_count));
        }

        // We should not get here
        Err(TransferError::ReadFail.into())
    }

    /// Trait-internal `respond_to_read` for the blocking flavour.
    fn respond_to_read_internal(&self, buf: &[u8]) -> Result<InternalTermination> {
        let i2c = self.info.regs;
        let mut xfer_count: usize = 0;
        let buf_len = buf.len();

        for b in buf {
            // Block until something happens
            self.poll()?;

            let stat = i2c.stat().read();
            // if master send nack or stop, we are done
            if stat.slvdesel().is_deselected() {
                break;
            }
            // if master send restart, we are done
            if stat.slvstate().is_slave_address() {
                break;
            }

            // Verify that we are ready for write
            if !stat.slvstate().is_slave_transmit() {
                return Err(TransferError::WriteFail.into());
            }

            i2c.slvdat().write(|w|
                // SAFETY: unsafe only here due to use of bits()
                unsafe{w.data().bits(*b)});
            i2c.slvctl().write(|w| w.slvcontinue().continue_());
            xfer_count += 1;
        }

        let stat = i2c.stat().read();
        if stat.slvdesel().is_deselected() {
            // clear the deselect bit
            i2c.stat().write(|w| w.slvdesel().deselected());
            // Distinguish Complete (buffer exactly exhausted) vs EarlyStop
            // (buffer had bytes left when controller stopped).
            if xfer_count == buf_len {
                return Ok(InternalTermination::ReadComplete(xfer_count));
            } else {
                return Ok(InternalTermination::ReadEarlyStop(xfer_count));
            }
        } else if stat.slvstate().is_slave_address() {
            // Handle restart after read
            return Ok(InternalTermination::Restarted(xfer_count));
        } else if stat.slvstate().is_slave_transmit() {
            // Buffer exhausted but master still expects bytes — NeedMore.
            debug_assert_eq!(xfer_count, buf_len);
            return Ok(InternalTermination::Continued(xfer_count));
        }

        // We should not get here
        Err(TransferError::WriteFail.into())
    }

    /// Bring the slave back to a known-clean state after a wedged or
    /// cancelled transfer.
    ///
    /// See [`mcu_target::blocking::I2c::recover`] for the contract.
    ///
    /// Performs: NAK any pending byte, disable DMA arming, clear the
    /// deselect latch, drop any pending remediation, and drop any queued
    /// edge bookkeeping. The configured address(es) and `slven` bit are
    /// preserved.
    pub fn recover(&self) -> Result<()> {
        let i2c = self.info.regs;
        critical_section::with(|_| {
            // Drop any latent DMA arming.
            i2c.slvctl().modify(|_r, w| w.slvdma().disabled());
            // Disable interrupts we may have left enabled.
            i2c.intenclr()
                .write(|w| w.slvpendingclr().set_bit().slvdeselclr().set_bit());

            // NAK an in-flight pending byte if any; this is harmless when
            // we are not in the pending state.
            if i2c.stat().read().slvpending().is_pending() {
                i2c.slvctl().write(|w| w.slvnack().set_bit());
            }

            // Clear the deselect latch if set.
            if i2c.stat().read().slvdesel().is_deselected() {
                i2c.stat().write(|w| w.slvdesel().deselected());
            }

            // Drop any pending remediation.
            self.info.remediation.store(REMEDIATON_NONE, Ordering::Release);
        });

        // Drop our software bookkeeping.
        self.pending.set(PendingEdge::default());
        Ok(())
    }
}

// ----- Internal helpers: Async -----------------------------------------------

impl I2cSlave<'_, Async> {
    /// Trait-internal `listen` for the async flavour. Mirrors the inherent
    /// async `listen` but tracks the matched address.
    async fn listen_internal(&mut self) -> Result<InternalEvent> {
        let i2c = self.info.regs;

        // Disable DMA
        i2c.slvctl().write(|w| w.slvdma().disabled());

        // Check whether we already have a matched address and just waiting
        // for software ack/nack
        if !i2c.stat().read().slvpending().is_pending() {
            self.poll_sw_action().await;
        }

        if i2c.stat().read().slvstate().is_slave_address() {
            i2c.slvctl().write(|w| w.slvcontinue().continue_());
        }

        // Poll for HW to transitioning from addressed to receive/transmit
        self.poll_sw_action().await;

        if let Some(ten_bit_address) = self.ten_bit_info {
            // For 10 bit address, the first byte received is the second byte of the address
            if i2c.slvdat().read().data().bits() == ten_bit_address.second_byte {
                i2c.slvctl().write(|w| w.slvcontinue().continue_());
                self.poll_sw_action().await;
            } else {
                // If the second byte of the 10 bit address is not received, then nack the address.
                i2c.slvctl().write(|w| w.slvnack().nack());
                let addr = self.matched_address();
                self.note_match(addr);
                return Ok(InternalEvent::Probe { addr });
            }

            // Check slave is still selected, master has not sent a stop
            if i2c.stat().read().slvsel().is_selected() {
                // Check for a restart
                if i2c.stat().read().slvstate().is_slave_address() {
                    // Check if first byte of 10 bit address is received again with read bit set
                    if i2c.slvdat().read().data().bits() == ten_bit_address.first_byte | 1 {
                        i2c.slvctl().write(|w| w.slvcontinue().continue_());
                        self.poll_sw_action().await;
                    } else {
                        // If the first byte of the 10 bit address is not received again, then nack the address.
                        i2c.slvctl().write(|w| w.slvnack().nack());
                        let addr = self.matched_address();
                        self.note_match(addr);
                        return Ok(InternalEvent::Probe { addr });
                    }
                    // Check slave is ready for transmit
                    if !i2c.stat().read().slvstate().is_slave_transmit() {
                        return Err(TransferError::WriteFail.into());
                    }
                } else {
                    // Check slave is ready to receive
                    if !i2c.stat().read().slvstate().is_slave_receive() {
                        return Err(TransferError::ReadFail.into());
                    }
                }
            }
        }

        // We are deselected, so it must be an 0 byte write transaction
        if i2c.stat().read().slvdesel().is_deselected() {
            // Clear the deselected bit
            i2c.stat().write(|w| w.slvdesel().deselected());
            let addr = self.matched_address();
            self.note_match(addr);
            return Ok(InternalEvent::Probe { addr });
        }

        let state = i2c.stat().read().slvstate().variant();
        let addr = self.matched_address();
        self.note_match(addr);
        match state {
            Some(Slvstate::SlaveReceive) => Ok(InternalEvent::Write { addr }),
            Some(Slvstate::SlaveTransmit) => Ok(InternalEvent::Read { addr }),
            _ => Err(TransferError::OtherBusError.into()),
        }
    }

    /// Trait-internal `respond_to_write` for the async flavour.
    async fn respond_to_write_internal(&mut self, buf: &mut [u8]) -> Result<InternalTermination> {
        let i2c = self.info.regs;
        let buf_len = buf.len();

        // Verify that we are ready for write
        let stat = i2c.stat().read();
        if !stat.slvstate().is_slave_receive() {
            // 0 byte write
            if stat.slvdesel().is_deselected() {
                return Ok(InternalTermination::Stopped(0));
            }
            return Err(TransferError::ReadFail.into());
        }

        let dma_channel = self.dma_ch.as_ref().ok_or(Error::UnsupportedConfiguration)?;

        // Enable DMA
        i2c.slvctl().write(|w| w.slvdma().enabled());

        // Enable interrupt
        i2c.intenset()
            .write(|w| w.slvpendingen().enabled().slvdeselen().enabled());

        let options = dma::transfer::TransferOptions::default();
        let _transfer = dma_channel.read_from_peripheral(i2c.slvdat().as_ptr() as *mut u8, buf, options);

        let nak_guard = NakGuard { info: self.info };
        let _dma_guard = OnDrop::new(|| {
            i2c.slvctl().modify(|_r, w| w.slvdma().disabled());
        });

        poll_fn(|cx| {
            let i2c = self.info.regs;

            self.info.waker.register(cx.waker());
            dma_channel.get_waker().register(cx.waker());

            let stat = i2c.stat().read();
            if stat.slvdesel().is_deselected() {
                return Poll::Ready(());
            }
            if stat.slvpending().is_pending() {
                return Poll::Ready(());
            }
            if !dma_channel.is_active() && stat.slvstate().is_slave_receive() {
                return Poll::Ready(());
            }

            Poll::Pending
        })
        .await;

        nak_guard.defuse();
        let xfer_count = self.abort_dma(buf_len)?;
        let stat = i2c.stat().read();
        if stat.slvdesel().is_deselected() {
            i2c.stat().write(|w| w.slvdesel().deselected());
            return Ok(InternalTermination::Stopped(xfer_count));
        } else if stat.slvstate().is_slave_address() {
            return Ok(InternalTermination::Restarted(xfer_count));
        } else if stat.slvstate().is_slave_receive() {
            return Ok(InternalTermination::Continued(xfer_count));
        }

        Err(TransferError::ReadFail.into())
    }

    /// Trait-internal `respond_to_read` for the async flavour.
    async fn respond_to_read_internal(&mut self, buf: &[u8]) -> Result<InternalTermination> {
        let i2c = self.info.regs;
        let buf_len = buf.len();

        if !i2c.stat().read().slvstate().is_slave_transmit() {
            return Err(TransferError::WriteFail.into());
        }

        i2c.slvctl().write(|w| w.slvdma().enabled());

        i2c.intenset()
            .write(|w| w.slvpendingen().enabled().slvdeselen().enabled());

        let options = dma::transfer::TransferOptions::default();
        let dma_channel = self.dma_ch.as_ref().ok_or(Error::UnsupportedConfiguration)?;

        let _transfer = dma_channel.write_to_peripheral(buf, i2c.slvdat().as_ptr() as *mut u8, options);

        let _dma_guard = OnDrop::new(|| {
            i2c.slvctl().modify(|_r, w| w.slvdma().disabled());
        });

        poll_fn(|cx| {
            let i2c = self.info.regs;

            self.info.waker.register(cx.waker());
            dma_channel.get_waker().register(cx.waker());

            let stat = i2c.stat().read();
            if stat.slvdesel().is_deselected() {
                return Poll::Ready(());
            }
            if stat.slvpending().is_pending() {
                return Poll::Ready(());
            }
            // DMA drained but the master still expects more bytes.
            // Without this guard the future sleeps forever because the
            // hardware does not raise slvpending once DMA is armed and
            // running dry — SDA just floats and the master clocks 0xFF
            // until something else aborts the transaction.
            if !dma_channel.is_active() && stat.slvstate().is_slave_transmit() {
                return Poll::Ready(());
            }

            Poll::Pending
        })
        .await;

        let xfer_count = self.abort_dma(buf_len)?;
        let stat = i2c.stat().read();

        if stat.slvdesel().is_deselected() {
            i2c.stat().write(|w| w.slvdesel().deselected());
            if xfer_count == buf_len {
                return Ok(InternalTermination::ReadComplete(xfer_count));
            } else {
                return Ok(InternalTermination::ReadEarlyStop(xfer_count));
            }
        } else if stat.slvpending().is_pending() || stat.slvstate().is_slave_address() {
            // Restart (or NACK-then-next-address) — surface as Restart so
            // the next `listen` reports the RepeatedStart edge.
            return Ok(InternalTermination::Restarted(xfer_count));
        } else if stat.slvstate().is_slave_transmit() {
            // DMA drained while the master is still clocking — surface
            // NeedMore so the caller can supply another buffer. The
            // caller's next `respond_to_read` call re-arms DMA without
            // dropping the transaction.
            debug_assert_eq!(xfer_count, buf_len);
            return Ok(InternalTermination::Continued(xfer_count));
        }

        Err(TransferError::WriteFail.into())
    }

    /// Bring the slave back to a known-clean state after a wedged or
    /// cancelled transfer.
    ///
    /// See [`mcu_target::asynch::I2c::recover`] for the contract.
    ///
    /// Aborts any in-flight DMA, NAKs any pending byte, disables DMA
    /// arming, clears the deselect latch, drops any pending remediation,
    /// and clears any queued edge bookkeeping. The configured address(es)
    /// and `slven` bit are preserved. The async flavour additionally awaits
    /// completion of the remediation pump so the returned future is the
    /// canonical join point.
    pub async fn recover(&mut self) -> Result<()> {
        let i2c = self.info.regs;
        if let Some(dma) = self.dma_ch.as_ref()
            && dma.is_active()
        {
            dma.abort();
        }

        critical_section::with(|_| {
            i2c.slvctl().modify(|_r, w| w.slvdma().disabled());
            i2c.intenclr()
                .write(|w| w.slvpendingclr().set_bit().slvdeselclr().set_bit());

            if i2c.stat().read().slvpending().is_pending() {
                i2c.slvctl().write(|w| w.slvnack().set_bit());
            }
            if i2c.stat().read().slvdesel().is_deselected() {
                i2c.stat().write(|w| w.slvdesel().deselected());
            }
            self.info.remediation.store(REMEDIATON_NONE, Ordering::Release);
        });

        self.pending.set(PendingEdge::default());
        Ok(())
    }
}

// ----- Error / ErrorType impls -----------------------------------------------

impl mcu_target::Error for Error {
    fn kind(&self) -> mcu_target::ErrorKind {
        match *self {
            Self::UnsupportedConfiguration => mcu_target::ErrorKind::Other,
            Self::Transfer(e) => match e {
                TransferError::Timeout => mcu_target::ErrorKind::Other,
                TransferError::ReadFail | TransferError::WriteFail => {
                    mcu_target::ErrorKind::NoAcknowledge(mcu_target::NoAcknowledgeSource::Data)
                }
                TransferError::AddressNack => {
                    mcu_target::ErrorKind::NoAcknowledge(mcu_target::NoAcknowledgeSource::Address)
                }
                TransferError::ArbitrationLoss => mcu_target::ErrorKind::ArbitrationLoss,
                TransferError::StartStopError | TransferError::OtherBusError => mcu_target::ErrorKind::Bus,
            },
        }
    }
}

impl<M: Mode> mcu_target::ErrorType for I2cSlave<'_, M> {
    type Error = Error;
}

// ----- Blocking I2c<SevenBitAddress> impl ------------------------------------

impl mcu_target::blocking::I2c<SevenBitAddress> for I2cSlave<'_, Blocking> {
    fn recover(&mut self) -> Result<()> {
        self.recover()
    }

    fn listen(&mut self) -> Result<mcu_target::Request<SevenBitAddress>> {
        self.require_address_kind(false)?;

        // Drain any queued edge first.
        if let Some(req) = self.drain_edge::<SevenBitAddress>(|a| a.as_u8().unwrap_or(0)) {
            return Ok(req);
        }

        let ev = self.listen_internal()?;
        Ok(match ev {
            InternalEvent::Probe { addr } => mcu_target::Request::Stop(addr.as_u8().unwrap_or(0)),
            InternalEvent::Read { addr } => mcu_target::Request::Read(addr.as_u8().unwrap_or(0)),
            InternalEvent::Write { addr } => mcu_target::Request::Write(addr.as_u8().unwrap_or(0)),
        })
    }

    fn respond_to_read(&mut self, buf: &[u8]) -> Result<mcu_target::ReadStatus> {
        let term = self.respond_to_read_internal(buf)?;
        Ok(read_termination_to_status(self, term))
    }

    fn respond_to_write(&mut self, buf: &mut [u8]) -> Result<mcu_target::WriteStatus> {
        let term = self.respond_to_write_internal(buf)?;
        Ok(write_termination_to_status(self, term))
    }
}

// ----- Blocking I2c<TenBitAddress> impl --------------------------------------

impl mcu_target::blocking::I2c<TenBitAddress> for I2cSlave<'_, Blocking> {
    fn recover(&mut self) -> Result<()> {
        self.recover()
    }

    fn listen(&mut self) -> Result<mcu_target::Request<TenBitAddress>> {
        self.require_address_kind(true)?;

        if let Some(req) = self.drain_edge::<TenBitAddress>(|a| a.as_u16()) {
            return Ok(req);
        }

        let ev = self.listen_internal()?;
        Ok(match ev {
            InternalEvent::Probe { addr } => mcu_target::Request::Stop(addr.as_u16()),
            InternalEvent::Read { addr } => mcu_target::Request::Read(addr.as_u16()),
            InternalEvent::Write { addr } => mcu_target::Request::Write(addr.as_u16()),
        })
    }

    fn respond_to_read(&mut self, buf: &[u8]) -> Result<mcu_target::ReadStatus> {
        let term = self.respond_to_read_internal(buf)?;
        Ok(read_termination_to_status(self, term))
    }

    fn respond_to_write(&mut self, buf: &mut [u8]) -> Result<mcu_target::WriteStatus> {
        let term = self.respond_to_write_internal(buf)?;
        Ok(write_termination_to_status(self, term))
    }
}

// ----- Async I2c<SevenBitAddress> impl ---------------------------------------

impl mcu_target::asynch::I2c<SevenBitAddress> for I2cSlave<'_, Async> {
    async fn recover(&mut self) -> Result<()> {
        self.recover().await
    }

    async fn listen(&mut self) -> Result<mcu_target::Request<SevenBitAddress>> {
        self.require_address_kind(false)?;

        if let Some(req) = self.drain_edge::<SevenBitAddress>(|a| a.as_u8().unwrap_or(0)) {
            return Ok(req);
        }

        let ev = self.listen_internal().await?;
        Ok(match ev {
            InternalEvent::Probe { addr } => mcu_target::Request::Stop(addr.as_u8().unwrap_or(0)),
            InternalEvent::Read { addr } => mcu_target::Request::Read(addr.as_u8().unwrap_or(0)),
            InternalEvent::Write { addr } => mcu_target::Request::Write(addr.as_u8().unwrap_or(0)),
        })
    }

    async fn respond_to_read(&mut self, buf: &[u8]) -> Result<mcu_target::ReadStatus> {
        let term = self.respond_to_read_internal(buf).await?;
        Ok(read_termination_to_status(self, term))
    }

    async fn respond_to_write(&mut self, buf: &mut [u8]) -> Result<mcu_target::WriteStatus> {
        let term = self.respond_to_write_internal(buf).await?;
        Ok(write_termination_to_status(self, term))
    }
}

// ----- Async I2c<TenBitAddress> impl -----------------------------------------

impl mcu_target::asynch::I2c<TenBitAddress> for I2cSlave<'_, Async> {
    async fn recover(&mut self) -> Result<()> {
        self.recover(self).await
    }

    async fn listen(&mut self) -> Result<mcu_target::Request<TenBitAddress>> {
        self.require_address_kind(true)?;

        if let Some(req) = self.drain_edge::<TenBitAddress>(|a| a.as_u16()) {
            return Ok(req);
        }

        let ev = self.listen_internal().await?;
        Ok(match ev {
            InternalEvent::Probe { addr } => mcu_target::Request::Stop(addr.as_u16()),
            InternalEvent::Read { addr } => mcu_target::Request::Read(addr.as_u16()),
            InternalEvent::Write { addr } => mcu_target::Request::Write(addr.as_u16()),
        })
    }

    async fn respond_to_read(&mut self, buf: &[u8]) -> Result<mcu_target::ReadStatus> {
        let term = self.respond_to_read_internal(buf).await?;
        Ok(read_termination_to_status(self, term))
    }

    async fn respond_to_write(&mut self, buf: &mut [u8]) -> Result<mcu_target::WriteStatus> {
        let term = self.respond_to_write_internal(buf).await?;
        Ok(write_termination_to_status(self, term))
    }
}

#[cfg(test)]
mod tests {
    use embedded_mcu_hal::i2c::target::{ErrorKind, NoAcknowledgeSource};

    use super::*;

    #[test]
    fn error_kind_mapping_covers_every_transfer_variant() {
        // Every TransferError variant must map to a deterministic ErrorKind.
        let cases = [
            (TransferError::Timeout, ErrorKind::Other),
            (
                TransferError::ReadFail,
                ErrorKind::NoAcknowledge(NoAcknowledgeSource::Data),
            ),
            (
                TransferError::WriteFail,
                ErrorKind::NoAcknowledge(NoAcknowledgeSource::Data),
            ),
            (
                TransferError::AddressNack,
                ErrorKind::NoAcknowledge(NoAcknowledgeSource::Address),
            ),
            (TransferError::ArbitrationLoss, ErrorKind::ArbitrationLoss),
            (TransferError::StartStopError, ErrorKind::Bus),
            (TransferError::OtherBusError, ErrorKind::Bus),
        ];

        for (transfer, expected) in cases {
            let err = Error::Transfer(transfer);
            assert_eq!(<Error as embedded_mcu_hal::i2c::target::Error>::kind(&err), expected);
        }
    }

    #[test]
    fn error_kind_mapping_unsupported_configuration_is_other() {
        let err = Error::UnsupportedConfiguration;
        assert_eq!(
            <Error as embedded_mcu_hal::i2c::target::Error>::kind(&err),
            ErrorKind::Other,
        );
    }

    #[test]
    fn address_kind_round_trips() {
        let seven = AddressKind::Seven(0x42);
        assert_eq!(seven.as_u8(), Some(0x42));
        assert_eq!(seven.as_u16(), 0x42);

        let ten = AddressKind::Ten(0x1AB);
        assert_eq!(ten.as_u8(), None);
        assert_eq!(ten.as_u16(), 0x1AB);
    }
}
