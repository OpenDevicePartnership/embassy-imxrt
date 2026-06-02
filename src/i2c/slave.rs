//! Implements I2C function support over flexcomm + gpios
//!
//! # Inherent API
//!
//! The [`I2cSlave`] driver exposes a small inherent API:
//!
//! - [`I2cSlave::listen`] — wait for the next [`Command`] from the
//!   controller. The variant carries the matched [`Address`].
//! - [`I2cSlave::respond_to_write`] — drain incoming bytes for a Write.
//! - [`I2cSlave::respond_to_read`] — supply outgoing bytes for a Read.
//! - [`I2cSlave::recover`] — re-baseline the peripheral after a wedged
//!   or cancelled transfer.
//!
//! Both `respond_to_*` calls return a [`Response`] that describes how the
//! transaction terminated. The variants distinguish stop, repeated start,
//! buffer exhaustion, and read-side early-stop, so callers can react
//! precisely instead of papering over the difference. The convenience
//! helpers [`Response::bytes`] and [`Response::is_terminal`] handle the
//! common "I just want the count and whether to loop" case.
//!
//! Probes (zero-byte writes — the controller sends `ADDR+W` and
//! immediately STOPs) surface as [`Command::Probe`] with the matched
//! address attached; there is no following `respond_to_write` call.
//!
//! # Target trait impls
//!
//! Besides the inherent API, this driver also implements the
//! [`embedded_mcu_hal::i2c::target`] traits:
//!
//! - [`embedded_mcu_hal::i2c::target::blocking::I2c`] for
//!   `I2cSlave<'_, Blocking>`
//! - [`embedded_mcu_hal::i2c::target::asynch::I2c`] for
//!   `I2cSlave<'_, Async>`
//!
//! Both flavours are implemented twice — once for `SevenBitAddress` and
//! once for `TenBitAddress`. The implementation that matches the address
//! mode configured at construction time succeeds; the mismatched
//! implementation returns [`Error::UnsupportedConfiguration`], which maps
//! to [`ErrorKind::Other`](embedded_mcu_hal::i2c::target::ErrorKind::Other).
//!
//! The trait API additionally surfaces a repeated-START as its own
//! [`Request::RepeatedStart`](embedded_mcu_hal::i2c::target::Request::RepeatedStart)
//! event on the next `listen` call. The inherent API folds restarts into
//! the preceding [`Response::Restarted`] instead — the next inherent
//! `listen` resumes hardware polling and reports the new direction
//! directly.

use core::cell::Cell;
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
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
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

/// Command observed by the slave on the I2C bus.
///
/// Returned by [`I2cSlave::listen`]. Each variant carries the [`Address`]
/// that matched on the wire so applications with multiple register files
/// or address aliases can dispatch on it.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Command {
    /// A probe: the controller sent `ADDR+W` and immediately followed
    /// with `STOP` (or with the second 10-bit address byte mismatching).
    /// No `respond_to_*` call is required. The carried [`Address`] is the
    /// configured address that matched.
    Probe {
        /// Address that was matched.
        addr: Address,
    },
    /// Controller is about to read from this target. Service it with
    /// [`I2cSlave::respond_to_read`].
    Read {
        /// Address that was matched.
        addr: Address,
    },
    /// Controller is about to write to this target. Service it with
    /// [`I2cSlave::respond_to_write`].
    Write {
        /// Address that was matched.
        addr: Address,
    },
}

/// Outcome of a [`I2cSlave::respond_to_read`] or
/// [`I2cSlave::respond_to_write`] call.
///
/// The variants distinguish every observable termination reason so callers
/// can decide between continuing with a fresh buffer, looping back to
/// [`I2cSlave::listen`] for the next event, or returning to the
/// application loop. The convenience helpers [`Response::bytes`] and
/// [`Response::is_terminal`] cover the "just give me the count and tell
/// me if we're done" case without forcing every call site to match on all
/// six variants.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Response {
    /// Controller issued `STOP`. The transaction is complete. `n` is the
    /// number of bytes moved.
    Stopped(usize),
    /// Controller issued a repeated `START` (`Sr`). The transaction is
    /// complete from this `respond_*` call's perspective; the next
    /// [`I2cSlave::listen`] will report the new direction. `n` is the
    /// number of bytes moved before the restart.
    Restarted(usize),
    /// Write side: the supplied buffer was filled before the controller
    /// terminated the transfer. Call [`I2cSlave::respond_to_write`] again
    /// with another buffer to continue draining. `n` equals the buffer
    /// length.
    WriteContinued(usize),
    /// Read side: the supplied buffer was fully consumed but the
    /// controller is still clocking more bytes. Call
    /// [`I2cSlave::respond_to_read`] again with another buffer to continue
    /// supplying data. `n` equals the buffer length.
    ReadContinued(usize),
    /// Read side: the supplied buffer was fully consumed at exactly the
    /// moment the controller NACKed and stopped. `n` equals the buffer
    /// length.
    ReadComplete(usize),
    /// Read side: the controller stopped (or restarted) before the
    /// supplied buffer was drained. `n` is the number of bytes the
    /// controller clocked out.
    ReadEarlyStop(usize),
}

impl Response {
    /// Number of bytes moved on the wire during the call that produced
    /// this response.
    #[must_use]
    pub const fn bytes(self) -> usize {
        match self {
            Self::Stopped(n)
            | Self::Restarted(n)
            | Self::WriteContinued(n)
            | Self::ReadContinued(n)
            | Self::ReadComplete(n)
            | Self::ReadEarlyStop(n) => n,
        }
    }

    /// Whether the transaction is complete from the slave's perspective.
    ///
    /// Returns `true` for [`Stopped`], [`Restarted`], [`ReadComplete`],
    /// and [`ReadEarlyStop`]; `false` for [`WriteContinued`] and
    /// [`ReadContinued`], which indicate the caller should supply another
    /// buffer to continue the in-flight transaction.
    ///
    /// [`Stopped`]: Self::Stopped
    /// [`Restarted`]: Self::Restarted
    /// [`ReadComplete`]: Self::ReadComplete
    /// [`ReadEarlyStop`]: Self::ReadEarlyStop
    /// [`WriteContinued`]: Self::WriteContinued
    /// [`ReadContinued`]: Self::ReadContinued
    #[must_use]
    pub const fn is_terminal(self) -> bool {
        match self {
            Self::Stopped(_) | Self::Restarted(_) | Self::ReadComplete(_) | Self::ReadEarlyStop(_) => true,
            Self::WriteContinued(_) | Self::ReadContinued(_) => false,
        }
    }
}

/// Edge event queued by a previous `respond_to_*` for the next trait-level
/// `listen` call.
///
/// Only used by the target trait impls — the inherent `listen` ignores
/// this field because it folds the restart edge into the preceding
/// [`Response::Restarted`] instead.
#[derive(Copy, Clone, Debug)]
enum EdgeKind {
    /// Surface a
    /// [`Request::RepeatedStart`](mcu_target::Request::RepeatedStart) at
    /// the next trait `listen`, then resume hardware polling for the next
    /// addressed event.
    RepeatedStart,
}

/// Per-driver pending-edge bookkeeping for the target trait impls.
///
/// Tracks the address that matched on the most recent addressed event
/// (for the trait's `Request<A>` payload) and any restart edge that
/// should be surfaced before the next hardware poll. The inherent API
/// never reads this state.
#[derive(Copy, Clone, Debug, Default)]
struct PendingEdge {
    last_addr: Option<Address>,
    pending: Option<EdgeKind>,
}

/// use `FCn` as I2C Slave controller
pub struct I2cSlave<'a, M: Mode> {
    info: Info,
    _flexcomm: FlexcommRef,
    _phantom: PhantomData<M>,
    dma_ch: Option<dma::channel::Channel<'a>>,
    ten_bit_info: Option<TenBitAddressInfo>,
    /// Address configured at construction time. Carried verbatim on every
    /// [`Command`] returned by [`I2cSlave::listen`] and used by the
    /// target trait impls to populate the `A` payload on
    /// [`Request`](mcu_target::Request) and to enforce the runtime
    /// address-mode check.
    configured_address: Address,
    /// Pending-edge bookkeeping for the target trait impls. Set by
    /// [`I2cSlave::respond_to_write`] / [`I2cSlave::respond_to_read`]
    /// when they observe a repeated-START terminator; drained by the
    /// trait `listen` wrapper. The inherent `listen` does not touch this
    /// field.
    pending: Cell<PendingEdge>,
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
            pending: Cell::new(PendingEdge::default()),
        })
    }

    /// Record the address that just matched on the bus. Set by every
    /// successful `listen` so subsequent trait-level edge surfacing
    /// (`RepeatedStart`) can attach the right address.
    fn note_match(&self, addr: Address) {
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
    fn drain_edge<A>(&self, addr_for: fn(Address) -> A) -> Option<mcu_target::Request<A>>
    where
        A: embedded_hal_1::i2c::AddressMode,
    {
        let mut p = self.pending.get();
        let edge = p.pending.take()?;
        let addr = p.last_addr.unwrap_or(self.configured_address);
        self.pending.set(p);
        Some(match edge {
            EdgeKind::RepeatedStart => mcu_target::Request::RepeatedStart(addr_for(addr)),
        })
    }

    /// Address-mode runtime guard. Returns
    /// `Err(UnsupportedConfiguration)` when the trait impl being driven
    /// does not match the address type the slave was constructed with.
    fn require_address_kind(&self, want_ten_bit: bool) -> Result<()> {
        let is_ten_bit = self.ten_bit_info.is_some();
        if is_ten_bit == want_ten_bit {
            Ok(())
        } else {
            Err(Error::UnsupportedConfiguration)
        }
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
    /// Listen for the next [`Command`] from the I2C controller.
    ///
    /// Blocks until the bus produces an addressed event for this target.
    /// The returned [`Command`] carries the matched [`Address`].
    pub fn listen(&self) -> Result<Command> {
        let i2c = self.info.regs;
        let addr = self.configured_address;

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
                self.note_match(addr);
                return Ok(Command::Probe { addr });
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
                        self.note_match(addr);
                        return Ok(Command::Probe { addr });
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
            self.note_match(addr);
            return Ok(Command::Probe { addr });
        }

        let state = i2c.stat().read().slvstate().variant();
        self.note_match(addr);
        match state {
            Some(Slvstate::SlaveReceive) => Ok(Command::Write { addr }),
            Some(Slvstate::SlaveTransmit) => Ok(Command::Read { addr }),
            _ => Err(TransferError::OtherBusError.into()),
        }
    }

    /// Drain incoming bytes for a [`Command::Write`].
    ///
    /// Fills the supplied buffer in order. Returns when the controller
    /// terminates the transfer (stop, repeated start) or when the buffer
    /// is full.
    pub fn respond_to_write(&self, buf: &mut [u8]) -> Result<Response> {
        let i2c = self.info.regs;
        let buf_len = buf.len();
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
            return Ok(Response::Stopped(xfer_count));
        } else if stat.slvstate().is_slave_address() {
            // Handle restart — record the edge for any trait caller; the
            // inherent `listen` will see the slave-address state directly
            // on its next call.
            self.queue_edge(EdgeKind::RepeatedStart);
            return Ok(Response::Restarted(xfer_count));
        } else if stat.slvstate().is_slave_receive() {
            // Buffer exhausted; controller is still sending — caller
            // should supply another buffer to continue draining.
            debug_assert_eq!(xfer_count, buf_len);
            return Ok(Response::WriteContinued(xfer_count));
        }

        // We should not get here
        Err(TransferError::ReadFail.into())
    }

    /// Supply outgoing bytes for a [`Command::Read`].
    ///
    /// Sends bytes from the supplied buffer in order. Returns when the
    /// controller terminates the transfer (NACK+stop, repeated start) or
    /// when the buffer is exhausted.
    pub fn respond_to_read(&self, buf: &[u8]) -> Result<Response> {
        let i2c = self.info.regs;
        let buf_len = buf.len();
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
            // Distinguish ReadComplete (buffer exactly exhausted at
            // NACK+STOP) from ReadEarlyStop (controller stopped with
            // bytes still in the buffer).
            if xfer_count == buf_len {
                return Ok(Response::ReadComplete(xfer_count));
            } else {
                return Ok(Response::ReadEarlyStop(xfer_count));
            }
        } else if stat.slvstate().is_slave_address() {
            // Handle restart after read — queue the edge for any trait
            // caller and report the restart to the inherent caller.
            self.queue_edge(EdgeKind::RepeatedStart);
            return Ok(Response::Restarted(xfer_count));
        } else if stat.slvstate().is_slave_transmit() {
            // Buffer exhausted but master still expects bytes — caller
            // should supply another buffer to continue.
            debug_assert_eq!(xfer_count, buf_len);
            return Ok(Response::ReadContinued(xfer_count));
        }

        // We should not get here
        Err(TransferError::WriteFail.into())
    }

    /// Bring the slave back to a known-clean state after a wedged
    /// transfer or an internally cancelled transaction.
    ///
    /// Disables DMA arming, NAKs any pending byte, clears the deselect
    /// latch, drops any pending remediation flag, and clears the queued
    /// edge bookkeeping. The configured address(es) and `slven` bit are
    /// preserved — the next [`I2cSlave::listen`] will accept a fresh
    /// transaction without re-initialising the driver.
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

impl I2cSlave<'_, Async> {
    /// Listen for the next [`Command`] from the I2C controller, asynchronously.
    ///
    /// The returned future resolves when the bus produces an addressed
    /// event for this target. The [`Command`] carries the matched
    /// [`Address`].
    pub async fn listen(&mut self) -> Result<Command> {
        let i2c = self.info.regs;
        let addr = self.configured_address;

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
                self.note_match(addr);
                return Ok(Command::Probe { addr });
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
                        self.note_match(addr);
                        return Ok(Command::Probe { addr });
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
            self.note_match(addr);
            return Ok(Command::Probe { addr });
        }

        let state = i2c.stat().read().slvstate().variant();
        self.note_match(addr);
        match state {
            Some(Slvstate::SlaveReceive) => Ok(Command::Write { addr }),
            Some(Slvstate::SlaveTransmit) => Ok(Command::Read { addr }),
            _ => Err(TransferError::OtherBusError.into()),
        }
    }

    /// Drain incoming bytes for a [`Command::Write`], asynchronously.
    ///
    /// DMA-driven. Fills the supplied buffer in order. Returns when the
    /// controller terminates the transfer (stop, repeated start) or when
    /// the buffer is full.
    pub async fn respond_to_write(&mut self, buf: &mut [u8]) -> Result<Response> {
        let i2c = self.info.regs;
        let buf_len = buf.len();

        // Verify that we are ready for write
        let stat = i2c.stat().read();
        if !stat.slvstate().is_slave_receive() {
            // 0 byte write
            if stat.slvdesel().is_deselected() {
                return Ok(Response::Stopped(0));
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
        if stat.slvdesel().is_deselected() {
            // Clear the deselected bit
            i2c.stat().write(|w| w.slvdesel().deselected());
            return Ok(Response::Stopped(xfer_count));
        } else if stat.slvstate().is_slave_address() {
            // Restart — queue the edge for any trait caller.
            self.queue_edge(EdgeKind::RepeatedStart);
            return Ok(Response::Restarted(xfer_count));
        } else if stat.slvstate().is_slave_receive() {
            // Buffer was filled before the controller terminated; caller
            // should supply another buffer to continue.
            return Ok(Response::WriteContinued(xfer_count));
        }

        Err(TransferError::ReadFail.into())
    }

    /// Supply outgoing bytes for a [`Command::Read`], asynchronously.
    ///
    /// DMA-driven. Sends bytes from the supplied buffer in order. Returns
    /// when the controller terminates the transfer (NACK+stop, repeated
    /// start) or when the buffer is exhausted.
    pub async fn respond_to_read(&mut self, buf: &[u8]) -> Result<Response> {
        let i2c = self.info.regs;
        let buf_len = buf.len();

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

        // Complete DMA transaction and get transfer count
        let xfer_count = self.abort_dma(buf_len)?;
        let stat = i2c.stat().read();

        if stat.slvdesel().is_deselected() {
            // clear the deselect bit
            i2c.stat().write(|w| w.slvdesel().deselected());
            // Distinguish ReadComplete (buffer exactly exhausted) from
            // ReadEarlyStop (controller stopped with bytes still in the
            // buffer).
            if xfer_count == buf_len {
                return Ok(Response::ReadComplete(xfer_count));
            } else {
                return Ok(Response::ReadEarlyStop(xfer_count));
            }
        } else if stat.slvpending().is_pending() || stat.slvstate().is_slave_address() {
            // Restart (or NACK-then-next-address) — queue the edge for
            // any trait caller and report the restart to the inherent
            // caller.
            self.queue_edge(EdgeKind::RepeatedStart);
            return Ok(Response::Restarted(xfer_count));
        } else if stat.slvstate().is_slave_transmit() {
            // DMA drained while the master is still clocking — caller
            // should supply another buffer to continue.
            debug_assert_eq!(xfer_count, buf_len);
            return Ok(Response::ReadContinued(xfer_count));
        }

        Err(TransferError::WriteFail.into())
    }

    /// Bring the slave back to a known-clean state after a wedged or
    /// cancelled transfer.
    ///
    /// Aborts any in-flight DMA, NAKs any pending byte, disables DMA
    /// arming, clears the deselect latch, drops any pending remediation,
    /// and clears any queued edge bookkeeping. The configured address(es)
    /// and `slven` bit are preserved.
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
// The traits layer on top of the inherent API: each trait method calls
// the inherent method and maps the result into the corresponding trait
// shape. The address-mode generic is handled by writing two separate
// trait impl blocks per flavour (one for `SevenBitAddress`, one for
// `TenBitAddress`); at runtime the impl checks the address type
// configured at construction time and returns `ErrorKind::Other` from
// `listen` if the wrong impl was invoked.
//
// The single piece of state that exists *only* for the trait is the
// `pending: Cell<PendingEdge>` field on `I2cSlave`: it carries a
// `RepeatedStart` edge from a previous `respond_to_*` to the next trait
// `listen` call, so the trait surfaces `Request::RepeatedStart` as its
// own event rather than folding it into the preceding response. The
// inherent API never reads this field.

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

/// Map the address from a [`Command`] to the trait-side `u8` payload
/// (used by the `SevenBitAddress` impls). Returns `0` for the
/// impossible-here `TenBit` case — the address-mode guard in the impl
/// rejects mismatched callers before we ever reach this mapping.
fn cmd_addr_u8(addr: Address) -> u8 {
    match addr {
        Address::SevenBit(a) => a,
        Address::TenBit(_) => 0,
    }
}

/// Map the address from a [`Command`] to the trait-side `u16` payload
/// (used by the `TenBitAddress` impls). 7-bit addresses widen losslessly.
fn cmd_addr_u16(addr: Address) -> u16 {
    match addr {
        Address::SevenBit(a) => a as u16,
        Address::TenBit(a) => a,
    }
}

/// Map a [`Command`] to a [`mcu_target::Request<u8>`].
fn cmd_to_request_u8(cmd: Command) -> mcu_target::Request<u8> {
    match cmd {
        Command::Probe { addr } => mcu_target::Request::Stop(cmd_addr_u8(addr)),
        Command::Read { addr } => mcu_target::Request::Read(cmd_addr_u8(addr)),
        Command::Write { addr } => mcu_target::Request::Write(cmd_addr_u8(addr)),
    }
}

/// Map a [`Command`] to a [`mcu_target::Request<u16>`].
fn cmd_to_request_u16(cmd: Command) -> mcu_target::Request<u16> {
    match cmd {
        Command::Probe { addr } => mcu_target::Request::Stop(cmd_addr_u16(addr)),
        Command::Read { addr } => mcu_target::Request::Read(cmd_addr_u16(addr)),
        Command::Write { addr } => mcu_target::Request::Write(cmd_addr_u16(addr)),
    }
}

/// Map a [`Response`] returned by `respond_to_write` to the trait-side
/// [`mcu_target::WriteStatus`].
fn resp_to_write_status(r: Response) -> mcu_target::WriteStatus {
    match r {
        Response::Stopped(n) => mcu_target::WriteStatus::Stopped(n),
        Response::Restarted(n) => mcu_target::WriteStatus::Restarted(n),
        Response::WriteContinued(n) => mcu_target::WriteStatus::BufferFull(n),
        // Read-only terminators should never come out of respond_to_write;
        // fall back to Stopped to keep the trait surface total.
        Response::ReadContinued(n) | Response::ReadComplete(n) | Response::ReadEarlyStop(n) => {
            mcu_target::WriteStatus::Stopped(n)
        }
    }
}

/// Map a [`Response`] returned by `respond_to_read` to the trait-side
/// [`mcu_target::ReadStatus`].
fn resp_to_read_status(r: Response) -> mcu_target::ReadStatus {
    match r {
        Response::ReadComplete(n) => mcu_target::ReadStatus::Complete(n),
        Response::ReadContinued(n) => mcu_target::ReadStatus::NeedMore(n),
        Response::ReadEarlyStop(n) | Response::Restarted(n) | Response::Stopped(n) => {
            mcu_target::ReadStatus::EarlyStop(n)
        }
        // Write-only terminator — should never come out of respond_to_read.
        Response::WriteContinued(n) => mcu_target::ReadStatus::EarlyStop(n),
    }
}

// ----- Blocking I2c<SevenBitAddress> impl ------------------------------------

impl mcu_target::blocking::I2c<SevenBitAddress> for I2cSlave<'_, Blocking> {
    fn recover(&mut self) -> Result<()> {
        I2cSlave::<Blocking>::recover(self)
    }

    fn listen(&mut self) -> Result<mcu_target::Request<SevenBitAddress>> {
        self.require_address_kind(false)?;

        // Drain any queued edge first.
        if let Some(req) = self.drain_edge::<SevenBitAddress>(cmd_addr_u8) {
            return Ok(req);
        }

        Ok(cmd_to_request_u8(I2cSlave::<Blocking>::listen(self)?))
    }

    fn respond_to_read(&mut self, buf: &[u8]) -> Result<mcu_target::ReadStatus> {
        Ok(resp_to_read_status(I2cSlave::<Blocking>::respond_to_read(self, buf)?))
    }

    fn respond_to_write(&mut self, buf: &mut [u8]) -> Result<mcu_target::WriteStatus> {
        Ok(resp_to_write_status(I2cSlave::<Blocking>::respond_to_write(self, buf)?))
    }
}

// ----- Blocking I2c<TenBitAddress> impl --------------------------------------

impl mcu_target::blocking::I2c<TenBitAddress> for I2cSlave<'_, Blocking> {
    fn recover(&mut self) -> Result<()> {
        I2cSlave::<Blocking>::recover(self)
    }

    fn listen(&mut self) -> Result<mcu_target::Request<TenBitAddress>> {
        self.require_address_kind(true)?;

        if let Some(req) = self.drain_edge::<TenBitAddress>(cmd_addr_u16) {
            return Ok(req);
        }

        Ok(cmd_to_request_u16(I2cSlave::<Blocking>::listen(self)?))
    }

    fn respond_to_read(&mut self, buf: &[u8]) -> Result<mcu_target::ReadStatus> {
        Ok(resp_to_read_status(I2cSlave::<Blocking>::respond_to_read(self, buf)?))
    }

    fn respond_to_write(&mut self, buf: &mut [u8]) -> Result<mcu_target::WriteStatus> {
        Ok(resp_to_write_status(I2cSlave::<Blocking>::respond_to_write(self, buf)?))
    }
}

// ----- Async I2c<SevenBitAddress> impl ---------------------------------------

impl mcu_target::asynch::I2c<SevenBitAddress> for I2cSlave<'_, Async> {
    async fn recover(&mut self) -> Result<()> {
        I2cSlave::<Async>::recover(self).await
    }

    async fn listen(&mut self) -> Result<mcu_target::Request<SevenBitAddress>> {
        self.require_address_kind(false)?;

        if let Some(req) = self.drain_edge::<SevenBitAddress>(cmd_addr_u8) {
            return Ok(req);
        }

        Ok(cmd_to_request_u8(I2cSlave::<Async>::listen(self).await?))
    }

    async fn respond_to_read(&mut self, buf: &[u8]) -> Result<mcu_target::ReadStatus> {
        Ok(resp_to_read_status(
            I2cSlave::<Async>::respond_to_read(self, buf).await?,
        ))
    }

    async fn respond_to_write(&mut self, buf: &mut [u8]) -> Result<mcu_target::WriteStatus> {
        Ok(resp_to_write_status(
            I2cSlave::<Async>::respond_to_write(self, buf).await?,
        ))
    }
}

// ----- Async I2c<TenBitAddress> impl -----------------------------------------

impl mcu_target::asynch::I2c<TenBitAddress> for I2cSlave<'_, Async> {
    async fn recover(&mut self) -> Result<()> {
        I2cSlave::<Async>::recover(self).await
    }

    async fn listen(&mut self) -> Result<mcu_target::Request<TenBitAddress>> {
        self.require_address_kind(true)?;

        if let Some(req) = self.drain_edge::<TenBitAddress>(cmd_addr_u16) {
            return Ok(req);
        }

        Ok(cmd_to_request_u16(I2cSlave::<Async>::listen(self).await?))
    }

    async fn respond_to_read(&mut self, buf: &[u8]) -> Result<mcu_target::ReadStatus> {
        Ok(resp_to_read_status(
            I2cSlave::<Async>::respond_to_read(self, buf).await?,
        ))
    }

    async fn respond_to_write(&mut self, buf: &mut [u8]) -> Result<mcu_target::WriteStatus> {
        Ok(resp_to_write_status(
            I2cSlave::<Async>::respond_to_write(self, buf).await?,
        ))
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
    fn response_bytes_returns_payload_for_every_variant() {
        assert_eq!(Response::Stopped(3).bytes(), 3);
        assert_eq!(Response::Restarted(5).bytes(), 5);
        assert_eq!(Response::WriteContinued(8).bytes(), 8);
        assert_eq!(Response::ReadContinued(8).bytes(), 8);
        assert_eq!(Response::ReadComplete(7).bytes(), 7);
        assert_eq!(Response::ReadEarlyStop(2).bytes(), 2);
    }

    #[test]
    fn response_is_terminal_distinguishes_continuation_from_completion() {
        assert!(Response::Stopped(0).is_terminal());
        assert!(Response::Restarted(0).is_terminal());
        assert!(Response::ReadComplete(0).is_terminal());
        assert!(Response::ReadEarlyStop(0).is_terminal());
        assert!(!Response::WriteContinued(0).is_terminal());
        assert!(!Response::ReadContinued(0).is_terminal());
    }

    #[test]
    fn cmd_addr_widens_seven_bit_losslessly() {
        let addr = Address::SevenBit(0x42);
        assert_eq!(cmd_addr_u8(addr), 0x42);
        assert_eq!(cmd_addr_u16(addr), 0x42);
    }

    #[test]
    fn cmd_addr_u16_passes_through_ten_bit() {
        let addr = Address::TenBit(0x1AB);
        assert_eq!(cmd_addr_u16(addr), 0x1AB);
    }
}
