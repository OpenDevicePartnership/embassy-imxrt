//! Implements I2C function support over flexcomm + gpios

use core::future::poll_fn;
use core::marker::PhantomData;
use core::sync::atomic::Ordering;
use core::task::Poll;

use embassy_hal_internal::drop::OnDrop;
use embassy_hal_internal::Peri;

use super::{
    Info, Instance, InterruptHandler, Result, SclPin, SdaPin, SlaveDma, TransferError, I2C_REMEDIATION, I2C_WAKERS,
    REMEDIATON_NONE, REMEDIATON_SLAVE_NAK, TEN_BIT_PREFIX,
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
    selected: bool,
}

impl TenBitAddressInfo {
    fn new(address: u16) -> Self {
        Self {
            first_byte: (((address >> 8) as u8) << 1) | TEN_BIT_PREFIX,
            second_byte: (address & 0xFF) as u8,
            selected: false,
        }
    }
}

/// An I2c transaction received from `listen`
pub enum Transaction<R, W> {
    /// A stop or restart with different address happened since the last
    /// transaction. This may be emitted multiple times between transactions
    Deselect,
    /// An i2c read transaction (data read by master from the slave)
    Read {
        /// Address for which the read was received
        address: Address,
        /// Handler to be used in handling the transaction
        ///
        /// Dropping this handler nacks the address. Any other interaction
        /// acknowledges the address.
        handler: R,
    },
    /// An i2c write transaction (data written by master to the slave)
    Write {
        /// Address for which the write was received
        address: Address,
        /// Handler to be used in handling the transaction
        ///
        /// Dropping this handler nacks the address. Any other interaction
        /// acknowledges the address.
        handler: W,
    },
}

impl<R, W> core::fmt::Debug for Transaction<R, W> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Deselect => f.write_str("Deselect"),
            Self::Read { .. } => f.write_str("Read"),
            Self::Write { .. } => f.write_str("Write"),
        }
    }
}

struct BaseI2cSlave<'a> {
    info: Info,
    address: Address,
    _flexcomm: FlexcommRef,
    // holds the lifetime for which we have exclusively borrowed the peripherals needed.
    _phantom: PhantomData<&'a mut ()>,
    ten_bit_info: Option<TenBitAddressInfo>,
}

impl<'a> BaseI2cSlave<'a> {
    /// use flexcomm fc with Pins scl, sda as an I2C Master bus, configuring to speed and pull
    fn new<T: Instance>(
        _bus: Peri<'a, T>,
        scl: Peri<'a, impl SclPin<T>>,
        sda: Peri<'a, impl SdaPin<T>>,
        // TODO - integrate clock APIs to allow dynamic freq selection | clock: crate::flexcomm::Clock,
        address: Address,
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

        // Ensure old remediations dont trigger anymore
        I2C_REMEDIATION[info.index].store(REMEDIATON_NONE, Ordering::Release);

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
                ten_bit_info = Some(TenBitAddressInfo::new(addr));

                // address 0 match = addr first byte, per UM11147 24.7.4
                i2c.slvadr(0).modify(|_, w|
                    // note: byte needs to be adjusted for shift performed via w.slvadr()
                    // SAFETY: unsafe only required due to use of unnamed "bits" field
                    unsafe{w.slvadr().bits(ten_bit_info.unwrap().first_byte >> 1)}.sadisable().enabled());
            }
        }

        // SLVEN = 1, per UM11147 24.3.2.1
        i2c.cfg().write(|w| w.slven().enabled());

        Ok(Self {
            info,
            address,
            _flexcomm: flexcomm,
            _phantom: PhantomData,
            ten_bit_info,
        })
    }
}

enum PendingRemediation {
    Write,
}

/// use `FCn` as I2C Slave controller
pub struct BlockingI2cSlave<'a> {
    base: BaseI2cSlave<'a>,
    pending_remediation: Option<PendingRemediation>,
}

impl<'a> BlockingI2cSlave<'a> {
    /// use flexcomm fc with Pins scl, sda as an I2C Master bus, configuring to speed and pull
    pub fn new<T: Instance>(
        _bus: Peri<'a, T>,
        scl: Peri<'a, impl SclPin<T>>,
        sda: Peri<'a, impl SdaPin<T>>,
        // TODO - integrate clock APIs to allow dynamic freq selection | clock: crate::flexcomm::Clock,
        address: Address,
    ) -> Result<Self> {
        Ok(Self {
            base: BaseI2cSlave::new::<T>(_bus, scl, sda, address)?,
            pending_remediation: None,
        })
    }

    /// Listen for a new incoming i2c transaction
    pub fn listen<'b>(&'b mut self) -> Result<Transaction<BlockingI2cSlaveRead<'b>, BlockingI2cSlaveWrite<'b>>>
    where
        'a: 'b,
    {
        let i2c = self.base.info.regs;

        // Handle pending remediations
        match self.pending_remediation {
            Some(PendingRemediation::Write) => loop {
                blocking_poll(self.base.info);
                let stat = i2c.stat().read();
                if stat.slvpending().is_pending() && stat.slvstate().is_slave_receive() {
                    i2c.slvctl().modify(|_, w| w.slvnack().nack());
                } else {
                    break;
                }
            },
            None => {}
        }
        self.pending_remediation = None;

        loop {
            // Wait to be addressed
            blocking_poll(self.base.info);

            let stat = i2c.stat().read();

            if stat.slvdesel().is_deselected() {
                // clear deselection and return it
                i2c.stat().write(|w| w.slvdesel().deselected());
                if self.base.ten_bit_info.map(|v| v.selected).unwrap_or(true) {
                    self.base.ten_bit_info = self.base.ten_bit_info.map(|mut v| {
                        v.selected = false;
                        v
                    });
                    return Ok(Transaction::Deselect);
                } else {
                    // We weren't actually selected, so no need for deselect transaction
                    continue;
                }
            }

            if !stat.slvstate().is_slave_address() {
                return Err(TransferError::OtherBusError.into());
            }

            if !stat.slvpending().is_pending() {
                return Err(TransferError::OtherBusError.into());
            }

            // Get the address
            let addr = i2c.slvdat().read().data().bits();

            if let Some(ten_bit_info) = self.base.ten_bit_info {
                if addr & 1 == 0 {
                    // Write transaction, read next byte and check 10 bit address
                    i2c.slvctl().write(|w| w.slvcontinue().continue_());
                    blocking_poll(self.base.info);
                    if !i2c.stat().read().slvstate().is_slave_receive() || !i2c.stat().read().slvpending().is_pending()
                    {
                        if i2c.stat().read().slvdesel().is_deselected() {
                            // deselect handled on next iteration of the loop
                            continue;
                        }
                    }

                    if i2c.slvdat().read().data().bits() == ten_bit_info.second_byte {
                        // We are selected, return a write transaction
                        // The actual selection is only recorded once the user tries to read the
                        // first byte from the master, as dropping before that should trigger a nack
                        // anyway

                        break Ok(Transaction::Write {
                            address: self.base.address,
                            handler: BlockingI2cSlaveWrite {
                                info: self.base.info,
                                should_ack_addr: true,
                                ten_bit_info: &mut self.base.ten_bit_info,
                                pending_remediation: &mut self.pending_remediation,
                            },
                        });
                    } else {
                        // Not selected, mark us as such
                        if ten_bit_info.selected {
                            // We were selected, so need to signal deselect to user.
                            self.base.ten_bit_info = self.base.ten_bit_info.map(|mut v| {
                                v.selected = false;
                                v
                            });
                            self.pending_remediation = Some(PendingRemediation::Write);
                            return Ok(Transaction::Deselect);
                        } else {
                            // Ensure that all the necessary bytes are nacked
                            loop {
                                let stat = i2c.stat().read();
                                if stat.slvpending().is_pending() && stat.slvstate().is_slave_receive() {
                                    i2c.slvctl().modify(|_, w| w.slvnack().nack());
                                    blocking_poll(self.base.info);
                                } else {
                                    break;
                                }
                            }

                            continue;
                        }
                    }
                } else {
                    // Read transaction, check if we are selected
                    if ten_bit_info.selected {
                        // We are selected, return a read transaction
                        // acknowledge only when the user doesn't immediately drop but tries to
                        // provide data to the master.

                        break Ok(Transaction::Read {
                            address: self.base.address,
                            handler: BlockingI2cSlaveRead {
                                info: self.base.info,
                                should_ack_addr: true,
                                _phantom: PhantomData,
                            },
                        });
                    } else {
                        // Not for us, nack address
                        i2c.slvctl().modify(|_, w| w.slvnack().nack());
                        continue;
                    }
                }
            } else {
                if addr & 1 == 0 {
                    // Write transaction
                    break Ok(Transaction::Write {
                        address: self.base.address,
                        handler: BlockingI2cSlaveWrite {
                            info: self.base.info,
                            should_ack_addr: true,
                            ten_bit_info: &mut self.base.ten_bit_info,
                            pending_remediation: &mut self.pending_remediation,
                        },
                    });
                } else {
                    // Read transaction
                    break Ok(Transaction::Read {
                        address: self.base.address,
                        handler: BlockingI2cSlaveRead {
                            info: self.base.info,
                            should_ack_addr: true,
                            _phantom: PhantomData,
                        },
                    });
                }
            }
        }
    }
}

fn blocking_poll(info: Info) {
    let i2c = info.regs;

    while i2c.stat().read().slvpending().is_in_progress() && i2c.stat().read().slvdesel().is_not_deselected() {}
}

/// Handler for a blocking i2c write
pub struct BlockingI2cSlaveWrite<'a> {
    info: Info,
    should_ack_addr: bool,
    ten_bit_info: &'a mut Option<TenBitAddressInfo>,
    pending_remediation: &'a mut Option<PendingRemediation>,
}

/// Result of a potentially partial i2c write.
pub enum WriteResult<R> {
    /// Complete buffer was filled, last byte still unacknowledged.
    Partial(R),
    /// Partial fill of the buffer. All bytes were acknowledged.
    Complete(usize),
}

impl<'a> BlockingI2cSlaveWrite<'a> {
    /// Get `buffer.len()` bytes from the master, acknowledging all but the last one in the buffer.
    pub fn handle_part(mut self, buffer: &mut [u8]) -> Result<WriteResult<BlockingI2cSlaveWrite<'a>>> {
        let i2c = self.info.regs;
        let mut xfer_count: usize = 0;

        *self.ten_bit_info = self.ten_bit_info.map(|mut v| {
            v.selected = true;
            v
        });

        for b in buffer {
            // confirm previous byte and start reading the next
            if !i2c.stat().read().slvpending().is_pending() {
                return Err(TransferError::OtherBusError.into());
            }
            i2c.slvctl().modify(|_, w| w.slvcontinue().continue_());

            // At this point the address has definitely been acknowledged
            self.should_ack_addr = false;

            //wait for completion of the read
            blocking_poll(self.info);

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
                return Err(TransferError::OtherBusError.into());
            }

            // Now we can safely read the next byte
            *b = i2c.slvdat().read().data().bits();
            xfer_count += 1;
        }

        let stat = i2c.stat().read();
        if stat.slvdesel().is_deselected() {
            // inhibit drop
            core::mem::forget(self);
            return Ok(WriteResult::Complete(xfer_count));
        } else if stat.slvstate().is_slave_address() {
            // Handle restart
            // inhibit drop
            core::mem::forget(self);
            return Ok(WriteResult::Complete(xfer_count));
        } else if stat.slvstate().is_slave_receive() {
            // Master still wants to send more data, transaction incomplete
            return Ok(WriteResult::Partial(self));
        }

        // We should not get here
        Err(TransferError::OtherBusError.into())
    }

    /// Receive `buffer.len()` bytes from the master, acknowledging all of them. Nacks
    /// any overrun write by the master.
    pub fn handle_complete(self, buffer: &mut [u8]) -> Result<usize> {
        match self.handle_part(buffer)? {
            WriteResult::Partial(handler) => {
                // ack last byte but nack any overrun.
                handler.handle_part(&mut [0])?;
                Ok(buffer.len())
            }
            WriteResult::Complete(size) => Ok(size),
        }
    }
}

impl Drop for BlockingI2cSlaveWrite<'_> {
    fn drop(&mut self) {
        let i2c = self.info.regs;
        if self.should_ack_addr {
            // No need to wait, by construction we are already in pending state
            i2c.slvctl().modify(|_, w| w.slvnack().nack());
        } else {
            *self.pending_remediation = Some(PendingRemediation::Write);
        }
    }
}

/// Handler for a blocking I2C read transaction.
pub struct BlockingI2cSlaveRead<'a> {
    info: Info,
    should_ack_addr: bool,
    _phantom: PhantomData<&'a mut ()>,
}

/// Result of a potentially partial i2c write.
pub enum ReadResult<R> {
    /// Complete buffer was filled, last byte still unacknowledged.
    Partial(R),
    /// Partial fill of the buffer. All bytes were acknowledged.
    Complete(usize),
}

impl<'a> BlockingI2cSlaveRead<'a> {
    /// Provide part of the data for the read transaction
    fn handle_part(mut self, buffer: &[u8]) -> Result<ReadResult<Self>> {
        let i2c = self.info.regs;

        // Ack address if needed
        if self.should_ack_addr {
            self.should_ack_addr = false;
            i2c.slvctl().modify(|_, w| w.slvcontinue().continue_());
        }

        let mut xfer_count = 0;

        for b in buffer {
            // Block until something happens
            blocking_poll(self.info);

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
            // inhibit drop
            core::mem::forget(self);
            return Ok(ReadResult::Complete(xfer_count));
        } else if stat.slvstate().is_slave_address() {
            // Handle restart after read
            // inhibit drop
            core::mem::forget(self);
            return Ok(ReadResult::Complete(xfer_count));
        } else if stat.slvstate().is_slave_transmit() {
            // Master is still expecting data, transaction incomplete
            return Ok(ReadResult::Partial(self));
        }

        // We should not get here
        Err(TransferError::WriteFail.into())
    }

    /// Finish the entire read transaction, providing the overrun character once the buffer runs out
    pub fn handle_complete(self, buffer: &[u8], ovc: u8) -> Result<usize> {
        match self.handle_part(buffer)? {
            ReadResult::Partial(mut this) => {
                let mut total = buffer.len();
                loop {
                    match this.handle_part(&[ovc])? {
                        ReadResult::Partial(handler) => {
                            this = handler;
                            total += 1;
                        }
                        ReadResult::Complete(extra) => {
                            return Ok(total + extra);
                        }
                    }
                }
            }
            ReadResult::Complete(size) => Ok(size),
        }
    }
}

impl Drop for BlockingI2cSlaveRead<'_> {
    fn drop(&mut self) {
        let i2c = self.info.regs;
        if self.should_ack_addr {
            i2c.slvctl().modify(|_, w| w.slvnack().nack());
        } else {
            // complete the read with all-ones overrun
            loop {
                // Block until something happens
                blocking_poll(self.info);

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
                    // This probably indicates an error, but nothing we can do here.
                    break;
                }

                i2c.slvdat().write(|w|
                    // SAFETY: unsafe only here due to use of bits()
                    unsafe{w.data().bits(0xFF)});
                i2c.slvctl().write(|w| w.slvcontinue().continue_());
            }
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

/// use `FCn` as I2C Slave controller
pub struct AsyncI2cSlave<'a> {
    base: BaseI2cSlave<'a>,
    dma_ch: Option<dma::channel::Channel<'a>>,
}

impl<'a> AsyncI2cSlave<'a> {
    /// use flexcomm fc with Pins scl, sda as an I2C Master bus, configuring to speed and pull
    pub fn new<T: Instance>(
        _bus: Peri<'a, T>,
        scl: Peri<'a, impl SclPin<T>>,
        sda: Peri<'a, impl SdaPin<T>>,
        _irq: impl interrupt::typelevel::Binding<T::Interrupt, InterruptHandler<T>> + 'a,
        // TODO - integrate clock APIs to allow dynamic freq selection | clock: crate::flexcomm::Clock,
        address: Address,
        dma_ch: Peri<'a, impl SlaveDma<T>>,
    ) -> Result<Self> {
        let ch = dma::Dma::reserve_channel(dma_ch);

        if ch.is_some() {
            let this: AsyncI2cSlave<'a> = Self {
                base: BaseI2cSlave::new(_bus, scl, sda, address)?,
                dma_ch: Some(ch.unwrap()),
            };

            T::Interrupt::unpend();
            unsafe { T::Interrupt::enable() };

            Ok(this)
        } else {
            Err(super::Error::UnsupportedConfiguration)
        }
    }
}

impl AsyncI2cSlave<'_> {
    /// Listen for commands from the I2C Master asynchronously
    pub async fn listen(&mut self) -> Result<Command> {
        let i2c = self.base.info.regs;

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

        if let Some(ten_bit_address) = self.base.ten_bit_info {
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
        let i2c = self.base.info.regs;
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

        // Enable DMA
        i2c.slvctl().write(|w| w.slvdma().enabled());

        // Enable interrupt
        i2c.intenset()
            .write(|w| w.slvpendingen().enabled().slvdeselen().enabled());

        let options = dma::transfer::TransferOptions::default();
        // Keep a reference to Transfer so it does not get dropped and aborted the DMA transfer
        let _transfer =
            self.dma_ch
                .as_ref()
                .unwrap()
                .read_from_peripheral(i2c.slvdat().as_ptr() as *mut u8, buf, options);

        // Hold guard to make sure that we send a NAK on cancellation
        // Since drop order is reverse, this comes BEFORE the dma guard,
        // so the DMA guard will be dropped FIRST, then the NAK guard.
        let nak_guard = NakGuard { info: self.base.info };
        // Hold guard to disable on cancellation or completion
        let _dma_guard = OnDrop::new(|| {
            i2c.slvctl().modify(|_r, w| w.slvdma().disabled());
        });

        poll_fn(|cx| {
            let i2c = self.base.info.regs;
            let dma = self.dma_ch.as_ref().unwrap();

            I2C_WAKERS[self.base.info.index].register(cx.waker());
            dma.get_waker().register(cx.waker());

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
            if !dma.is_active() && stat.slvstate().is_slave_receive() {
                return Poll::Ready(());
            }

            Poll::Pending
        })
        .await;

        // Complete DMA transaction and get transfer count
        nak_guard.defuse();
        let xfer_count = self.abort_dma(buf_len);
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
        let i2c = self.base.info.regs;

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
        // Keep a reference to Transfer so it does not get dropped and aborted the DMA transfer
        let _transfer =
            self.dma_ch
                .as_ref()
                .unwrap()
                .write_to_peripheral(buf, i2c.slvdat().as_ptr() as *mut u8, options);

        // Hold guard to disable on cancellation or completion
        let _dma_guard = OnDrop::new(|| {
            i2c.slvctl().modify(|_r, w| w.slvdma().disabled());
        });

        poll_fn(|cx| {
            let i2c = self.base.info.regs;
            let dma = self.dma_ch.as_ref().unwrap();

            I2C_WAKERS[self.base.info.index].register(cx.waker());
            dma.get_waker().register(cx.waker());

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
        let xfer_count = self.abort_dma(buf.len());
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

    async fn poll_sw_action(&self) {
        let i2c = self.base.info.regs;

        i2c.intenset()
            .write(|w| w.slvpendingen().enabled().slvdeselen().enabled());

        poll_fn(|cx: &mut core::task::Context<'_>| {
            I2C_WAKERS[self.base.info.index].register(cx.waker());

            let stat = i2c.stat().read();
            if stat.slvdesel().is_deselected() {
                return Poll::Ready(());
            }
            if stat.slvpending().is_pending() {
                return Poll::Ready(());
            }

            Poll::Pending
        })
        .await;
    }

    /// Complete DMA and return bytes transfer
    fn abort_dma(&self, xfer_size: usize) -> usize {
        // abort DMA if DMA is not compelted
        let dma = self.dma_ch.as_ref().unwrap();
        let remain_xfer_count = dma.get_xfer_count();
        let mut xfer_count = xfer_size;
        if dma.is_active() && remain_xfer_count != 0x3FF {
            xfer_count -= remain_xfer_count as usize + 1;
            dma.abort();
        }

        xfer_count
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
                I2C_REMEDIATION[self.info.index].fetch_or(REMEDIATON_SLAVE_NAK, Ordering::AcqRel);
            }
        })
    }
}
