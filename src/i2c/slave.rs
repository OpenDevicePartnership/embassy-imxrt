//! Implements I2C function support over flexcomm + gpios

use core::future::poll_fn;
use core::marker::PhantomData;
use core::sync::atomic::Ordering;
use core::task::Poll;

use embassy_hal_internal::Peri;

use super::{
    Info, Instance, InterruptHandler, Result, SclPin, SdaPin, SlaveDma, TransferError, I2C_REMEDIATION, I2C_WAKERS,
    REMEDIATION_NONE, REMEDIATION_SLAVE_FINISH_READ, REMEDIATION_SLAVE_FINISH_WRITE, TEN_BIT_PREFIX,
};
use crate::flexcomm::FlexcommRef;
use crate::interrupt::typelevel::Interrupt;
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
    /// transaction. This may be emitted multiple times between transactions.
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
        I2C_REMEDIATION[info.index].store(REMEDIATION_NONE, Ordering::Release);

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
    Read,
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
            Some(PendingRemediation::Read) => {
                // Wait until input is needed, then cycle the slave to reset it
                blocking_poll(self.base.info);
                let stat = i2c.stat().read();
                if stat.slvpending().is_pending() && stat.slvstate().is_slave_transmit() {
                    // send another overrun character (0xff)
                    // Safety: modifying data register is safe since we are pending
                    unsafe {
                        i2c.slvdat().write(|w| w.data().bits(0xff));
                    }
                    i2c.slvctl().modify(|_, w| w.slvcontinue().continue_());
                }
            }
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
                                pending_remediation: &mut self.pending_remediation,
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
                            pending_remediation: &mut self.pending_remediation,
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
    pending_remediation: &'a mut Option<PendingRemediation>,
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
    pub fn handle_part(mut self, buffer: &[u8]) -> Result<ReadResult<Self>> {
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
            *self.pending_remediation = Some(PendingRemediation::Read);
        }
    }
}
/// use `FCn` as I2C Slave controller
pub struct AsyncI2cSlave<'a> {
    base: BaseI2cSlave<'a>,
    dma_ch: dma::channel::Channel<'a>,
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
                dma_ch: ch.unwrap(),
            };

            T::Interrupt::unpend();
            unsafe { T::Interrupt::enable() };

            Ok(this)
        } else {
            Err(super::Error::UnsupportedConfiguration)
        }
    }

    /// Listen for a new incoming i2c transaction
    pub async fn listen<'b>(&'b mut self) -> Result<Transaction<AsyncI2cSlaveRead<'b>, AsyncI2cSlaveWrite<'b>>>
    where
        'a: 'b,
    {
        let i2c = self.base.info.regs;

        // Ensure dma is disabled
        i2c.slvctl().modify(|_, w| w.slvdma().disabled());

        loop {
            wait_no_dma(self.base.info).await;

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

            if !stat.slvpending().is_pending() || !stat.slvstate().is_slave_address() {
                return Err(TransferError::OtherBusError.into());
                // Unexpected state
            }

            // Read address
            let addr = i2c.slvdat().read().data().bits();

            if let Some(ten_bit_info) = self.base.ten_bit_info {
                if addr & 1 == 0 {
                    // Write transaction, read next byte and check 10 bit address
                    i2c.slvctl().write(|w| w.slvcontinue().continue_());
                    wait_no_dma(self.base.info).await;

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

                        // Write transaction
                        return Ok(Transaction::Write {
                            address: self.base.address,
                            handler: AsyncI2cSlaveWrite {
                                info: self.base.info,
                                dma_ch: &self.dma_ch,
                                should_ack_addr: true,
                                ten_bit_info: &mut self.base.ten_bit_info,
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
                            I2C_REMEDIATION[self.base.info.index]
                                .fetch_or(REMEDIATION_SLAVE_FINISH_WRITE, Ordering::Release);
                            // Enable interrupts to ensure the remediation happens
                            i2c.intenset()
                                .write(|w| w.slvpendingen().enabled().slvdeselen().enabled());
                            return Ok(Transaction::Deselect);
                        } else {
                            // Ensure that all necessary data bytes are nacked
                            I2C_REMEDIATION[self.base.info.index]
                                .fetch_or(REMEDIATION_SLAVE_FINISH_WRITE, Ordering::Release);

                            // And wait for next event.
                            continue;
                        }
                    }
                } else {
                    // Read transaction
                    if ten_bit_info.selected {
                        return Ok(Transaction::Read {
                            address: self.base.address,
                            handler: AsyncI2cSlaveRead {
                                info: self.base.info,
                                should_ack_addr: true,
                                dma_ch: &self.dma_ch,
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
                    return Ok(Transaction::Write {
                        address: self.base.address,
                        handler: AsyncI2cSlaveWrite {
                            info: self.base.info,
                            dma_ch: &self.dma_ch,
                            should_ack_addr: true,
                            ten_bit_info: &mut self.base.ten_bit_info,
                        },
                    });
                } else {
                    // Read transaction
                    return Ok(Transaction::Read {
                        address: self.base.address,
                        handler: AsyncI2cSlaveRead {
                            info: self.base.info,
                            should_ack_addr: true,
                            dma_ch: &self.dma_ch,
                            _phantom: PhantomData,
                        },
                    });
                }
            }
        }
    }
}

async fn wait_no_dma(info: Info) {
    let i2c = info.regs;

    i2c.intenset()
        .write(|w| w.slvpendingen().enabled().slvdeselen().enabled());

    poll_fn(|cx: &mut core::task::Context<'_>| {
        I2C_WAKERS[info.index].register(cx.waker());

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

async fn wait_dma(info: Info, dma: &dma::channel::Channel<'_>) {
    let i2c = info.regs;

    i2c.intenset()
        .write(|w| w.slvdeselen().enabled().slvpendingen().enabled());
    poll_fn(|cx| {
        I2C_WAKERS[info.index].register(cx.waker());
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

        // Did we complete the DMA transfer?
        if !dma.is_active() {
            return Poll::Ready(());
        }

        Poll::Pending
    })
    .await;
}

/// Complete DMA and return bytes transfer
fn abort_dma(dma: &dma::channel::Channel<'_>, xfer_size: usize) -> usize {
    // abort DMA if DMA is not compelted
    let remain_xfer_count = dma.get_xfer_count();
    let mut xfer_count = xfer_size;
    if dma.is_active() && remain_xfer_count != 0x3FF {
        xfer_count -= remain_xfer_count as usize + 1;
        dma.abort();
    }

    xfer_count
}

/// Handler for a asynchronous i2c write
pub struct AsyncI2cSlaveWrite<'a> {
    info: Info,
    dma_ch: &'a dma::channel::Channel<'a>,
    should_ack_addr: bool,
    ten_bit_info: &'a mut Option<TenBitAddressInfo>,
}

impl AsyncI2cSlaveWrite<'_> {
    /// Bulk response to the write, all the bytes received
    /// by this function are immediately acknowledged
    async fn handle_part_bulk(mut self, buffer: &mut [u8]) -> Result<WriteResult<Self>> {
        let i2c = self.info.regs;
        let buffer_len = buffer.len();

        *self.ten_bit_info = self.ten_bit_info.map(|mut v| {
            v.selected = true;
            v
        });

        // Acknowledge address if needed, otherwise ack last byte
        i2c.slvctl().modify(|_, w| w.slvcontinue().continue_());
        if self.should_ack_addr {
            self.should_ack_addr = false;
        }

        // Setup the dma transfer
        i2c.slvctl().modify(|_, w| w.slvdma().enabled());
        let transfer = self
            .dma_ch
            .read_from_peripheral(i2c.slvdat().as_ptr() as *const u8, buffer, Default::default());

        wait_dma(self.info, self.dma_ch).await;

        let xfer_count = abort_dma(&self.dma_ch, buffer_len);

        let stat = i2c.stat().read();
        // We can't use stat.slvstate to (reliably) make a decision as to what the
        // next step is, since it is unreliable when slvpending is not
        // in the pending state already. But no deselection and no pending
        // implies the dma ran out and triggered the end of the wait.
        if stat.slvdesel().is_deselected() || stat.slvpending().is_pending() {
            // Something caused us to stop
            // inhibit our own drop handler
            core::mem::forget(self);
            return Ok(WriteResult::Complete(xfer_count));
        } else {
            // That was a partial transaction, the master wants to send more
            // data
            drop(transfer);
            return Ok(WriteResult::Partial(self));
        }
    }

    /// Receive a single byte from the master, and don't immediately ack it
    /// `should_ack_prev` indicates whether there is still a byte from a
    /// previous transaction that should be acknowledged.
    async fn handle_single(mut self, last: &mut u8, should_ack_prev: bool) -> Result<WriteResult<Self>> {
        let i2c = self.info.regs;

        *self.ten_bit_info = self.ten_bit_info.map(|mut v| {
            v.selected = true;
            v
        });

        // Acknowledge address if needed
        if self.should_ack_addr {
            i2c.slvctl().modify(|_, w| w.slvcontinue().continue_());
            self.should_ack_addr = false;
        } else if should_ack_prev {
            // Acknowledge last byte of previous block, since that wasn't done by bulk.
            i2c.slvctl().modify(|_, w| w.slvcontinue().continue_());
        }

        // Disable dma and wait for read to be ready
        i2c.slvctl().modify(|_, w| w.slvdma().disabled());
        wait_no_dma(self.info).await;

        let stat = i2c.stat().read();
        if stat.slvdesel().is_deselected() || stat.slvstate().is_slave_address() {
            // Something caused us to stop
            // inhibit our own drop handler
            core::mem::forget(self);
            return Ok(WriteResult::Complete(0));
        } else if stat.slvstate().is_slave_receive() {
            // That was a partial transaction, the master wants to send more
            // data
            *last = i2c.slvdat().read().data().bits();
            return Ok(WriteResult::Partial(self));
        }

        Err(TransferError::OtherBusError.into())
    }

    /// Get `buffer.len()` bytes from the master, acknowledging all but the last one in the buffer.
    pub async fn handle_part(mut self, buffer: &mut [u8]) -> Result<WriteResult<Self>> {
        let (last, bulk_len) = match buffer.split_last_mut() {
            Some((last, [])) => (last, 0),
            Some((last, bulk)) => {
                match self.handle_part_bulk(bulk).await? {
                    WriteResult::Partial(this) => self = this,
                    v => return Ok(v),
                }
                (last, bulk.len())
            }
            None => {
                return Ok(WriteResult::Partial(self));
            }
        };

        match self.handle_single(last, bulk_len == 0).await? {
            WriteResult::Complete(size) => Ok(WriteResult::Complete(size + bulk_len)),
            v => Ok(v),
        }
    }

    /// Receive `buffer.len()` bytes from the master, acknowledging all of them. Nacks
    /// any overrun write by the master.
    pub async fn handle_complete(self, buffer: &mut [u8]) -> Result<usize> {
        if buffer.len() == 0 {
            // ack last byte but nack any overrun.
            self.handle_single(&mut 0, true).await?;
            Ok(buffer.len())
        } else {
            match self.handle_part_bulk(buffer).await? {
                WriteResult::Partial(_) => Ok(buffer.len()),
                WriteResult::Complete(size) => Ok(size),
            }
        }
    }
}

impl Drop for AsyncI2cSlaveWrite<'_> {
    fn drop(&mut self) {
        if self.should_ack_addr {
            self.info.regs.slvctl().modify(|_, w| w.slvnack().set_bit());
        } else {
            // Using a critical section makes this code a lot simpler and predictable
            critical_section::with(|_| {
                self.info.regs.slvctl().modify(|_, w| w.slvdma().clear_bit());
                I2C_REMEDIATION[self.info.index].fetch_or(REMEDIATION_SLAVE_FINISH_WRITE, Ordering::Acquire);
                self.info
                    .regs
                    .intenset()
                    .write(|w| w.slvdeselen().enabled().slvpendingen().enabled());
            });
        }
    }
}

/// Handler for a asynchronous I2C read transaction.
pub struct AsyncI2cSlaveRead<'a> {
    info: Info,
    dma_ch: &'a dma::channel::Channel<'a>,
    should_ack_addr: bool,
    _phantom: PhantomData<&'a mut ()>,
}

impl AsyncI2cSlaveRead<'_> {
    /// Provide part of the data for the read transaction
    pub async fn handle_part(mut self, buffer: &[u8]) -> Result<ReadResult<Self>> {
        // Empty buffer reads succeed trivially
        if buffer.len() == 0 {
            return Ok(ReadResult::Partial(self));
        }

        let i2c = self.info.regs;

        // Acknowledge address if needed
        if self.should_ack_addr {
            i2c.slvctl()
                .modify(|_, w| w.slvdma().enabled().slvcontinue().continue_());
            self.should_ack_addr = false;
        }

        // Setup the dma transfer
        let transfer = self
            .dma_ch
            .write_to_peripheral(buffer, i2c.slvdat().as_ptr() as *mut u8, Default::default());

        wait_dma(self.info, self.dma_ch).await;

        let xfer_count = abort_dma(self.dma_ch, buffer.len());

        // we got a nack or a stop from master, either way this transaction is
        // completed
        let stat = i2c.stat().read();
        // We can't use stat.slvstate to (reliably) make a decision as to what the
        // next step is, since it is unreliable when slvpending is not
        // in the pending state already. But no deselection and no pending
        // implies the dma ran out and triggered the end of the wait.
        if stat.slvdesel().is_deselected() || stat.slvpending().is_pending() {
            // Something caused us to stop
            // inhibit our own drop handler
            core::mem::forget(self);
            return Ok(ReadResult::Complete(xfer_count));
        } else {
            // Handle restart after read as well as the cases where
            // slave deselected is not set in response to a master nack
            // then the next transaction starts the slave state goes into
            // pending + addressed.
            drop(transfer);
            return Ok(ReadResult::Partial(self));
        }
    }

    /// Finish the entire read transaction, providing the overrun character once the buffer runs out
    pub async fn handle_complete(self, buffer: &[u8], ovc: u8) -> Result<usize> {
        // Note, this coudl be made a bit more efficient by using the linked transfer functionality
        // of the dma.
        match self.handle_part(buffer).await? {
            ReadResult::Partial(mut this) => {
                let mut total = buffer.len();
                loop {
                    match this.handle_part(&[ovc]).await? {
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

impl Drop for AsyncI2cSlaveRead<'_> {
    fn drop(&mut self) {
        if self.should_ack_addr {
            self.info.regs.slvctl().modify(|_, w| w.slvnack().set_bit());
        } else {
            // Using a critical section makes this code a lot simpler and predictable
            critical_section::with(|_| {
                self.info.regs.slvctl().modify(|_, w| w.slvdma().clear_bit());
                I2C_REMEDIATION[self.info.index].fetch_or(REMEDIATION_SLAVE_FINISH_READ, Ordering::Acquire);
                self.info
                    .regs
                    .intenset()
                    .write(|w| w.slvdeselen().enabled().slvpendingen().enabled());
            });
        }
    }
}
