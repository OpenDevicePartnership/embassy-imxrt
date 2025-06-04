//! Low level FlexSPI peripheral access.

use crate::peripherals::FLEXSPI;
use crate::{pac, Peri};

/// Low level FlexSPI interface.
pub struct FlexSpi<'a> {
    /// The FlexSPI peripheral.
    #[allow(
        unused,
        reason = "This field represents unique access to the FlexSPI peripheral, but we don't actually need the object"
    )]
    flex_spi: Peri<'a, FLEXSPI>,
}

/// A command sequence to run on the FlexSPI peripheral.
///
/// Note that this struct does not encode an actual command to send to the flash.
/// It points to pre-defined commands in the FlexSPI LUT (lookup table).
#[derive(Copy, Clone)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct CommandSequence {
    /// The start index in the LUT of the sequence to execute.
    pub start: u8,

    /// The number of sequences to run.
    ///
    /// If more than one, sequences will be run from the LUT in order, starting at [`Self::sequence_start`].
    /// A value of 0 is interpreted the same as 1: run a single sequence.
    pub count: u8,

    /// The physical flash address for the command sequence.
    ///
    /// This is used by the `RADDR` and `CADDR` instructions.
    pub address: u32,

    /// The data size for the instruction.
    ///
    /// This is used by the `DATSZ` instruction.
    pub data_size: u16,

    /// Enable parallel mode for this command sequence.
    ///
    /// In parallel mode, instructions are sent to two connected flash memories.
    /// Refer to the FlexSPI documentation in the RT6xx user manual for details about parallel mode.
    pub parallel: bool,
}

impl<'a> FlexSpi<'a> {
    /// Create a new FlexSPI peripheral.
    pub fn new(flex_spi: Peri<'a, FLEXSPI>) -> Self {
        Self { flex_spi }
    }

    /// Write a command sequence to the LUT.
    ///
    /// This function will overwrite one single LUT sequence,
    /// which consists of 4 words, where each word contains two instructions.
    ///
    /// See the [`mimxrt600-fcb`] crate for utilities to create LUT commnad sequences.
    ///
    /// # Safety
    /// Altering the LUT will potentiall change the behaviour of memory mapped flash access.
    /// You must ensure that memory mapped flash access still behaves properly.
    /// The easiest way to do this is to only modify LUT sequences that are NOT used for memory mapped flash access.
    pub unsafe fn write_lut_sequence(&mut self, index: usize, data: [u32; 4]) {
        let flexspi = pac::Flexspi::steal();

        // Unlock the LUT.
        flexspi.lutkey().modify(|_, w| w.key().bits(0x5AF05AF0));
        flexspi.lutcr().write(|w| w.unlock().set_bit());

        // Write the LUT entries.
        flexspi.lut(index * 4 + 0).write(|w| w.bits(data[0]));
        flexspi.lut(index * 4 + 1).write(|w| w.bits(data[1]));
        flexspi.lut(index * 4 + 2).write(|w| w.bits(data[2]));
        flexspi.lut(index * 4 + 3).write(|w| w.bits(data[3]));

        // Lock the LUT.
        flexspi.lutkey().modify(|_, w| w.key().bits(0x5AF05AF0));
        flexspi.lutcr().write(|w| w.lock().set_bit());
    }

    /// Start a command sequence from the LUT using the IP interface.
    ///
    /// Does not wait for the sequence to finish, as you may need to write to the TX FIFO or read from the RX FIFO..
    pub fn start_command_sequence(&mut self, sequence: CommandSequence) -> Result<(), InvalidCommandSequence> {
        // Check if the sequence start and end fall within the valid range (0..32).
        if sequence.start >= 32 || sequence.count >= 32 || sequence.start + sequence.count >= 32 {
            return Err(InvalidCommandSequence {
                start: sequence.start,
                count: sequence.count,
            });
        }

        // Clear all command error/finished interrupt bits in case someone forgot to clear them.
        // Ignore the error bits, because they do not belong to the new command.
        if let Ok(interrupts) = self.check_and_clear_command_errors() {
            self.clear_command_finished_bits(&interrupts);
        }

        // TODO: Can we check if an IP command is already running or queued?

        unsafe {
            let flex_spi = pac::Flexspi::steal();
            let parallel = match sequence.parallel {
                false => pac::flexspi::ipcr1::Iparen::Iparen0,
                true => pac::flexspi::ipcr1::Iparen::Iparen1,
            };
            flex_spi.ipcr0().write(|w| w.sfar().bits(sequence.address));
            flex_spi.ipcr1().write(|w| {
                w.idatsz().bits(sequence.data_size);
                w.iseqid().bits(sequence.start);
                w.iseqnum().bits(sequence.count.saturating_sub(1));
                w.iparen().variant(parallel);
                w
            });
            flex_spi.ipcmd().write(|w| w.trg().bit(true));
        }
        Ok(())
    }

    /// Set the IP TX FIFO watermark to the given number of u64 entries.
    ///
    /// Note: Attempts to set the watermark level to zero will set the level to pne 64 bit word instead.
    pub fn set_tx_fifo_watermark_u64_words(&mut self, num_u64: u8) {
        unsafe {
            let flex_spi = pac::Flexspi::steal();
            let value = num_u64.saturating_sub(1);
            flex_spi.iptxfcr().modify(|_, w| w.txwmrk().bits(value));
        }
    }

    /// Get the TX FIFO watermark level in `u64` words.
    pub fn get_tx_fifo_watermark_u64_words(&mut self) -> u8 {
        let flex_spi = unsafe { pac::Flexspi::steal() };
        flex_spi.iptxfcr().read().txwmrk().bits() + 1
    }

    /// Get the TX FIFO watermark level in bytes.
    pub fn get_tx_fifo_watermark_bytes(&mut self) -> usize {
        usize::from(self.get_tx_fifo_watermark_u64_words()) * 8
    }

    /// Set the IP RX FIFO watermark to the given number of u64 entries.
    ///
    /// Note: Attempts to set the watermark level to zero will set the level to one 64 bit word instead.
    pub fn set_rx_fifo_watermark_u64_words(&mut self, num_u64: u8) {
        unsafe {
            let flex_spi = pac::Flexspi::steal();
            let value = num_u64.saturating_sub(1);
            flex_spi.iprxfcr().modify(|_, w| w.rxwmrk().bits(value));
        }
    }

    /// Get the RX FIFO watermark level in `u64` words.
    pub fn get_rx_fifo_watermark_u64_words(&self) -> u8 {
        let flex_spi = unsafe { pac::Flexspi::steal() };
        flex_spi.iprxfcr().read().rxwmrk().bits() + 1
    }

    /// Get the RX FIFO watermark level in bytes.
    pub fn get_rx_fifo_watermark_bytes(&self) -> usize {
        usize::from(self.get_rx_fifo_watermark_u64_words()) * 8
    }

    /// Get the RX FIFO fill level in `u64` words.
    pub fn get_rx_fill_level_u64_words(&self) -> u8 {
        let flex_spi = unsafe { pac::Flexspi::steal() };
        flex_spi.iprxfsts().read().fill().bits()
    }

    /// Get the RX FIFO fill level in bytes.
    pub fn get_rx_fill_level_bytes(&self) -> usize {
        usize::from(self.get_rx_fill_level_u64_words()) * 8
    }

    /// Wait for the command sequence to finish.
    ///
    /// You must always call this after executing a command sequence to clear the relevant interrupt bits.
    /// Additionally, the FlexSPI peripheral says it is undefined what happens when you start an IP command before the last one finished.
    pub fn wait_command_done(&mut self) -> Result<(), WaitCommandError> {
        unsafe {
            let flex_spi = pac::Flexspi::steal();
            loop {
                // Read status0 before checking interrupt bits to avoid a race between the ipcmddone interrupt and the arbidle status bit
                let status0 = flex_spi.sts0().read();

                // Read the interrupt flags (automatically reports and clears error conditions).
                let interrupts = self.check_and_clear_command_errors()?;
                if interrupts.ipcmddone().bit() {
                    self.clear_command_finished_bits(&interrupts);
                    return Ok(());
                } else if status0.arbidle().bit_is_set() {
                    return Err(WaitCommandError::ArbiterIdle);
                }
            }
        }
    }

    /// Wait for data in the RX FIFO to become available.
    ///
    /// Should only be called after starting a command sequence that reads data from the remote device.
    pub fn wait_rx_ready(&mut self) -> Result<(), WaitCommandError> {
        unsafe {
            let flex_spi = pac::Flexspi::steal();
            loop {
                // Read status0 before checking interrupt bits to avoid a race between the ipcmddone interrupt and the arbidle status bit
                let status0 = flex_spi.sts0().read();

                // Read the interrupt flags (automatically reports and clears error conditions).
                let interrupts = self.check_and_clear_command_errors()?;

                if interrupts.ipcmddone().bit() || interrupts.iprxwa().bit() {
                    // Note: we do not check the FIFO fill level here.
                    // We let the caller do that, because otherwise we need to know how much data to expect.
                    //
                    // We also do not clear the command done bit, since that would break the next call to `wait_command_done()`.
                    return Ok(());
                } else if status0.arbidle().bit_is_set() {
                    return Err(WaitCommandError::ArbiterIdle);
                }
            }
        }
    }

    /// Wait for space in the TX FIFO to become available.
    ///
    /// Should only be called after starting a command sequence that writes data to the remote device.
    pub fn wait_tx_ready(&mut self) -> Result<(), WaitTxReadyError> {
        unsafe {
            let flex_spi = pac::Flexspi::steal();
            loop {
                // Read status0 before checking interrupt bits to avoid a race between the ipcmddone interrupt and the arbidle status bit
                let status0 = flex_spi.sts0().read();

                // Read the interrupt flags (automatically reports and clears error conditions).
                let interrupts = self.check_and_clear_command_errors()?;

                if interrupts.ipcmddone().bit() {
                    // We report an error, so the caller should not call `wait_command_done()` anymore.
                    // So clear the command done bit here.
                    self.clear_command_finished_bits(&interrupts);
                    return Err(WaitTxReadyError::CommandFinished);
                } else if interrupts.iptxwe().bit() {
                    return Ok(());
                } else if status0.arbidle().bit_is_set() {
                    return Err(WaitCommandError::ArbiterIdle.into());
                }
            }
        }
    }

    /// Clear the entire RX fifo.
    pub fn clear_rx_fifo(&mut self) {
        let flex_spi = unsafe { pac::Flexspi::steal() };
        flex_spi.iprxfcr().modify(|_, w| w.clriprxf().set_bit());
    }

    /// Clear the entire TX fifo.
    pub fn clear_tx_fifo(&mut self) {
        let flex_spi = unsafe { pac::Flexspi::steal() };
        flex_spi.iptxfcr().modify(|_, w| w.clriptxf().set_bit());
    }

    /// Write data to the IP TX FIFO and mark it ready for sending.
    ///
    /// This copies data into the IP TX FIFO, up to the watermark level.
    pub fn fill_tx_fifo(&mut self, buffer: &[u8]) -> usize {
        // Limit buffer to fifo length.
        let watermark = self.get_tx_fifo_watermark_bytes();
        let copy_len = buffer.len().min(watermark);
        let buffer = &buffer[..copy_len];

        unsafe {
            let flex_spi = pac::Flexspi::steal();

            // Copy the data from the FIFO to the user buffer.
            read_u8_write_u32_volatile(buffer, flex_spi.tfdr(0).as_ptr().cast());

            // Clear the TX watermark empty interrupt to transmit the data.
            flex_spi.intr().write(|w| w.iptxwe().clear_bit_by_one());
        }

        // Report the number of bytes copied into the buffer.
        copy_len
    }

    /// Drain the RX fifo.
    ///
    /// Returns the number of bytes written into the buffer.
    ///
    /// You should ensure that either the FIFO is filled to the watermark level,
    /// or this is the final drain in a transfer.
    ///
    /// This function will always remove a full watermark of data from the FIFO,
    /// since that is the only way to remove any data from the FIFO.
    pub fn drain_rx_fifo(&mut self, buffer: &mut [u8]) -> usize {
        let flex_spi = unsafe { pac::Flexspi::steal() };

        // Get the fill level, but limit it to the watermark level.
        let watermark = self.get_rx_fifo_watermark_bytes();
        let fill_level = self.get_rx_fill_level_bytes();

        // Truncate buffer to available FIFO size.
        let copy_len = buffer.len().min(fill_level).min(watermark);
        let buffer = &mut buffer[..copy_len];

        // Copy data from TX FIFO to buffer.
        unsafe {
            read_u32_volatile_write_u8(flex_spi.rfdr(0).as_ptr().cast(), buffer);
        }

        // Pop watermark data from the FIFO.
        flex_spi.intr().write(|w| w.iprxwa().clear_bit_by_one());

        // Return the number of bytes written to the buffer.
        copy_len
    }

    /// Discard the AHB RX buffer.
    ///
    /// Warning! Currently not implemented.
    pub fn clear_ahb_rx_buffers(&mut self) {
        // TODO: Uhhh... how?
        // https://community.nxp.com/t5/i-MX-RT-Crossover-MCUs/RT600-685-Invalidating-AHB-FlexSPI-Cache-RX-Buffers-after/m-p/1487133
    }

    /// Invalidate the complete memory cache.
    pub fn invalidate_cache(&mut self) {
        let cache = unsafe { pac::Cache64::steal() };
        loop {
            while cache.ccr().read().go().bit() {
                // Wait for the cache controller to be idle.
            }

            // Execute the command in a critical section to ensure we do not race with other users of the cache.
            // (As long as they also use a critical section this way.)
            let command_started = critical_section::with(|_| {
                if cache.ccr().read().go().bit() {
                    return false;
                }
                // Invalidate the whole cache.
                cache.ccr().modify(|_, w| {
                    w.invw0().set_bit();
                    w.pushw0().clear_bit();
                    w.invw1().set_bit();
                    w.pushw1().clear_bit();
                    w.go().set_bit();
                    w
                });
                true
            });
            if command_started {
                break;
            }
        }
        while cache.ccr().read().go().bit() {
            // Wait for the cache controller to be idle.
        }
    }

    /// Check the interrupt register for command errors, and clear them.
    ///
    /// Performs one read of the interrupt register and clears only the set bits that indicate that command failed.
    /// Only set bits will be cleared, and only if the interrupt flags indicate the command failed.
    /// If this function returns `Ok`, no interrupt flags have been cleared.
    ///
    /// Returns the value of the interrupt register if no error is detected.
    fn check_and_clear_command_errors(&mut self) -> Result<pac::flexspi::intr::R, WaitCommandError> {
        let flex_spi = unsafe { pac::Flexspi::steal() };

        // Read and clear all interrupt flags that indicate a command finished (maybe with an error).
        let interrupts = flex_spi.intr().read();

        if interrupts.ipcmderr().bit() {
            // If the cmderr interrupt is set, read status1 before clearing the interrupt.
            let status1 = flex_spi.sts1().read();
            self.clear_command_finished_bits(&interrupts);
            Err(CommandFailed {
                sequence_index: status1.ipcmderrid().bits(),
                error_code: CommandErrorCode::from_pac(status1.ipcmderrcode()),
            }
            .into())
        } else if interrupts.seqtimeout().bit() {
            self.clear_command_finished_bits(&interrupts);
            Err(WaitCommandError::ExecutionTimeout)
        } else if interrupts.datalearnfail().bit() {
            self.clear_command_finished_bits(&interrupts);
            Err(WaitCommandError::DataLearnFailed)
        } else if interrupts.ipcmdge().bit() {
            self.clear_command_finished_bits(&interrupts);
            Err(WaitCommandError::GrantTimeout)
        } else {
            Ok(interrupts)
        }
    }

    /// Clear all set interrupt bits that indicate a command finished (maybe with an error).
    ///
    /// Does not clear bits that are not set in the input.
    fn clear_command_finished_bits(&mut self, interrupts: &pac::flexspi::intr::R) {
        let flex_spi = unsafe { pac::Flexspi::steal() };
        flex_spi.intr().write(|w| {
            w.ipcmddone().bit(interrupts.ipcmddone().bit());
            w.ipcmderr().bit(interrupts.ipcmderr().bit());
            w.ipcmdge().bit(interrupts.ipcmdge().bit());
            w.datalearnfail().bit(interrupts.datalearnfail().bit());
            w.seqtimeout().bit(interrupts.seqtimeout().bit());
            w
        });
    }
}

/// Error that can occur while waiting for a command to complete or make progress.
#[derive(Copy, Clone)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum WaitCommandError {
    /// The arbiter went into idle state, but the command did not finish.
    ArbiterIdle,

    /// The command failed with an error.
    CommandFailed(CommandFailed),

    /// Timeout waiting for the arbiter to execute the command.
    GrantTimeout,

    /// The command sequence contained a data learn instruction that failed.
    DataLearnFailed,

    /// Timeout while executing the command.
    ExecutionTimeout,
}

/// The FlexSPI peripheral failed to execute a command.
#[derive(Copy, Clone)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct CommandFailed {
    /// The index of the sequence in the FlexSPI LUT that caused the error.
    pub sequence_index: u8,

    /// The error code reported by the flash.
    pub error_code: CommandErrorCode,
}

impl From<CommandFailed> for WaitCommandError {
    fn from(value: CommandFailed) -> Self {
        Self::CommandFailed(value)
    }
}

/// Error code reported by the FlexSPI peripheral when it fails to execute a command sequence.
#[derive(Copy, Clone)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[repr(u8)]
pub enum CommandErrorCode {
    /// No error occured.
    NoError = 0b0000,

    /// Unknown error code: 1.
    Unknown1 = 0b0001,

    /// The sequence contains a JUMP_ON_CS instruction, which is not allowed for IP commands.
    IllegalJumpOnCs = 0b0010,

    /// The sequence contains an unknown opcode.
    UnknownOpcode = 0b0011,

    /// There was a DUMMY_SDR or DUMMY_RWDS_SDR instruction in a DDR sequence.
    DummySdrInDdrSequence = 0b0100,

    /// There was a DUMMY_DDR or DUMMY_RWDS_DDR instruction in a SDR sequence.
    DummyDdrInSdrSequence = 0b0101,

    /// The start address exceeds the total flash capacity.
    StartAddressOutOfBounds = 0b0110,

    /// Unknown error code: 7.
    Unknown7 = 0b0111,

    /// Unknown error code: 8.
    Unknown8 = 0b1000,

    /// Unknown error code: 9.
    Unknown9 = 0b1001,

    /// Unknown error code: 10.
    Unknown10 = 0b1010,

    /// Unknown error code: 11.
    Unknown11 = 0b1011,

    /// Unknown error code: 12.
    Unknown12 = 0b1100,

    /// Unknown error code: 13.
    Unknown13 = 0b1101,

    /// The execution of the sequence timed out.
    SequenceTimeout = 0b1110,

    /// The access crossed a flash boundary.
    AccessCrossedFlashBoundary = 0b1111,
}

impl CommandErrorCode {
    fn from_pac(error_code: pac::flexspi::sts1::IpcmderrcodeR) -> Self {
        let code = error_code.bits();
        match code & 0xF {
            0 => Self::NoError,
            1 => Self::Unknown1,
            2 => Self::IllegalJumpOnCs,
            3 => Self::UnknownOpcode,
            4 => Self::DummySdrInDdrSequence,
            5 => Self::DummyDdrInSdrSequence,
            6 => Self::StartAddressOutOfBounds,
            7 => Self::Unknown7,
            8 => Self::Unknown8,
            9 => Self::Unknown9,
            10 => Self::Unknown10,
            11 => Self::Unknown11,
            12 => Self::Unknown12,
            13 => Self::Unknown13,
            14 => Self::SequenceTimeout,
            15 => Self::AccessCrossedFlashBoundary,
            _ => unsafe { core::hint::unreachable_unchecked() },
        }
    }
}

/// Error that can occur while waiting for space in the TX FIFO.
#[derive(Copy, Clone)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum WaitTxReadyError {
    /// The command failed with an error.
    CommandError(WaitCommandError),

    /// The command finished while we were waiting for space in the TX FIFO.
    CommandFinished,
}

impl From<WaitCommandError> for WaitTxReadyError {
    fn from(value: WaitCommandError) -> Self {
        Self::CommandError(value)
    }
}

/// Error executing a command sequence.
#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct InvalidCommandSequence {
    /// The requested sequence start index.
    pub start: u8,

    /// The requested number of sequences.
    pub count: u8,
}

/// Copy bytes from `source` to `dest`.
///
/// The data is read from the source pointer as bytes,
/// and written to the destination as [`u32`] words with a volatile write.
///
/// If the number of bytes is not a multiple of 4,
/// the last word will be padded with zeros in the most significant bytes.
///
/// # Safety:
/// The destination pointer must point to an region of writable memory properly aligned for `u32` access.
/// The size in bytes of the region must be at-least `source.len()` rounded up to a multiple of 4 bytes.
/// There may be no reference in existence to the destination region.
/// This also means that the destination may not overlap with the source.
unsafe fn read_u8_write_u32_volatile(source: &[u8], dest: *mut u32) {
    unsafe {
        let word_count = source.len() / 4;
        let remainder = source.len() % 4;

        // Write whole words.
        for i in 0..word_count {
            let source: &[u8; 4] = &*source[i * 4..][..4].as_ptr().cast();
            let word = u32::from_ne_bytes(*source);
            dest.add(i).write_volatile(word);
        }

        // Write remainder, zero padded.
        if remainder > 0 {
            let mut word = [0; 4];
            word[..remainder].copy_from_slice(&source[word_count * 4..][..remainder]);
            let word = u32::from_ne_bytes(word);
            dest.add(word_count).write_volatile(word);
        }
    }
}

/// Copy bytes from `source` to `dest`.
///
/// The data is read as [`u32`] words with a volatile read,
/// and written to the destination as [`u8`].
///
/// If the number of bytes is not a multiple of 4,
/// the unneeded most significant bytes of the last word will be discarded.
///
/// # Safety:
/// The source pointer must point to a readable memory region propperly aligned for `u32` access.
/// The size in bytes of the region must be atleast `dest.len()` rounded up to a multiple of 4.
/// The source region may not overlap with the `dest` slice.
unsafe fn read_u32_volatile_write_u8(source: *const u32, dest: &mut [u8]) {
    unsafe {
        let word_count = dest.len() / 4;
        let remainder = dest.len() % 4;

        // Read whole words.
        for i in 0..word_count {
            let dest: &mut [u8; 4] = &mut *dest[i * 4..].as_mut_ptr().cast();
            let source = source.add(i);
            let word = source.read_volatile();
            *dest = word.to_ne_bytes();
        }

        // Read last word and truncate.
        if remainder > 0 {
            let word = source.add(word_count).read_volatile();
            let word = word.to_ne_bytes();
            dest[word_count * 4..].copy_from_slice(&word[..remainder]);
        }
    }
}

#[cfg(test)]
mod tests {
    use core::cell::Cell;

    use super::*;

    #[test]
    fn test_read_u8_write_u32_volatile() {
        {
            let source = [1];
            let dest = Cell::new(0xCAFECAFE);
            unsafe { read_u8_write_u32_volatile(&source, dest.as_ptr()) };
            assert!(dest.get().to_le_bytes() == [0x01, 0x00, 0x00, 0x00]);
        }

        {
            let source = [1, 2];
            let dest = Cell::new(0xCAFECAFE);
            unsafe { read_u8_write_u32_volatile(&source, dest.as_ptr()) };
            assert!(dest.get().to_le_bytes() == [0x01, 0x02, 0x00, 0x00]);
        }
        {
            let source = [1, 2, 3];
            let dest = Cell::new(0xCAFECAFE);
            unsafe { read_u8_write_u32_volatile(&source, dest.as_ptr()) };
            assert!(dest.get().to_le_bytes() == [0x01, 0x02, 0x03, 0x00]);
        }
        {
            let source = [1, 2, 3, 4];
            let dest = Cell::new(0xCAFECAFE);
            unsafe { read_u8_write_u32_volatile(&source, dest.as_ptr()) };
            assert!(dest.get().to_le_bytes() == [0x01, 0x02, 0x03, 0x04]);
        }
        {
            let source = [1, 2, 3, 4, 5];
            let mut dest = Cell::new([0xCAFECAFEu32; 2]);
            unsafe { read_u8_write_u32_volatile(&source, dest.get_mut().as_mut_ptr()) };
            assert!(dest.get()[0].to_le_bytes() == [0x01, 0x02, 0x03, 0x04]);
            assert!(dest.get()[1].to_le_bytes() == [0x05, 0x00, 0x00, 0x00]);
        }
        {
            let source = [1, 2, 3, 4, 5, 6, 7];
            let mut dest = Cell::new([0xCAFECAFEu32; 2]);
            unsafe { read_u8_write_u32_volatile(&source, dest.get_mut().as_mut_ptr()) };
            assert!(dest.get()[0].to_le_bytes() == [0x01, 0x02, 0x03, 0x04]);
            assert!(dest.get()[1].to_le_bytes() == [0x05, 0x06, 0x07, 0x00]);
        }
        {
            let source = [1, 2, 3, 4, 5, 6, 7, 8];
            let mut dest = Cell::new([0xCAFECAFEu32; 2]);
            unsafe { read_u8_write_u32_volatile(&source, dest.get_mut().as_mut_ptr()) };
            assert!(dest.get()[0].to_le_bytes() == [0x01, 0x02, 0x03, 0x04]);
            assert!(dest.get()[1].to_le_bytes() == [0x05, 0x06, 0x07, 0x08]);
        }
    }

    #[test]
    fn test_read_u32_volatile_write_u8() {
        let source = [
            u32::from_ne_bytes([0x01, 0x23, 0x45, 0x67]),
            u32::from_ne_bytes([0x89, 0xAB, 0xCD, 0xEF]),
        ];

        {
            let mut dest = [0xFF];
            unsafe {
                read_u32_volatile_write_u8(source.as_ptr(), &mut dest);
            }
            assert!(dest == [0x01]);
        }
        {
            let mut dest = [0xFF; 2];
            unsafe {
                read_u32_volatile_write_u8(source.as_ptr(), &mut dest);
            }
            assert!(dest == [0x01, 0x23]);
        }
        {
            let mut dest = [0xFF; 3];
            unsafe {
                read_u32_volatile_write_u8(source.as_ptr(), &mut dest);
            }
            assert!(dest == [0x01, 0x23, 0x45]);
        }
        {
            let mut dest = [0xFF; 4];
            unsafe {
                read_u32_volatile_write_u8(source.as_ptr(), &mut dest);
            }
            assert!(dest == [0x01, 0x23, 0x45, 0x67]);
        }
        {
            let mut dest = [0xFF; 5];
            unsafe {
                read_u32_volatile_write_u8(source.as_ptr(), &mut dest);
            }
            assert!(dest == [0x01, 0x23, 0x45, 0x67, 0x89]);
        }
        {
            let mut dest = [0xFF; 6];
            unsafe {
                read_u32_volatile_write_u8(source.as_ptr(), &mut dest);
            }
            assert!(dest == [0x01, 0x23, 0x45, 0x67, 0x89, 0xAB]);
        }
        {
            let mut dest = [0xFF; 7];
            unsafe {
                read_u32_volatile_write_u8(source.as_ptr(), &mut dest);
            }
            assert!(dest == [0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD]);
        }
        {
            let mut dest = [0xFF; 8];
            unsafe {
                read_u32_volatile_write_u8(source.as_ptr(), &mut dest);
            }
            assert!(dest == [0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF]);
        }
    }
}
