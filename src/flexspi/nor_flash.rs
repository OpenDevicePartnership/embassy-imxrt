//! FlexSPI FLASH driver.

use super::peripheral::{CommandSequence, FlexSpi, InvalidCommandSequence};
use crate::Peri;
use crate::peripherals::FLEXSPI;

/// FlexSPI NOR FLASH driver.
///
/// This driver re-uses the existing FlexSPI configuration.
/// It only changes some settings for the IP command execution.
/// It should not interfere with AHB access to the flash device.
///
/// It can also probe the flash memory to automatically detect the correct [`FlashAlignment`].
/// For this to work, the flash memory must have a valid FlexSPI Configuration Block (FCB) at address 0x400.
/// See the documentation of the ROM bootloader in the RT6xx User Manual for more details about the FCB.
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct FlexSpiNorFlash<'a> {
    /// The FlexSPI peripheral.
    flex_spi: FlexSpi<'a>,

    /// The alignment requirements of the flash memory.
    alignment: FlashAlignment,
}

/// Configuration of the [`FlexSpiNorFlash`] driver.
pub struct FlashConfig {
    /// Alignment requirements of access to the flash memory.
    pub alignment: FlashAlignment,

    /// Command sequences for the FlexSPI peripheral.
    pub sequences: FlashSequences,
}

/// Alignment requirements of a flash memory chip.
#[derive(Copy, Clone)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct FlashAlignment {
    /// The alignment requirement of read commands.
    ///
    /// Read command start and end addresses must be aligned to a multiple of this value.
    pub read_alignment: u32,

    /// The alignment requirement of write commands.
    ///
    /// Write command start and end addresses must be aligned to a multiple of this value.
    ///
    /// Note that writes must also be fully contained in a single page (see [`page_size`] for details).
    pub write_alignment: u32,

    /// The size of a sector erased by the [`FlexSpiFlash::sector_erase()`] command.
    pub sector_size: u32,

    /// The size of a block erased by the [`FlexSpiFlash::block_erase()`] command.
    pub block_size: u32,

    /// The size of a page for the [`FlexSpiFlash::page_program()`] command.
    ///
    /// Writes using the `page_program()` command may not cross page boundaries.
    pub page_size: u32,
}

/// FlexSPI command sequences for NOR flash.
///
/// You can use the [`mimxrt600_fcb`] crate to create command sequences.
// TODO: Support longer sequences?
pub struct FlashSequences {
    /// The sequence for reading data from flash.
    pub read: [u32; 4],

    /// The sequence for reading the flash status register.
    pub read_status: [u32; 4],

    /// The sequence for setting the write-enable latch.
    pub write_enable: [u32; 4],

    /// The sequence to erase a single sector.
    pub erase_sector: [u32; 4],

    /// The sequence to erase a single block.
    pub erase_block: [u32; 4],

    /// The sequence to erase the entire chip.
    pub erase_chip: [u32; 4],

    /// The sequence for performing a page program.
    pub page_program: [u32; 4],
}

/// Sequence indexes in the LUT for specific commands.
///
/// These are chosen specifically for the driver.
/// Note that the upper half of the LUT (16..32) seems to ignore all writes and always reads as 0.
/// So avoid that region.
#[allow(unused)]
pub(super) mod sequence {
    pub const READ: u8 = 8;
    pub const READ_STATUS: u8 = 9;
    pub const WRITE_ENABLE: u8 = 10;
    pub const ERASE_SECTOR: u8 = 11;
    pub const ERASE_BLOCK: u8 = 12;
    pub const ERASE_CHIP: u8 = 13;
    pub const PAGE_PROGRAM: u8 = 14;
}

impl<'a> FlexSpiNorFlash<'a> {
    /// Create a new FlexSPI FLASH driver with the given configuration.
    ///
    /// The driver does not check if the config is correct for the flash chip connected to the FlexSPI peripheral.
    ///
    /// # Safety
    /// The FLASH driver can be used to write to flash,
    /// which can potentially overwrite parts of the currently running program.
    /// The user must take care to uphold all the soundness requirements of Rust.
    ///
    /// It also overwrites entries in the FlexSPI LUT,
    /// which might interfer with memory mapped flash access in non-default system configurations.
    pub unsafe fn with_config(
        flex_spi: Peri<'a, FLEXSPI>,
        config: FlashConfig,
    ) -> Result<Self, InvalidAlignmentRequirement> {
        // Check if the alignment requirements are all powers of two.
        config.alignment.check()?;

        let flex_spi = FlexSpi::new(flex_spi);
        let mut me = Self {
            flex_spi,
            alignment: config.alignment,
        };

        // Copy the sequences into the LUT.
        unsafe {
            me.flex_spi.write_lut_sequence(sequence::READ, config.sequences.read);
            me.flex_spi
                .write_lut_sequence(sequence::READ_STATUS, config.sequences.read_status);
            me.flex_spi
                .write_lut_sequence(sequence::WRITE_ENABLE, config.sequences.write_enable);
            me.flex_spi
                .write_lut_sequence(sequence::ERASE_SECTOR, config.sequences.erase_sector);
            me.flex_spi
                .write_lut_sequence(sequence::ERASE_BLOCK, config.sequences.erase_block);
            me.flex_spi
                .write_lut_sequence(sequence::ERASE_CHIP, config.sequences.erase_chip);
            me.flex_spi
                .write_lut_sequence(sequence::PAGE_PROGRAM, config.sequences.page_program);
        }

        Ok(me)
    }

    /// Create a new FlexSPI FLASH driver, reading most of the configuration from the flash itself.
    ///
    /// The configuration is reaad from the FlexSPI Configuration Block (FCB) on the flash memory at address `0x400..0x600`.
    /// The FCB does not contain the read and write alignment of the flash memory,
    /// so these must be provided manually.
    ///
    /// The driver does not check if the read config is correct for the flash chip connected to the FlexSPI peripheral.
    ///
    /// This only works if the FlexSPI has already been configured for memory mapped (AHB) access,
    /// and if the flash memory has a valid and correct FlexSPI Configuration Block.
    ///
    /// # Safety
    /// The FLASH driver can be used to write to flash,
    /// which can potentially overwrite parts of the currently running program.
    /// The user must take care to uphold all the soundness requirements of Rust.
    ///
    /// It also overwrites entries in the FlexSPI LUT,
    /// which might interfer with memory mapped flash access in non-default system configurations.
    pub unsafe fn with_probed_config(
        mut flex_spi: Peri<'a, FLEXSPI>,
        read_alignment: u32,
        write_alignment: u32,
    ) -> Result<Self, ReadConfigError> {
        let config = FlashConfig::read_from_flash(flex_spi.reborrow(), read_alignment, write_alignment)?;
        unsafe { Self::with_config(flex_spi, config).map_err(ReadConfigError::InvalidAlignmentRequirement) }
    }

    /// Get the alignment requirements of the flash device.
    ///
    /// These requirements are either passed in manually or read from the FlexSPI Configuration Block (FCB) on the flash.
    /// In eiter case, it is possible that they do not match the actual requirements of the flash memory.
    pub fn alignment(&self) -> &FlashAlignment {
        &self.alignment
    }

    /// Get a shared reference to the underlying FlexSPI peripheral.
    pub fn peripheral(&self) -> &super::peripheral::FlexSpi<'a> {
        &self.flex_spi
    }

    /// Get the total size in bytes of the addressable flash memory.
    ///
    /// This gives the sum of the size of the flash memory chips connected to each port, capped at 4 GiB.
    pub fn size_bytes(&self) -> u32 {
        // Sum the flash memory of all the ports.
        let total_kb = 0u32;
        let total_kb = total_kb.saturating_add(self.flex_spi.flash_size_kb(super::peripheral::FlashPort::A1));
        let total_kb = total_kb.saturating_add(self.flex_spi.flash_size_kb(super::peripheral::FlashPort::A2));
        let total_kb = total_kb.saturating_add(self.flex_spi.flash_size_kb(super::peripheral::FlashPort::B1));
        let total_kb = total_kb.saturating_add(self.flex_spi.flash_size_kb(super::peripheral::FlashPort::B2));

        // Convert to bytes.
        total_kb.saturating_mul(1024)
    }

    /// Read data from the given flash address.
    ///
    /// NOTE: The address argument is a physical flash address, not a CPU memory address.
    pub fn read(&mut self, address: u32, buffer: &mut [u8]) -> Result<(), ReadError> {
        MisalignedAccessError::check(address, self.alignment.read_alignment)?;
        read(&mut self.flex_spi, sequence::READ, 1, address, buffer)
    }

    /// Erase a sector of flash memory.
    ///
    /// NOTE: The address argument is a physical flash address, not a CPU memory address.
    ///
    /// # Safety
    /// You may not erase flash memory holding code of the current program.
    ///
    /// If your program also performs memory mapped access to the erased region,
    /// you must invalidate the FlexSPI cache and the AHB RX buffer.
    pub unsafe fn erase_sector(&mut self, address: u32) -> Result<(), WriteError> {
        MisalignedAccessError::check(address, self.alignment.sector_size)?;
        self.set_and_verify_write_enable()?;

        unsafe {
            self.flex_spi
                .configure_command_sequence(CommandSequence {
                    start: sequence::ERASE_SECTOR,
                    count: 1,
                    address,
                    data_size: 0,
                    parallel: false,
                })
                .map_err(|e| WriteError::Command(e.into()))?;
            self.flex_spi.trigger_command_and_wait_write()?;
        }
        Ok(())
    }

    /// Erase a block of flash memory.
    ///
    /// NOTE: The address argument is a physical flash address, not a CPU memory address.
    ///
    /// # Safety
    /// You may not erase flash memory holding code of the current program.
    ///
    /// If your program also performs memory mapped access to the erased region,
    /// you must invalidate the FlexSPI cache and the AHB RX buffer.
    pub unsafe fn erase_block(&mut self, address: u32) -> Result<(), WriteError> {
        MisalignedAccessError::check(address, self.alignment.block_size)?;
        self.set_and_verify_write_enable()?;

        unsafe {
            self.flex_spi
                .configure_command_sequence(CommandSequence {
                    start: sequence::ERASE_BLOCK,
                    count: 1,
                    address,
                    data_size: 0,
                    parallel: false,
                })
                .map_err(|e| WriteError::Command(e.into()))?;
            self.flex_spi.trigger_command_and_wait_write()?;
        }
        Ok(())
    }

    /// Erase the whole flash chip.
    ///
    /// # Safety
    /// You may not erase flash memory holding code of the current program.
    /// This means this function is never sound to call when executing your program
    /// directly from flash.
    ///
    /// If your program also performs memory mapped access to the erased region,
    /// you must invalidate the FlexSPI cache and the AHB RX buffer.
    pub unsafe fn erase_chip(&mut self) -> Result<(), WriteError> {
        self.set_and_verify_write_enable()?;

        unsafe {
            self.flex_spi
                .configure_command_sequence(CommandSequence {
                    start: sequence::ERASE_CHIP,
                    count: 1,
                    address: 0,
                    data_size: 0,
                    parallel: false,
                })
                .map_err(|e| WriteError::Command(e.into()))?;
            self.flex_spi.trigger_command_and_wait_write()?;
        }
        Ok(())
    }

    /// Perform a page program.
    ///
    /// The data to be written may not cross a page boundary.
    /// Your flash memory may impose more restrictions on programming.
    /// Please refer to the datasheet of the flash memory for more details.
    ///
    /// NOTE: The address argument is a physical flash address, not a CPU memory address.
    ///
    /// # Safety
    /// You may not modify flash memory holding code of the current program.
    ///
    /// If your program also performs memory mapped access to the erased region,
    /// you must invalidate the FlexSPI cache and the AHB RX buffer.
    pub unsafe fn page_program(&mut self, address: u32, data: &[u8]) -> Result<(), PageProgramError> {
        // Check that address is aligned to self.write_alignment.
        MisalignedAccessError::check(address, self.alignment.write_alignment)?;

        // Check if the write fully falls into one page.
        WriteCrossesPageBoundary::check(address, data.len() as u32, self.alignment.page_size)?;

        // Set write enable latch and verify that it worked.
        self.set_and_verify_write_enable()?;

        // Make sure no old data remains in the TX FIFO.
        self.flex_spi.set_tx_fifo_watermark_u64_words(16);
        self.flex_spi.clear_tx_fifo();

        // Program chunks of at most 128 bytes.
        // TODO: Split into 128 bytes aligned chunks automatically so we can remove the restriction of crossing page boundaries.
        for (i, chunk) in data.chunks(128).enumerate() {
            self.flex_spi.fill_tx_fifo(chunk);
            unsafe {
                self.flex_spi
                    .configure_command_sequence(CommandSequence {
                        start: sequence::PAGE_PROGRAM,
                        count: 1,
                        address: address + i as u32 * 128,
                        data_size: chunk.len() as u16,
                        parallel: false,
                    })
                    .map_err(|e| WriteError::Command(e.into()))?;
                self.flex_spi.trigger_command_and_wait_write()?;
            }
        }

        Ok(())
    }

    /// Read the status of the flash memory.
    ///
    /// Note that you normally do not need to call this yourself.
    /// The status of the flash memory is checked before write operations automatically.
    pub fn read_status(&mut self) -> Result<Status, ReadError> {
        self.flex_spi.set_rx_fifo_watermark_u64_words(16);
        self.flex_spi.clear_rx_fifo();

        unsafe {
            self.flex_spi
                .configure_command_sequence(CommandSequence {
                    start: sequence::READ_STATUS,
                    count: 1,
                    address: 0,
                    data_size: 1,
                    parallel: false,
                })
                .map_err(|e| ReadError::Command(e.into()))?;
            self.flex_spi
                .trigger_command_and_wait()
                .map_err(|e| ReadError::Command(e.into()))?;
        };

        let mut buffer = [0; 1];
        let read = self.flex_spi.drain_rx_fifo(&mut buffer);

        if read != buffer.len() {
            return Err(NotEnoughData {
                expected: buffer.len(),
                actual: read,
            }
            .into());
        }

        Ok(Status(buffer[0]))
    }

    /// Set the write enable latch without verifying that it is actually enabled.
    fn set_write_enable(&mut self) -> Result<(), CommandError> {
        unsafe {
            self.flex_spi.configure_command_sequence(CommandSequence {
                start: sequence::WRITE_ENABLE,
                count: 1,
                address: 0,
                data_size: 0,
                parallel: false,
            })?;
            self.flex_spi.trigger_command_and_wait()?;
        }
        Ok(())
    }

    /// Set the write-enable latch and verify that it is enabled.
    fn set_and_verify_write_enable(&mut self) -> Result<(), WriteError> {
        let status = self.read_status().map_err(WriteError::ReadStatus)?;

        if status.is_write_in_progress() {
            return Err(WriteError::WriteInProgress);
        }

        if status.is_write_enabled() {
            return Ok(());
        }

        for _ in 0..10 {
            self.set_write_enable().map_err(WriteError::SetWriteEnable)?;

            let status = self.read_status().map_err(WriteError::ReadStatus)?;
            if status.is_write_in_progress() {
                return Err(WriteError::WriteInProgress);
            }
            if status.is_write_enabled() {
                return Ok(());
            }
        }

        Err(WriteError::WriteEnableFailed)
    }
}

/// The flash memory status.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct Status(u8);

impl Status {
    /// Returns the raw status byte.
    pub fn raw(self) -> u8 {
        self.0
    }
    /// Check if there is a write operation in progress.
    pub fn is_write_in_progress(self) -> bool {
        // TODO: Taken from Macronix datasheet, but is this universal?
        self.0 & 0x01 != 0
    }

    /// Check if the write-enable latch it set.
    pub fn is_write_enabled(self) -> bool {
        // TODO: Taken from Macronix datasheet, but is this universal?
        self.0 & 0x02 != 0
    }
}

/// Read data from the given flash address.
///
/// NOTE: The address argument is a physical flash address, not a CPU memory address.
fn read(
    flex_spi: &mut FlexSpi,
    sequence_start: u8,
    sequence_count: u8,
    address: u32,
    buffer: &mut [u8],
) -> Result<(), ReadError> {
    // Make sure no old data remains in the RX fifo.
    flex_spi.set_rx_fifo_watermark_u64_words(16);
    flex_spi.clear_rx_fifo();

    // Split into reads of at most 128 (16 u64 words) bytes to ensure we don't need to worry about the FIFO during each transfer.
    for (i, buffer) in buffer.chunks_mut(128).enumerate() {
        // Start the read sequence.
        unsafe {
            flex_spi
                .configure_command_sequence(CommandSequence {
                    start: sequence_start,
                    count: sequence_count,
                    address: address + i as u32 * 128,
                    data_size: buffer.len() as u16,
                    parallel: false,
                })
                .map_err(|e| ReadError::Command(e.into()))?;
            flex_spi
                .trigger_command_and_wait()
                .map_err(|e| ReadError::Command(e.into()))?;
        }

        // Drain the RX queue until the read buffer is full.
        let read = flex_spi.drain_rx_fifo(buffer);
        if read != buffer.len() {
            return Err(NotEnoughData {
                expected: i * 128 + buffer.len(),
                actual: i * 128 + read,
            }
            .into());
        }
    }

    Ok(())
}

impl FlashConfig {
    /// Read the configuration from the FlexSPI Configuration Block (FCB) on the flash memory.
    ///
    /// The read and write alignment of the flash are not stored in the FCB, so they must be provided separately.
    fn read_from_flash(
        flex_spi: Peri<'_, FLEXSPI>,
        read_alignment: u32,
        write_alignment: u32,
    ) -> Result<Self, ReadConfigError> {
        let flex_spi = &mut super::peripheral::FlexSpi::new(flex_spi);

        const FCB_START: u32 = 0x400;
        const FCB_END: u32 = FCB_START + 512;

        // Figure out which flash port holds the FCB, so we can determine what read sequence to use.
        let port = flex_spi
            .port_for_address(FCB_START)
            .ok_or(ReadConfigError::MemoryTooSmall)?;
        if flex_spi.port_for_address(FCB_END - 1) != Some(port) {
            return Err(ReadConfigError::ConfigurationSpreadOverMultipleChips);
        }

        let read_sequence = flex_spi.ahb_read_sequence(port);
        let read_sequence_start = read_sequence.start;
        let read_sequence_count = read_sequence.end - read_sequence.start;

        // Helper to read from flash with the right error type.
        let read = |flex_spi: &mut _, address: u32, buffer: &mut [u8]| {
            read(flex_spi, read_sequence_start, read_sequence_count, address, buffer)
                .map_err(|e| ReadConfigError::ReadFailed(address, e))
        };

        // Read and verify FCB header.
        let mut buffer = [0u8; 8];
        read(flex_spi, FCB_START, &mut buffer)?;
        if buffer != [0x46, 0x43, 0x46, 0x42, 0x00, 0x00, 0x02, 0x56] {
            return Err(ReadConfigError::InvalidHeader(buffer));
        }

        // Read misc configuration.
        let mut buffer = [0u8; 4];
        read(flex_spi, FCB_START + 0x44, &mut buffer)?;
        let device_type = buffer[0];
        let num_pins = buffer[1];
        let lut_custom_seq_enable = buffer[3];

        // We only support serial NOR flash (type == 1).
        if device_type != 1 {
            return Err(ReadConfigError::InvalidDeviceType(device_type));
        }

        // The documentation on the meaning of lutCustomSeq is unclear, so refuse to parse it.
        if lut_custom_seq_enable != 0 {
            return Err(ReadConfigError::CustomLutSequencesNotSupported);
        }

        // Read page size and sector size.
        let mut buffer = [0u8; 8];
        read(flex_spi, FCB_START + 0x1C0, &mut buffer)?;
        let page_size = u32::from_ne_bytes([buffer[0], buffer[1], buffer[2], buffer[3]]);
        let sector_size = u32::from_ne_bytes([buffer[4], buffer[5], buffer[6], buffer[7]]);

        // Read block size.
        let mut buffer = [0u8; 4];
        read(flex_spi, FCB_START + 0x1D0, &mut buffer)?;
        let block_size = u32::from_ne_bytes(buffer);

        let alignment = FlashAlignment {
            read_alignment,
            write_alignment,
            sector_size,
            block_size,
            page_size,
        };
        alignment
            .check()
            .map_err(ReadConfigError::InvalidAlignmentRequirement)?;

        // Read LUT entries.
        //
        // Indices in FCB taken from RT6xx User Manual, section 42.8.16.2.2, table 1105.
        let read_fcb_lut_sequence = |flex_spi: &mut _, index: u32| {
            let mut buffer = [0u8; 16];
            let flash_offset = FCB_START + 0x80 + index * 16;
            read(flex_spi, flash_offset, &mut buffer)?;
            Ok([
                u32::from_ne_bytes([buffer[0], buffer[1], buffer[2], buffer[3]]),
                u32::from_ne_bytes([buffer[4], buffer[5], buffer[6], buffer[7]]),
                u32::from_ne_bytes([buffer[8], buffer[9], buffer[10], buffer[11]]),
                u32::from_ne_bytes([buffer[12], buffer[13], buffer[14], buffer[15]]),
            ])
        };

        let xpi_offset = match num_pins {
            0 | 1 => 0,
            2.. => 1,
        };
        let sequences = FlashSequences {
            read: read_fcb_lut_sequence(flex_spi, 0)?,
            read_status: read_fcb_lut_sequence(flex_spi, 1 + xpi_offset)?,
            write_enable: read_fcb_lut_sequence(flex_spi, 3 + xpi_offset)?,
            erase_sector: read_fcb_lut_sequence(flex_spi, 5)?,
            erase_block: read_fcb_lut_sequence(flex_spi, 8)?,
            erase_chip: read_fcb_lut_sequence(flex_spi, 11)?,
            page_program: read_fcb_lut_sequence(flex_spi, 9)?,
        };

        Ok(Self { alignment, sequences })
    }
}

impl FlashAlignment {
    fn check(&self) -> Result<(), InvalidAlignmentRequirement> {
        // If the alignment is a power of two, exactly one bit is set to 1.
        // We also allow `0`, which we treat the same as `1` (no alignment required).
        if self.read_alignment != 0 && self.read_alignment.count_ones() != 1 {
            return Err(InvalidAlignmentRequirement::ReadAlignment(self.read_alignment));
        }
        if self.write_alignment != 0 && self.write_alignment.count_ones() != 1 {
            return Err(InvalidAlignmentRequirement::WriteAlignment(self.write_alignment));
        }
        Ok(())
    }
}

/// Error that can occur when reading the configuration from flash.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum ReadConfigError {
    /// The configuration block (address 0x400..0x600) is spread over multiple memory chips.
    ConfigurationSpreadOverMultipleChips,

    /// The total memory is too small to hold the configuration block.
    MemoryTooSmall,

    /// Failed to read (part of) the configuration block.
    ReadFailed(u32, ReadError),

    /// The header of the configuration block is invalid.
    InvalidHeader([u8; 8]),

    /// The device type is wrong (should be `1` for serial NOR flash).
    InvalidDeviceType(u8),

    /// The configuration block has `lutCustomSeqEnabled` set to true.
    ///
    /// The documentation of lutCustomSeq is unclear, so no attempt it made to parse it.
    CustomLutSequencesNotSupported,

    /// The alignment requirement is invalid (not a power of two).
    InvalidAlignmentRequirement(InvalidAlignmentRequirement),
}

/// Error indicating that an alignment requirement of flash is not a power of two.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum InvalidAlignmentRequirement {
    /// The read alignment is not a power of two.
    ReadAlignment(u32),

    /// The write alignment is not a power of two.
    WriteAlignment(u32),
}

/// Error that can occur when executing a command.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum CommandError {
    /// The requested command sequence is out of bounds.
    InvalidCommandSequence(InvalidCommandSequence),

    /// An error occured while waiting for the command the finish.
    WaitFinish(super::peripheral::WaitCommandError),
}

impl From<InvalidCommandSequence> for CommandError {
    fn from(value: InvalidCommandSequence) -> Self {
        Self::InvalidCommandSequence(value)
    }
}

impl From<super::peripheral::WaitCommandError> for CommandError {
    fn from(value: super::peripheral::WaitCommandError) -> Self {
        Self::WaitFinish(value)
    }
}

/// Error that can occur when reading data from the flash memory.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum ReadError {
    /// The address is not aligned to the required read alignment.
    Misaligned(MisalignedAccessError),

    /// The command failed to execute.
    Command(CommandError),

    /// The command finished, but we did not get the amount of data we expected.
    NotEnoughData(NotEnoughData),
}

/// We did not receive the amount of data we expected.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct MisalignedAccessError {
    /// The address for the access.
    pub address: u32,

    /// The alignment requirement that the address does not meet.
    pub alignment: u32,
}

impl MisalignedAccessError {
    /// Check if an address is aligned.
    ///
    /// The alignment requires must be a power of two.
    fn check(address: u32, alignment: u32) -> Result<(), MisalignedAccessError> {
        if address & (alignment - 1) == 0 {
            Ok(())
        } else {
            Err(MisalignedAccessError { address, alignment })
        }
    }
}

/// We did not receive the amount of data we expected.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct NotEnoughData {
    /// The expected amount of data.
    pub expected: usize,

    /// The actual amount of data.
    pub actual: usize,
}

impl From<MisalignedAccessError> for ReadError {
    fn from(value: MisalignedAccessError) -> Self {
        Self::Misaligned(value)
    }
}

impl From<NotEnoughData> for ReadError {
    fn from(value: NotEnoughData) -> Self {
        Self::NotEnoughData(value)
    }
}

/// Error that can occur when performing an erase or write operation.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum WriteError {
    /// The address is not aligned to the required write alignment.
    Misaligned(MisalignedAccessError),

    /// Failed to read the flash memory status.
    ReadStatus(ReadError),

    /// A write operation is already in progress.
    WriteInProgress,

    /// Failed to set the write-enable latch.
    SetWriteEnable(CommandError),

    /// The write-enable latch did not actually engage.
    WriteEnableFailed,

    /// The command failed to execute.
    Command(CommandError),
}

impl From<MisalignedAccessError> for WriteError {
    fn from(value: MisalignedAccessError) -> Self {
        Self::Misaligned(value)
    }
}

/// Error that can occur during a page program operation.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum PageProgramError {
    /// The write operation would have crossed a page boundary.
    PageBoundaryCrossed(WriteCrossesPageBoundary),

    /// The operation was attempted but failed.
    WriteFailed(WriteError),
}

impl From<MisalignedAccessError> for PageProgramError {
    fn from(value: MisalignedAccessError) -> Self {
        Self::WriteFailed(value.into())
    }
}

/// A write operation would have crossed a page boundary.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct WriteCrossesPageBoundary {
    /// The start address of the write.
    pub address: u32,

    /// The total length of the write.
    pub length: u32,

    /// The page size of the flash memory.
    pub page_size: u32,
}

impl From<WriteError> for PageProgramError {
    fn from(value: WriteError) -> Self {
        Self::WriteFailed(value)
    }
}

impl WriteCrossesPageBoundary {
    fn check(address: u32, length: u32, page_size: u32) -> Result<(), Self> {
        if length <= page_size && address % page_size + length <= page_size {
            Ok(())
        } else {
            Err(Self {
                address,
                length,
                page_size,
            })
        }
    }
}

impl From<WriteCrossesPageBoundary> for PageProgramError {
    fn from(value: WriteCrossesPageBoundary) -> Self {
        Self::PageBoundaryCrossed(value)
    }
}
