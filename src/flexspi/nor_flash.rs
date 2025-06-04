//! FlexSPI FLASH driver.

use super::peripheral::{CommandSequence, FlexSpi, InvalidCommandSequence};
use crate::peripherals::FLEXSPI;
use crate::Peri;

/// FlexSPI NOR FLASH driver.
///
/// This driver re-uses the existing FlexSPI configuration.
/// It only changes some settings for the IP command execution.
/// It should not interfere with AHB access to the flash device.
///
/// It can also probe the the flash memory to automatically detect the correct [`FlashAlignment`].
/// For this to work, the flash memory must have a valid FlexSPI Configuration Block (FCB) at address 0x400.
/// See the documentation of the ROM bootloader in the RT6xx User Manual for more details about the FCB.
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct FlexSpiNorFlash<'a> {
    /// The FlexSPI peripheral.
    flex_spi: FlexSpi<'a>,

    /// The alignment requirements of the flash memory.
    alignment: FlashAlignment,
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
    /// Note that writes must also be fully contained in a single page (see [`page_size`
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

/// Default sequence indexes in the LUT for specific commands.
#[allow(unused)]
mod sequence {
    pub const READ: u8 = 0;
    pub const READ_STATUS: u8 = 1;
    pub const READ_STATUS_XPI: u8 = 2;
    pub const WRITE_ENABLE: u8 = 3;
    pub const WRITE_ENABLE_XPI: u8 = 4;
    pub const ERASE_SECTOR: u8 = 5;
    pub const ERASE_BLOCK: u8 = 8;
    pub const PAGE_PROGRAM: u8 = 9;
    pub const CHIP_ERASE: u8 = 11;
    pub const EXIT_NO_COMMAND: u8 = 15;
}

impl<'a> FlexSpiNorFlash<'a> {
    /// Create a new FlexSPI FLASH driver without checking the alignment validity.
    ///
    /// The page size is used exclusivly for the [`page_program()`] command.
    /// It is used to ensure that data is not written across page boundaries.
    ///
    /// # Safety
    /// The FLASH driver can be used to write to flash,
    /// which can potentially overwrite parts of the currently running program.
    /// The user must take care to uphold all the soundness requirements of Rust.
    pub unsafe fn new_unchecked(flex_spi: Peri<'a, FLEXSPI>, alignment: FlashAlignment) -> Self {
        // TODO: Add constructor that reads alignment from the FCB on the flash itself.
        let flex_spi = FlexSpi::new(flex_spi);
        let mut me = Self { flex_spi, alignment };

        // Set the RX fifo to the maximum size.
        me.flex_spi.set_rx_fifo_watermark_u64_words(16);
        me.flex_spi.set_tx_fifo_watermark_u64_words(16);

        // Read the FCB from flash.
        let mut fcb = [0; 512];
        if let Err(e) = me.read(0x400, &mut fcb) {
            panic!("Failed to read FCB: {}", e);
        }

        // TODO: Validate FCB header and version number.

        // Copy the FCB LUT entries into the real LUT.
        // TODO: Ensure that we do not change any sequences used by AHB flash access.
        let fcb_lut = &fcb[0x80..][..256];
        for (i, sequence) in fcb_lut.chunks_exact(16).enumerate() {
            let word1 = u32::from_ne_bytes(sequence[0..][..4].try_into().unwrap_or_else(|_| panic!()));
            let word2 = u32::from_ne_bytes(sequence[4..][..4].try_into().unwrap_or_else(|_| panic!()));
            let word3 = u32::from_ne_bytes(sequence[8..][..4].try_into().unwrap_or_else(|_| panic!()));
            let word4 = u32::from_ne_bytes(sequence[12..][..4].try_into().unwrap_or_else(|_| panic!()));
            me.flex_spi.write_lut_sequence(i, [word1, word2, word3, word4]);
        }

        me
    }

    /// Read data from the given flash address.
    ///
    /// NOTE: The address argument is a physical flash address, not a CPU memory address.
    pub fn read(&mut self, address: u32, buffer: &mut [u8]) -> Result<(), ReadError> {
        // TODO: check that start and end address are aligned to `read_alignment`.

        // Make sure no old data remains in the RX fifo.
        self.flex_spi.clear_rx_fifo();

        // Split into reads of at most u16::MAX bytes.
        for (i, mut buffer) in buffer.chunks_mut(u16::MAX as usize).enumerate() {
            let address = address + i as u32 * u16::MAX as u32;
            // Start the read sequence.
            self.flex_spi
                .start_command_sequence(CommandSequence {
                    start: sequence::READ,
                    count: 1,
                    address,
                    data_size: buffer.len() as u16,
                    parallel: false,
                })
                .unwrap_or_else(|_: InvalidCommandSequence| {
                    panic!("FlexSPI driver reported invalid command sequence for hard-coded read sequence")
                });

            // Drain the RX queue until the read buffer is full.
            while !buffer.is_empty() {
                self.flex_spi.wait_rx_ready().map_err(ReadError::WaitRx)?;
                let read = self.flex_spi.drain_rx_fifo(buffer);
                buffer = &mut buffer[read..];
            }

            // Wait for the command to finish (and check for errors).
            self.flex_spi.wait_command_done().map_err(ReadError::WaitFinish)?;
        }

        Ok(())
    }

    /// Erase a sector of flash memory.
    ///
    /// NOTE: The address argument is a physical flash address, not a CPU memory address.
    pub fn erase_sector(&mut self, address: u32) -> Result<(), WriteError> {
        // TODO: verify address is aligned to a sector.
        self.set_and_verify_write_enable()?;

        self.flex_spi
            .start_command_sequence(CommandSequence {
                start: sequence::ERASE_SECTOR,
                count: 1,
                address,
                data_size: 0,
                parallel: false,
            })
            .unwrap_or_else(|_: InvalidCommandSequence| {
                panic!("FlexSPI driver reported invalid command sequence for hard-coded erase sector sequence")
            });

        self.flex_spi.wait_command_done().map_err(WriteError::WaitFinish)?;
        self.wait_write_not_in_progress()?;
        self.flex_spi.invalidate_cache();
        self.flex_spi.clear_ahb_rx_buffers();
        Ok(())
    }

    /// Erase a block of flash memory.
    ///
    /// NOTE: The address argument is a physical flash address, not a CPU memory address.
    pub fn erase_block(&mut self, address: u32) -> Result<(), WriteError> {
        // TODO: verify address is aligned to a block.
        self.set_and_verify_write_enable()?;

        self.flex_spi
            .start_command_sequence(CommandSequence {
                start: sequence::ERASE_BLOCK,
                count: 1,
                address,
                data_size: 0,
                parallel: false,
            })
            .unwrap_or_else(|_: InvalidCommandSequence| {
                panic!("FlexSPI driver reported invalid command sequence for hard-coded erase sector sequence")
            });

        self.flex_spi.wait_command_done().map_err(WriteError::WaitFinish)?;
        self.wait_write_not_in_progress()?;
        self.flex_spi.invalidate_cache();
        self.flex_spi.clear_ahb_rx_buffers();
        Ok(())
    }

    /// Erase the whole flash chip.
    pub fn erase_chip(&mut self) -> Result<(), WriteError> {
        self.set_and_verify_write_enable()?;

        self.flex_spi
            .start_command_sequence(CommandSequence {
                start: sequence::CHIP_ERASE,
                count: 1,
                address: 0,
                data_size: 0,
                parallel: false,
            })
            .unwrap_or_else(|_: InvalidCommandSequence| {
                panic!("FlexSPI driver reported invalid command sequence for hard-coded erase sector sequence")
            });

        self.flex_spi.wait_command_done().map_err(WriteError::WaitFinish)?;
        self.wait_write_not_in_progress()?;
        self.flex_spi.invalidate_cache();
        self.flex_spi.clear_ahb_rx_buffers();
        Ok(())
    }

    /// Perform a page program.
    ///
    /// The data to be written may not cross a page boundary.
    /// You flash memory may impose more restrictions on programming.
    /// Please refer to the datasheet of the flash memory for more details.
    ///
    /// NOTE: The address argument is a physical flash address, not a CPU memory address.
    pub fn page_program(&mut self, address: u32, data: &[u8]) -> Result<(), PageProgramError> {
        // Check if the write fully falls into one page.
        WriteCrossesPageBoundary::check(address, data.len() as u32, self.alignment.page_size)?;

        // TODO: Check that address is aligned to self.write_alignment.

        // Set write enable latch and verify that it worked.
        self.set_and_verify_write_enable()?;

        // Make sure no old data remains in the TX FIFO.
        self.flex_spi.clear_tx_fifo();

        // Start the command.
        self.flex_spi
            .start_command_sequence(CommandSequence {
                start: sequence::PAGE_PROGRAM,
                count: 1,
                address,
                data_size: data.len() as u16,
                parallel: false,
            })
            .unwrap_or_else(|_: InvalidCommandSequence| {
                panic!("FlexSPI driver reported invalid command sequence for hard-coded page program sequence")
            });

        // TODO: Verify write in progress?

        // Write the data.
        let mut data = data;
        while !data.is_empty() {
            self.flex_spi.wait_tx_ready().map_err(WriteError::WaitTx)?;
            let written = self.flex_spi.fill_tx_fifo(data);
            data = &data[written..];
        }

        // Wait for the command to finish.
        self.flex_spi.wait_command_done().map_err(WriteError::WaitFinish)?;
        self.wait_write_not_in_progress()?;

        // TODO: Part of the data may have been written earlier even if we exit with an error.
        // So we should consider clearing the cache and buffers even in case of errors.
        self.flex_spi.invalidate_cache();
        self.flex_spi.clear_ahb_rx_buffers();

        Ok(())
    }

    /// Read the status of the flash memory.
    ///
    /// Note that you normally do not need to call this yourself.
    /// The status of the flash memory is checked before write operations automatically.
    pub fn read_status(&mut self) -> Result<Status, ReadError> {
        self.flex_spi.clear_rx_fifo();
        self.flex_spi
            .start_command_sequence(CommandSequence {
                start: sequence::READ_STATUS_XPI,
                count: 1,
                address: 0,
                data_size: 4,
                parallel: false,
            })
            .unwrap_or_else(|_: InvalidCommandSequence| {
                panic!("FlexSPI driver reported invalid command sequence for hard-coded read status (XPI) sequence")
            });

        self.flex_spi.wait_command_done().map_err(ReadError::WaitFinish)?;

        let mut buffer = 0xDEADBEEFu32.to_ne_bytes();
        let read = self.flex_spi.drain_rx_fifo(&mut buffer);

        if read != buffer.len() {
            return Err(NotEnoughData {
                expected: buffer.len(),
                actual: read,
            }
            .into());
        }

        Ok(Status {
            raw: u32::from_le_bytes(buffer),
        })
    }

    /// Set the write enable latch without verifying that it is actually enabled.
    fn set_write_enable(&mut self) -> Result<(), super::peripheral::WaitCommandError> {
        self.flex_spi
            .start_command_sequence(CommandSequence {
                start: sequence::WRITE_ENABLE_XPI,
                count: 1,
                address: 0,
                data_size: 0,
                parallel: false,
            })
            .unwrap_or_else(|_: InvalidCommandSequence| {
                panic!("FlexSPI driver reported invalid command sequence for hard-coded write enable sequence")
            });
        self.flex_spi.wait_command_done()
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

    /// Wait for a write to not be in progress.
    fn wait_write_not_in_progress(&mut self) -> Result<(), WriteError> {
        let status = self.read_status().map_err(WriteError::ReadStatus)?;
        while status.is_write_in_progress() {
            // We can not use the WFE instruction here,
            // as the write is handled by the flash chip.
            // There will not be a CPU event to wake us up.
        }
        Ok(())
    }
}

/// The flash memory status.
#[derive(Copy, Clone)]
pub struct Status {
    /// The raw status returned by the flash chip.
    pub raw: u32,
}

impl Status {
    /// Check if there is a write operation in progress.
    pub fn is_write_in_progress(self) -> bool {
        // TODO: Taken from Macronix datasheet, but is this universal?
        self.raw & 0x01 != 0
    }

    /// Check if the write-enable latch it set.
    pub fn is_write_enabled(self) -> bool {
        // TODO: Taken from Macronix datasheet, but is this universal?
        self.raw & 0x02 != 0
    }
}

/// Error that can occur when reading data from the flash memory.
#[derive(Copy, Clone)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum ReadError {
    /// An error occured while waiting for data in the RX buffer.
    WaitRx(super::peripheral::WaitCommandError),

    /// An error occured while waiting for the command the finish.
    WaitFinish(super::peripheral::WaitCommandError),

    /// The command finished, but we did not get the amount of data we expected.
    NotEnoughData(NotEnoughData),
}

/// We did not receive the amount of data we expected.
#[derive(Copy, Clone)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct NotEnoughData {
    /// The expected amount of data.
    pub expected: usize,

    /// The actual amount of data.
    pub actual: usize,
}

impl From<NotEnoughData> for ReadError {
    fn from(value: NotEnoughData) -> Self {
        Self::NotEnoughData(value)
    }
}

/// Error that can occur when performing an erase or write operation.
#[derive(Copy, Clone)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum WriteError {
    /// Failed to read the flash memory status.
    ReadStatus(ReadError),

    /// A write operation is already in progress.
    WriteInProgress,

    /// Failed to set the write-enable latch.
    SetWriteEnable(super::peripheral::WaitCommandError),

    /// The write-enable latch did not actually engage.
    WriteEnableFailed,

    /// An error occured while waiting for space in the TX buffer.
    WaitTx(super::peripheral::WaitTxReadyError),

    /// An error occured while waiting for the command to finish.
    WaitFinish(super::peripheral::WaitCommandError),
}

/// Error that can occur during a page program operation.
#[derive(Copy, Clone)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum PageProgramError {
    /// The write operation would have crossed a page boundary.
    PageBoundaryCrossed(WriteCrossesPageBoundary),

    /// The operation was attempted but failed.
    WriteFailed(WriteError),
}

/// A write operation would have crossed a page boundary.
#[derive(Copy, Clone)]
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
