//! Implementations of the `embedded_storage` traits using the FlexSPI peripheral.

use super::nor_flash::FlexSpiNorFlash;

/// Adapter struct to implement the `embedded_storage` traits for `FlexSpiNorFlash`.
pub struct FlexSpiNorStorage<'a, const READ_SIZE: u32, const WRITE_SIZE: u32, const ERASE_SIZE: u32> {
    flash: FlexSpiNorFlash<'a>,
}

impl<'a, const READ_SIZE: u32, const WRITE_SIZE: u32, const ERASE_SIZE: u32>
    FlexSpiNorStorage<'a, READ_SIZE, WRITE_SIZE, ERASE_SIZE>
{
    /// Wrap a pre-constructed [`FlexSpiNorFlash`] driver.
    ///
    /// # Safety
    /// The returned object can be used to modify memory mapped flash.
    /// Doing to while holding any reference to the memory (including through statics or extern statics) is undefined behaviour.
    /// This also applies to memory mapped executable code if you are executing your program directly from flash.
    ///
    /// The functions of the `embedded_storage` traits are not marked unsafe, so it is up to the caller of the constructor to ensure that the flash is used correctly.
    pub unsafe fn new(flash: FlexSpiNorFlash<'a>) -> Result<Self, Error> {
        let alignment = flash.alignment();

        if !check_const_size_parameter(READ_SIZE, alignment.read_alignment) {
            Err(IncorrectConstGeneric::ReadSize {
                given: READ_SIZE,
                driver: alignment.read_alignment,
            }
            .into())
        } else if !check_const_size_parameter(WRITE_SIZE, alignment.write_alignment) {
            Err(IncorrectConstGeneric::WriteSize {
                given: WRITE_SIZE,
                driver: alignment.write_alignment,
            }
            .into())
        } else if !check_const_size_parameter(ERASE_SIZE, alignment.sector_size) {
            Err(IncorrectConstGeneric::EraseSize {
                given: ERASE_SIZE,
                driver: alignment.sector_size,
            }
            .into())
        } else {
            Ok(Self { flash })
        }
    }
}

impl<const READ_SIZE: u32, const WRITE_SIZE: u32, const ERASE_SIZE: u32> embedded_storage::nor_flash::ErrorType
    for FlexSpiNorStorage<'_, READ_SIZE, WRITE_SIZE, ERASE_SIZE>
{
    type Error = Error;
}

impl<const READ_SIZE: u32, const WRITE_SIZE: u32, const ERASE_SIZE: u32> embedded_storage::nor_flash::ReadNorFlash
    for FlexSpiNorStorage<'_, READ_SIZE, WRITE_SIZE, ERASE_SIZE>
{
    const READ_SIZE: usize = READ_SIZE as usize;

    fn read(&mut self, offset: u32, bytes: &mut [u8]) -> Result<(), Self::Error> {
        self.flash.read(offset, bytes).map_err(Error::ReadFailed)
    }

    fn capacity(&self) -> usize {
        self.flash.size_bytes() as usize
    }
}

impl<const READ_SIZE: u32, const WRITE_SIZE: u32, const ERASE_SIZE: u32> embedded_storage::nor_flash::NorFlash
    for FlexSpiNorStorage<'_, READ_SIZE, WRITE_SIZE, ERASE_SIZE>
{
    const WRITE_SIZE: usize = WRITE_SIZE as usize;
    const ERASE_SIZE: usize = ERASE_SIZE as usize;

    fn erase(&mut self, from: u32, to: u32) -> Result<(), Self::Error> {
        // Driver already checks alignment on start addresses, so we only check the size of the range.
        let len = to.checked_sub(from).ok_or(Error::InvalidEraseRange { from, to })?;
        if len % ERASE_SIZE != 0 {
            return Err(Error::InvalidEraseSize {
                actual: len,
                alignment: ERASE_SIZE,
            });
        }

        let sector_size = self.flash.alignment().sector_size;
        let block_size = self.flash.alignment().block_size;
        let blocks_are_sector_aligned = block_size.is_multiple_of(sector_size);

        let mut from = from;
        while from < to {
            // Erase a whole block if we can:
            //  * blocks must be sector aligned (TODO: verify this in FlexSpiNorFlash constructor and rely on it unconditionally?).
            //  * remaining erase size must be at-least a block
            //  * current offset must be block aligned
            if blocks_are_sector_aligned && to - from >= block_size && from.is_multiple_of(block_size) {
                // SAFETY: The safety requirements have been shifted to the caller of the constructor.
                unsafe {
                    self.flash.erase_block(from).map_err(Error::EraseBlockFailed)?;
                }
                from += block_size;
            // Otherwise erase a sector.
            } else {
                // SAFETY: The safety requirements have been shifted to the caller of the constructor.
                unsafe {
                    self.flash.erase_sector(from).map_err(Error::EraseSectorFailed)?;
                }
                from += sector_size;
            }
        }

        Ok(())
    }

    fn write(&mut self, offset: u32, bytes: &[u8]) -> Result<(), Self::Error> {
        let page_size = self.flash.alignment().page_size;
        let mut offset = offset;
        let mut bytes = bytes;

        // Write the data page by page.
        // The driver already checks alignment, so we only split on page boundaries.
        while !bytes.is_empty() {
            let page_end = round_down_nearest_multiple(offset, page_size) + page_size;
            let write_size = (bytes.len() as u32).min(page_end - offset);
            let (page_bytes, rest) = bytes.split_at(write_size as usize);

            // SAFETY: The safety requirements have been shifted to the caller of the constructor.
            unsafe {
                self.flash
                    .page_program(offset, page_bytes)
                    .map_err(Error::WriteFailed)?;
            }
            bytes = rest;
            offset += write_size;
        }

        Ok(())
    }
}

/// Error type for the [`FlexSpiNorStorage`] struct.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum Error {
    /// One of the const generic parameters does not match the runtime information of the driver.
    IncorrectConstGeneric(IncorrectConstGeneric),

    /// Failed to read from flash.
    ReadFailed(super::nor_flash::ReadError),

    /// Failed to erase a sector.
    EraseSectorFailed(super::nor_flash::WriteError),

    /// Failed to erase a block.
    EraseBlockFailed(super::nor_flash::WriteError),

    /// The end of the requested erase range lies before the start.
    InvalidEraseRange {
        /// The start offset of the requested erase.
        from: u32,

        /// The end offset of the requested erase.
        to: u32,
    },

    /// The size of the erase operation is not a multiple of the alignment requirement.
    InvalidEraseSize {
        /// The size of the requested erase operation.
        actual: u32,

        /// The minimum alignment requirement of erase operations.
        alignment: u32,
    },

    /// Failed to write (program) flash memory.
    WriteFailed(super::nor_flash::PageProgramError),
}

/// One of the const generic parameters does not match the runtime information of the driver.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum IncorrectConstGeneric {
    /// The generic READ_SIZE parameter does not match the read alignment specified by the driver.
    ReadSize {
        /// The given READ_SIZE.
        given: u32,

        /// The read alignment from the FlexSPI driver.
        driver: u32,
    },

    /// The generic WRITE_SIZE parameter does not match the write alignment specified by the driver.
    WriteSize {
        /// The given WRITE_SIZE.
        given: u32,

        /// The read alignment from the FlexSPI driver.
        driver: u32,
    },

    /// The generic ERASE_SIZE parameter does not match the sector size specified by the driver.
    ///
    /// A sector is the smallest region that can be erased.
    EraseSize {
        /// The given ERASE_SIZE
        given: u32,

        /// The sector size from the FlexSPI driver.
        driver: u32,
    },
}

impl From<IncorrectConstGeneric> for Error {
    fn from(value: IncorrectConstGeneric) -> Self {
        Self::IncorrectConstGeneric(value)
    }
}

fn check_const_size_parameter(given: u32, driver: u32) -> bool {
    // The given const param must be a multiple of the driver value (but it can not be zero if the driver value is non-zero).
    given >= driver && given.is_multiple_of(driver)
}

impl embedded_storage::nor_flash::NorFlashError for Error {
    fn kind(&self) -> embedded_storage::nor_flash::NorFlashErrorKind {
        use embedded_storage::nor_flash::NorFlashErrorKind;

        match self {
            Self::IncorrectConstGeneric(_) => NorFlashErrorKind::Other,
            Self::InvalidEraseRange { .. } => NorFlashErrorKind::NotAligned,
            Self::InvalidEraseSize { .. } => NorFlashErrorKind::NotAligned,
            Self::ReadFailed(e) => read_error_kind(e),
            Self::EraseSectorFailed(e) => write_error_kind(e),
            Self::EraseBlockFailed(e) => write_error_kind(e),
            Self::WriteFailed(e) => page_program_error_kind(e),
        }
    }
}

fn read_error_kind(error: &super::nor_flash::ReadError) -> embedded_storage::nor_flash::NorFlashErrorKind {
    use embedded_storage::nor_flash::NorFlashErrorKind;
    match error {
        super::nor_flash::ReadError::Misaligned(_) => NorFlashErrorKind::NotAligned,
        super::nor_flash::ReadError::Command(_) => NorFlashErrorKind::Other,
        super::nor_flash::ReadError::NotEnoughData(_) => NorFlashErrorKind::Other,
    }
}

fn write_error_kind(error: &super::nor_flash::WriteError) -> embedded_storage::nor_flash::NorFlashErrorKind {
    use embedded_storage::nor_flash::NorFlashErrorKind;
    match error {
        super::nor_flash::WriteError::Misaligned(_) => NorFlashErrorKind::NotAligned,
        super::nor_flash::WriteError::ReadStatus(_) => NorFlashErrorKind::Other,
        super::nor_flash::WriteError::WriteInProgress => NorFlashErrorKind::Other,
        super::nor_flash::WriteError::SetWriteEnable(_) => NorFlashErrorKind::Other,
        super::nor_flash::WriteError::WriteEnableFailed => NorFlashErrorKind::Other,
        super::nor_flash::WriteError::Command(_) => NorFlashErrorKind::Other,
    }
}

fn page_program_error_kind(
    error: &super::nor_flash::PageProgramError,
) -> embedded_storage::nor_flash::NorFlashErrorKind {
    use embedded_storage::nor_flash::NorFlashErrorKind;
    match error {
        super::nor_flash::PageProgramError::PageBoundaryCrossed(_) => NorFlashErrorKind::NotAligned,
        super::nor_flash::PageProgramError::WriteFailed(e) => write_error_kind(e),
    }
}

#[must_use]
fn round_down_nearest_multiple(value: u32, multiple: u32) -> u32 {
    value / multiple * multiple
}
