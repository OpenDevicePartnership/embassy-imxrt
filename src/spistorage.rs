use embassy_hal_internal::Peripheral;
use embedded_storage::nor_flash::{
    ErrorType, NorFlash as BlockingNorFlash, NorFlashError, NorFlashErrorKind, ReadNorFlash as BlockingReadNorFlash,
};

/// Driver mode.
#[allow(private_bounds)]
mod sealed {
    /// simply seal a trait
    pub trait Sealed {}
}

impl<T> sealed::Sealed for T {}

struct Info {
    regs: &'static crate::pac::flexspi::RegisterBlock,
}

trait SealedInstance {
    fn info() -> Info;
}
pub trait Mode: sealed::Sealed {}

/// Blocking mode.
pub struct Blocking;
impl Mode for Blocking {}

/// Async mode.
pub struct Async;
impl Mode for Async {}

pub trait Instance: SealedInstance + Peripheral<P = Self> + 'static + Send {}

impl SealedInstance for crate::peripherals::FLEXSPI {
    fn info() -> Info {
        Info {
            regs: unsafe { &*crate::pac::Flexspi::ptr() },
        }
    }
}

#[derive(Debug)]
pub struct FlashStorageErrorOther;
impl<M: Mode> ErrorType for SpiStorage<M> {
    type Error = FlashStorageErrorOther;
}

impl NorFlashError for FlashStorageErrorOther {
    fn kind(&self) -> embedded_storage::nor_flash::NorFlashErrorKind {
        NorFlashErrorKind::Other
    }
}

impl BlockingReadNorFlash for SpiStorage<Blocking> {
    const READ_SIZE: usize = 1;
    fn read(&mut self, offset: u32, bytes: &mut [u8]) -> Result<(), Self::Error> {
        Ok(())
    }
    fn capacity(&self) -> usize {
        // Return the capacity of the flash
        0
    }
}

impl BlockingNorFlash for SpiStorage<Blocking> {
    const WRITE_SIZE: usize = 256;
    const ERASE_SIZE: usize = 4096;

    fn erase(&mut self, from: u32, to: u32) -> Result<(), Self::Error> {
        // Erase data in blocking mode
        panic!("Erase operation is not implemented for Data Port. Please use Command Port for erase operation");
    }

    fn write(&mut self, offset: u32, bytes: &[u8]) -> Result<(), Self::Error> {
        Ok(())
    }
}

pub struct SpiStorage<M: Mode> {
    info: Info,
    phantom: core::marker::PhantomData<M>,
}

impl crate::storage::StorageCmdPort<Blocking> for SpiStorage<Blocking> {}
impl crate::storage::StorageDataPort<Blocking> for SpiStorage<Blocking> {}
impl crate::storage::StorageDriver<Blocking> for SpiStorage<Blocking> {}

impl SpiStorage<Blocking> {
    pub fn new_blocking<T: Instance>(_spiinstance: T) -> Self {
        let info = T::info();
        Self {
            info,
            phantom: core::marker::PhantomData,
        }
    }
}
