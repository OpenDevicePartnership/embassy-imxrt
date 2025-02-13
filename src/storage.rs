use embedded_storage::nor_flash::{
    ErrorType, NorFlash as BlockingNorFlash, NorFlashError, NorFlashErrorKind, ReadNorFlash as BlockingReadNorFlash,
};

/// Storage Data Port Trait
pub trait StorageDataPort<Blocking>: BlockingNorFlash + BlockingReadNorFlash {}

/// Storage Command Port Trait
pub trait StorageCmdPort<Blocking>: BlockingNorFlash + BlockingReadNorFlash {
    fn lock_flash() -> bool {
        // Lock the storage
        false
    }

    fn unlock_flash() -> bool {
        // Unlock the storage
        false
    }

    fn read_jedec_id() -> [u8; 3] {
        // Read JEDEC ID
        [0, 0, 0]
    }

    fn power_down() -> bool {
        // Power down the storage
        false
    }

    fn power_up() -> bool {
        // Power up the storage
        false
    }
}

/// Storage Driver
pub trait StorageDriver<Blocking>: StorageDataPort<Blocking> + StorageCmdPort<Blocking> {}
