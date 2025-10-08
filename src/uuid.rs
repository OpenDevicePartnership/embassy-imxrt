//! Universally Unique Identifier (UUID)

/// NXP RT6xx UUID
pub struct Uuid {
    uuid0: u32,
    uuid1: u32,
    uuid2: u32,
    uuid3: u32,
}

impl Uuid {
    /// Read MCU on-die UUID.
    pub fn read() -> Self {
        let sysctl0 = unsafe { &*crate::pac::Sysctl0::ptr() };

        let uuid0 = sysctl0.uuid(0).read().bits();
        let uuid1 = sysctl0.uuid(1).read().bits();
        let uuid2 = sysctl0.uuid(2).read().bits();
        let uuid3 = sysctl0.uuid(3).read().bits();

        Self {
            uuid0,
            uuid1,
            uuid2,
            uuid3,
        }
    }

    /// Returns the memory representation of this UUID as a `u128`
    pub fn to_u128(self) -> u128 {
        u128::from(self.uuid3) << 96
            | u128::from(self.uuid2) << 64
            | u128::from(self.uuid1) << 32
            | u128::from(self.uuid0)
    }

    /// Returns the memory representation of this UUID as native-endian bytes
    pub fn to_ne_bytes(self) -> [u8; 16] {
        self.to_u128().to_ne_bytes()
    }

    /// Returns the memory representation of this UUID as big-endian bytes
    pub fn to_be_bytes(self) -> [u8; 16] {
        self.to_u128().to_be_bytes()
    }

    /// Returns the memory representation of this UUID as little-endian bytes
    pub fn to_le_bytes(self) -> [u8; 16] {
        self.to_u128().to_le_bytes()
    }
}
