//! RTC DateTime driver.

use core::marker::PhantomData;

use embedded_mcu_hal::time::{Datetime, DatetimeClock, DatetimeClockError};
use embedded_mcu_hal::{Nvram, NvramStorage};

use crate::{Peri, pac, peripherals};

/// Number of general-purpose registers in the RTC NVRAM
// If you need to consume some of these registers for internal HAL use, write a feature flag that reduces this count,
// and use registers starting from the end of the array (i.e. use gpreg7 first) so we don't need to renumber based on
// which feature flags are enabled.
const IMXRT_GPREG_COUNT: usize = 8;

/// Returns a reference to the RTC peripheral's register block.
/// SAFETY: The caller is responsible for ensuring that no individual register is touched by multiple threads/interrupts at the same time.
unsafe fn rtc() -> &'static pac::rtc::RegisterBlock {
    unsafe { &*pac::Rtc::ptr() }
}

/// Represents the real-time clock (RTC) peripheral and provides access to its datetime clock and NVRAM functionality.
pub struct Rtc<'r> {
    _p: Peri<'r, peripherals::RTC>,
    clock: RtcDatetimeClock<'r>,
    nvram: RtcNvram<'r>,
}

impl<'r> Rtc<'r> {
    /// Create a new `Rtc` instance, taking ownership of the RTC peripheral.
    pub fn new(rtc: Peri<'r, peripherals::RTC>) -> Self {
        Self {
            _p: rtc,
            clock: RtcDatetimeClock { _phantom: PhantomData },

            // SAFETY: Only one instance of Rtc can be created because we consume the Peri<RTC> singleton, which ensures that we only create one instance of RtcNvram.
            nvram: unsafe { RtcNvram::new() },
        }
    }

    /// Obtains a clock and NVRAM wrapper from the Rtc peripheral.
    pub fn split(&'r mut self) -> (&'r mut RtcDatetimeClock<'r>, &'r mut RtcNvram<'r>) {
        (&mut self.clock, &mut self.nvram)
    }
}

/// Implementation of the `DatetimeClock` trait - allows setting and getting the current date and time in structured format.
pub struct RtcDatetimeClock<'r> {
    _phantom: PhantomData<&'r Peri<'r, peripherals::RTC>>,
}

/// Implementation for `RtcDatetime`.
impl<'r> RtcDatetimeClock<'r> {
    /// Set the datetime in seconds since the Unix time epoch (January 1, 1970).
    fn set_datetime_in_secs(&self, secs: u64) -> Result<(), DatetimeClockError> {
        // SAFETY: We have sole ownership of the RTC peripheral and we enforce that there is only one instance of RtcDatetime,
        //         so we can safely access it as long as it's always from an object that has the handle-to-RTC.
        let r = unsafe { rtc() };

        // This won't fail until 2106, when we'll overflow the 32-bit counter.
        let secs: u32 = secs.try_into().map_err(|_| DatetimeClockError::UnsupportedDatetime)?;
        r.ctrl().modify(|_r, w| w.rtc_en().disable());
        r.count().write(|w| unsafe { w.bits(secs) });
        r.ctrl().modify(|_r, w| w.rtc_en().enable());

        Ok(())
    }

    /// Get the datetime as seconds since the Unix time epoch (January 1, 1970).
    fn get_datetime_in_secs(&self) -> Result<u64, DatetimeClockError> {
        // SAFETY: We have sole ownership of the RTC peripheral and we enforce that there is only one instance of RtcDatetime,
        //         so we can safely access it as long as it's always from an object that has the handle-to-RTC.
        let r = unsafe { rtc() };

        if r.ctrl().read().rtc_en().bit_is_clear() {
            return Err(DatetimeClockError::NotEnabled);
        }

        // Wait for the count to stabilize - it can change in the middle of a read, so we need to read it twice and make sure they match.
        let secs = loop {
            let secs1 = r.count().read().bits();
            let secs2 = r.count().read().bits();
            if secs1 == secs2 {
                break secs1;
            }
        };

        Ok(secs.into())
    }
}

impl DatetimeClock for RtcDatetimeClock<'_> {
    /// Returns the current structured date and time.
    fn get_current_datetime(&self) -> Result<Datetime, DatetimeClockError> {
        Ok(Datetime::from_unix_time_seconds(self.get_datetime_in_secs()?))
    }

    /// Sets the current structured date and time.
    fn set_current_datetime(&mut self, datetime: &Datetime) -> Result<(), DatetimeClockError> {
        self.set_datetime_in_secs(datetime.to_unix_time_seconds())
    }

    // TODO As currently implemented, we only return times with 1s resolution.  However, the hardware is capable of 1KHz
    //      resolution in some configurations.  In the future, we may consider adding a feature flag to enable setting
    //      timestamps with 1KHz resolution, but we don't currently have a use case for that.
    //
    fn max_resolution_hz(&self) -> u32 {
        1
    }
}

/// Represents a storage cell in the RTC's general-purpose NVRAM registers.
pub struct RtcNvramStorage<'r> {
    /// Which general-purpose register index this storage cell represents.
    gpreg_idx: usize,
    _phantom: PhantomData<&'r Peri<'r, peripherals::RTC>>,
}

impl<'r> NvramStorage<'r, u32> for RtcNvramStorage<'r> {
    /// Reads the value from the NVRAM storage cell.
    fn read(&self) -> u32 {
        // SAFETY: If only a single instance of NvramStorage exists for a given gpreg, we can safely access it.
        //         The function that constructs us is responsible for enforcing that only a single instance exists.
        unsafe { rtc() }.gpreg(self.gpreg_idx).read().gpdata().bits()
    }

    /// Writes a value to the NVRAM storage cell.
    fn write(&mut self, value: u32) {
        // SAFETY: If only a single instance of NvramStorage exists for a given gpreg, we can safely access it.
        //         The function that constructs us is responsible for enforcing that only a single instance exists.
        //         General-purpose registers have no side effects and are not shared between multiple logical fields, so bits() is safe.
        unsafe { rtc() }
            .gpreg(self.gpreg_idx)
            .write(|w| unsafe { w.gpdata().bits(value) });
    }
}

impl<'r> RtcNvramStorage<'r> {
    /// Creates a new `RtcNvramStorage` instance for the specified register index.
    /// SAFETY: The caller is responsible for ensuring that only one RtcNvramStorage instance is created for each register index.
    unsafe fn new(gpreg_idx: usize) -> Self {
        Self {
            gpreg_idx: match gpreg_idx {
                0..IMXRT_GPREG_COUNT => gpreg_idx,
                _ => panic!("Invalid GPREG index: {}", gpreg_idx),
            },
            _phantom: PhantomData,
        }
    }
}

/// Represents the RTC's NVRAM storage, which consists of 8 general-purpose registers (GPREGs).
pub struct RtcNvram<'r> {
    storage: [RtcNvramStorage<'r>; IMXRT_GPREG_COUNT],
}

impl<'r> RtcNvram<'r> {
    /// Creates a representation of the RTC's NVRAM storage.
    /// SAFETY: It is only safe to construct an RtcNvram once, because it contains a static reference to the RTC peripheral.
    unsafe fn new() -> Self {
        Self {
            storage: core::array::from_fn(|gpreg_idx| {
                // SAFETY: We ensure that we only create one instance per index. Our caller is responsible
                //         for only calling this once, and this function is marked unsafe to signal that
                //         they must enforce that.
                unsafe { RtcNvramStorage::new(gpreg_idx) }
            }),
        }
    }
}

impl<'r> Nvram<'r, RtcNvramStorage<'r>, u32, IMXRT_GPREG_COUNT> for RtcNvram<'r> {
    fn storage(&'r mut self) -> &'r mut [RtcNvramStorage<'r>; IMXRT_GPREG_COUNT] {
        // SAFETY: We have sole ownership of the RTC peripheral and we enforce that there is only one instance of RtcDatetime,
        //         so we can safely access it as long as it's always from an object that has the handle-to-RTC.
        &mut self.storage
    }
}
