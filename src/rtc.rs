//! RTC DateTime driver.

use core::marker::PhantomData;

use embassy_hal_internal::interrupt::InterruptExt;
use embassy_sync::waitqueue::AtomicWaker;
use embedded_mcu_hal::time::{Datetime, DatetimeClock, DatetimeClockError};
use embedded_mcu_hal::{Nvram, NvramStorage};

use crate::{Peri, interrupt, pac, peripherals};

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

/// Static waker for RTC alarm interrupts.
///
/// This is a **global** `AtomicWaker` used by the RTC alarm interrupt handler to
/// wake an asynchronous task waiting for the next alarm.
///
/// # Concurrency and usage constraints
///
/// - Only **one** alarm can be pending at a time when using this waker. Registering
///   a new waker (e.g. by polling a different future that also uses this waker)
///   will replace the previously registered waker.
/// - This value is a low-level primitive and does **not** itself represent a
///   future. Consumers are expected to implement their own `Future` wrapper
///   (for example, a type like `RtcAlarm`) that:
///   - registers its task's waker with `RTC_ALARM_WAKER`,
///   - programs/configures the hardware alarm, and
///   - completes when the alarm interrupt fires and calls `wake()`.
///
/// Using this waker directly from multiple independent alarm abstractions at the
/// same time is not supported and may lead to lost wakeups.
static RTC_ALARM_WAKER: AtomicWaker = AtomicWaker::new();

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

/// Implementation for `RtcDatetimeClock`.
impl<'r> RtcDatetimeClock<'r> {
    /// Set the datetime in seconds since the Unix time epoch (January 1, 1970).
    fn set_datetime_in_secs(&mut self, secs: u64) -> Result<(), DatetimeClockError> {
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

    /// Sets the RTC wake alarm via the match register to wake after the given time in seconds.
    ///
    /// WARNING:
    /// * Only one RTC alarm can be present in the system at a time.
    ///   Setting a new alarm will cancel an existing one.
    /// * After an alarm is set, changing the RTC time will NOT adjust the alarm accordingly.
    ///   The alarm will still fire at the originally configured absolute time value
    ///   in the hardware register.
    ///
    /// # Parameters
    ///
    /// * `secs_from_now` - A relative offset in seconds from the current RTC time
    ///   after which the alarm should fire.
    ///
    /// # Returns
    ///
    /// `u64` - The absolute RTC time in seconds at which the alarm is scheduled to fire.
    pub fn set_alarm_from_now(&mut self, secs_from_now: u64) -> Result<u64, DatetimeClockError> {
        let secs = self
            .get_datetime_in_secs()?
            .checked_add(secs_from_now)
            .ok_or(DatetimeClockError::UnsupportedDatetime)?;
        self.set_alarm_at(secs)?;
        Ok(secs)
    }

    /// Sets the RTC wake alarm via the match register to wake at the given Datetime.
    ///
    /// WARNING:
    /// * Only one RTC alarm can be present in the system at a time.
    ///   Setting a new alarm will cancel an existing one.
    /// * After an alarm is set, changing the RTC time will NOT adjust the alarm accordingly.
    ///   The alarm will still fire at the originally configured absolute time value
    ///   in the hardware register.
    ///
    /// # Parameters
    ///
    /// * `alarm_time` - An absolute RTC time in seconds at which the alarm should fire.
    ///
    /// # Returns
    ///
    /// `u64` - The absolute RTC time in seconds at which the alarm is scheduled to fire.
    ///         This is the `alarm_time` argument converted into u64
    pub fn set_alarm_at(&mut self, unix_time_secs: u64) -> Result<(), DatetimeClockError> {
        // Check that the alarm end time is not in the past
        if self.get_datetime_in_secs()? > unix_time_secs {
            return Err(DatetimeClockError::UnsupportedDatetime);
        }

        // Convert seconds to u32 to interface with 32 bit hardware RTC
        let secs: u32 = unix_time_secs
            .try_into()
            .map_err(|_| DatetimeClockError::UnsupportedDatetime)?;

        // SAFETY: We have sole ownership of the RTC peripheral and we enforce that there is only one instance of RtcDatetime,
        //         so we can safely access it as long as it's always from an object that has the handle-to-RTC.
        //         The handle was retrieved in get_datetime_in_secs(), which has since completed and gone out of scope.
        let r = unsafe { rtc() };

        critical_section::with(|_cs| {
            // Clear any pending alarm interrupt
            r.ctrl().modify(|_r, w| w.alarm1hz().set_bit());

            // Set the match register with the new time
            r.match_().write(|w| unsafe { w.bits(secs) });

            // Enable the 1Hz timer alarm for deep power down
            r.ctrl().modify(|_r, w| w.alarmdpd_en().set_bit());

            // Enable RTC interrupt
            interrupt::RTC.unpend();
            unsafe {
                interrupt::RTC.enable();
            }
        });

        Ok(())
    }

    /// Clears the RTC 1Hz alarm by resetting related registers
    pub fn clear_alarm(&mut self) {
        // SAFETY: We have sole ownership of the RTC peripheral and we enforce that there is only one instance of RtcDatetime,
        //         so we can safely access it as long as it's always from an object that has the handle-to-RTC.
        let r = unsafe { rtc() };

        critical_section::with(|_cs| {
            // Disable the 1Hz timer alarm for deep power down
            r.ctrl().modify(|_r, w| w.alarmdpd_en().clear_bit());

            // Clear the Alarm1Hz match status register
            // Note: "Writing a 1 clears this bit"
            r.ctrl().modify(|_r, w| w.alarm1hz().set_bit());

            // Resets the match register to its default
            r.match_().write(|w| unsafe { w.bits(u32::MAX) });

            // Disable RTC interrupt
            interrupt::RTC.disable();
        });
    }

    /// Registers a waker to be notified when the RTC alarm fires.
    ///
    /// This method forwards the waker to the internal static [`AtomicWaker`] used
    /// by the RTC interrupt handler. When the alarm interrupt fires, the registered
    /// waker will be called.
    ///
    /// This is typically called from a `Future::poll` implementation when waiting
    /// for an RTC alarm to expire. Only one waker can be registered at a time;
    /// calling this method replaces any previously registered waker.
    ///
    /// # Parameters
    ///
    /// * `waker` - The waker to be notified when the alarm fires
    pub fn register_alarm_waker(&self, waker: &core::task::Waker) {
        RTC_ALARM_WAKER.register(waker);
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

    fn clear_storage(&mut self) {
        for storage in self.storage.iter_mut() {
            storage.write(0);
        }
    }

    fn dump_storage(&self) -> [u32; IMXRT_GPREG_COUNT] {
        self.storage.each_ref().map(|storage| storage.read())
    }
}

/// RTC interrupt handler
/// This is called when the RTC alarm fires
#[cfg(feature = "rt")]
#[interrupt]
fn RTC() {
    // SAFETY: This is called from an interrupt context, but we only read/write the CTRL register
    //         which is safe to access from multiple contexts with proper atomic operations
    let r = unsafe { rtc() };

    // Check if this is an alarm interrupt
    if r.ctrl().read().alarm1hz().bit_is_set() {
        // Clear any pending RTC interrupt before waking tasks to avoid spurious retriggers
        interrupt::RTC.unpend();

        // Disable RTC interrupt
        interrupt::RTC.disable();

        // Disable the 1Hz timer alarm for deep power down
        r.ctrl().modify(|_r, w| w.alarmdpd_en().clear_bit());

        // Clear the alarm interrupt flag by writing 1 to it
        r.ctrl().modify(|_r, w| w.alarm1hz().set_bit());

        // Wake any task waiting on the alarm
        RTC_ALARM_WAKER.wake();
    }
}
