use core::cell::{Cell, RefCell};
use core::sync::atomic::{compiler_fence, AtomicU32, Ordering};

use critical_section::CriticalSection;
use embassy_sync::blocking_mutex::raw::CriticalSectionRawMutex;
use embassy_sync::blocking_mutex::Mutex;
use embassy_time_driver::Driver;
use embassy_time_queue_utils::Queue;

use crate::interrupt::InterruptExt;
use crate::{interrupt, pac, peripherals, Peri};

fn rtc() -> &'static pac::rtc::RegisterBlock {
    unsafe { &*pac::Rtc::ptr() }
}

/// Calculate the timestamp from the period count and the tick count.
///
/// To get `now()`, `period` is read first, then `counter` is read. If the counter value matches
/// the expected range for the `period` parity, we're done. If it doesn't, this means that
/// a new period start has raced us between reading `period` and `counter`, so we assume the `counter` value
/// corresponds to the next period.
///
/// the 1kHz RTC counter is 16 bits and RTC doesn't have separate compare channels,
/// so using a 32 bit GPREG0-2 as counter, compare, and int_en
/// `period` is a 32bit integer, gpreg 'counter' is 31 bits plus the parity bit for overflow detection
fn calc_now(period: u32, counter: u32) -> u64 {
    ((period as u64) << 31) + ((counter ^ ((period & 1) << 31)) as u64)
}

struct AlarmState {
    timestamp: Cell<u64>,
}

unsafe impl Send for AlarmState {}

impl AlarmState {
    const fn new() -> Self {
        Self {
            timestamp: Cell::new(u64::MAX),
        }
    }
}

struct TimerDriver {
    /// Number of 2^31 periods elapsed since boot.
    period: AtomicU32,
    /// Timestamp at which to fire alarm. u64::MAX if no alarm is scheduled.
    alarms: Mutex<CriticalSectionRawMutex, AlarmState>,
    queue: Mutex<CriticalSectionRawMutex, RefCell<Queue>>,
}

embassy_time_driver::time_driver_impl!(static DRIVER: TimerDriver = TimerDriver {
    period: AtomicU32::new(0),
    alarms:  Mutex::const_new(CriticalSectionRawMutex::new(), AlarmState::new()),
    queue: Mutex::new(RefCell::new(Queue::new())),
});

impl TimerDriver {
    /// Access the GPREG0 register to use it as a 31-bit counter.
    #[inline]
    fn counter_reg(&self) -> &pac::rtc::Gpreg {
        rtc().gpreg(0)
    }

    /// Access the GPREG1 register to use it as a compare register for triggering alarms.
    #[inline]
    fn compare_reg(&self) -> &pac::rtc::Gpreg {
        rtc().gpreg(1)
    }

    /// Access the GPREG2 register to use it to enable or disable interrupts (int_en).
    #[inline]
    fn int_en_reg(&self) -> &pac::rtc::Gpreg {
        rtc().gpreg(2)
    }

    fn init(&'static self, irq_prio: crate::interrupt::Priority) {
        let r = rtc();
        // enable RTC int (1kHz since subsecond doesn't generate an int)
        r.ctrl().modify(|_r, w| w.rtc1khz_en().set_bit());
        // TODO: low power support. line above is leaving out write to .wakedpd_en().set_bit())
        // which enables wake from deep power down

        // safety: Writing to the gregs is always considered unsafe, gpreg1 is used
        // as a compare register for triggering an alarm so to avoid unnecessary triggers
        // after initialization, this is set to 0x:FFFF_FFFF
        self.compare_reg().write(|w| unsafe { w.gpdata().bits(u32::MAX) });
        // safety: writing a value to the 1kHz RTC wake counter is always considered unsafe.
        // The following loads 10 into the count-down timer.
        r.wake().write(|w| unsafe { w.bits(0xA) });
        interrupt::RTC.set_priority(irq_prio);
        unsafe { interrupt::RTC.enable() };
    }

    #[cfg(feature = "rt")]
    fn on_interrupt(&self) {
        let r = rtc();
        // This interrupt fires every 10 ticks of the 1kHz RTC high res clk and adds
        // 10 to the 31 bit counter gpreg0. The 32nd bit is used for parity detection
        // This is done to avoid needing to calculate # of ticks spent on interrupt
        // handlers to recalibrate the clock between interrupts
        //
        // TODO: this is admittedly not great for power that we're generating this
        // many interrupts, will probably get updated in future iterations.
        if r.ctrl().read().wake1khz().bit_is_set() {
            r.ctrl().modify(|_r, w| w.wake1khz().set_bit());
            // safety: writing a value to the 1kHz RTC wake counter is always considered unsafe.
            // The following reloads 10 into the count-down timer after it triggers an int.
            // The countdown begins anew after the write so time can continue to be measured.
            r.wake().write(|w| unsafe { w.bits(0xA) });
            if (self.counter_reg().read().bits() + 0xA) > 0x8000_0000 {
                // if we're going to "overflow", increase the period
                self.next_period();
                let rollover_diff = 0x8000_0000 - (self.counter_reg().read().bits() + 0xA);
                // safety: writing to gpregs is always considered unsafe. In order to
                // not "lose" time when incrementing the period, gpreg0, the extended
                // counter, is restarted at the # of ticks it would overflow by
                self.counter_reg().write(|w| unsafe { w.bits(rollover_diff) });
            } else {
                self.counter_reg().modify(|r, w| unsafe { w.bits(r.bits() + 0xA) });
            }
        }

        critical_section::with(|cs| {
            // gpreg2 as an "int_en" set by next_period(). This is
            // 1 when the timestamp for the alarm deadline expires
            // before the counter register overflows again.
            if self.int_en_reg().read().gpdata().bits() == 1 {
                // gpreg0 is our extended counter register, check if
                // our counter is larger than the compare value
                if self.counter_reg().read().bits() > self.compare_reg().read().bits() {
                    self.trigger_alarm(cs);
                }
            }
        })
    }

    #[cfg(feature = "rt")]
    fn next_period(&self) {
        critical_section::with(|cs| {
            let period = self
                .period
                .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |p| Some(p + 1))
                .unwrap_or_else(|p| {
                    trace!("Unable to increment period. Time is now inaccurate");
                    // TODO: additional error handling beyond logging

                    p
                });
            let t = (period as u64) << 31;

            let alarm = &self.alarms.borrow(cs);
            let at = alarm.timestamp.get();
            if at < t + 0xc000_0000 {
                // safety: writing to gpregs is always unsafe, gpreg2 is an alarm
                // enable. If the alarm must trigger within the next period, then
                // just enable it. `set_alarm` has already set the correct CC val.
                self.int_en_reg().write(|w| unsafe { w.gpdata().bits(1) });
            }
        })
    }

    #[must_use]
    fn set_alarm(&self, cs: CriticalSection, timestamp: u64) -> bool {
        let alarm = self.alarms.borrow(cs);
        alarm.timestamp.set(timestamp);

        let t = self.now();
        if timestamp <= t {
            // safety: Writing to the gpregs is always unsafe, gpreg2 is
            // always just used as the alarm enable for the timer driver.
            // If alarm timestamp has passed the alarm will not fire.
            // Disarm the alarm and return `false` to indicate that.
            self.int_en_reg().write(|w| unsafe { w.gpdata().bits(0) });

            alarm.timestamp.set(u64::MAX);

            return false;
        }

        // If it hasn't triggered yet, setup it by writing to the compare field
        // An alarm can be delayed, but this is allowed by the Alarm trait contract.
        // What's not allowed is triggering alarms *before* their scheduled time,
        let safe_timestamp = timestamp.max(t + 10); //t+3 was done for nrf chip, choosing 10

        // safety: writing to the gregs is always unsafe. When a new alarm is set,
        // the compare register, gpreg1, is set to the last 31 bits of the timestamp
        // as the 32nd and final bit is used for the parity check in `next_period`
        // `period` will be used for the upper bits in a timestamp comparison.
        self.compare_reg()
            .modify(|_r, w| unsafe { w.bits(safe_timestamp as u32 & 0x7FFF_FFFF) });

        // The following checks that the difference in timestamp is less than the overflow period
        let diff = timestamp - t;
        if diff < 0xc000_0000 {
            // this is 0b11 << (30). NRF chip used 23 bit periods and checked against 0b11<<22

            // safety: writing to the gpregs is always unsafe. If the alarm
            // must trigger within the next period, set the "int enable"
            self.int_en_reg().write(|w| unsafe { w.gpdata().bits(1) });
        } else {
            // safety: writing to the gpregs is always unsafe. If alarm must trigger
            // some time after the current period, too far in the future, don't setup
            // the alarm enable, gpreg2, yet. It will be setup later by `next_period`.
            self.int_en_reg().write(|w| unsafe { w.gpdata().bits(0) });
        }

        true
    }

    #[cfg(feature = "rt")]
    fn trigger_alarm(&self, cs: CriticalSection) {
        let mut next = self.queue.borrow(cs).borrow_mut().next_expiration(self.now());
        while !self.set_alarm(cs, next) {
            next = self.queue.borrow(cs).borrow_mut().next_expiration(self.now());
        }
    }
}

impl Driver for TimerDriver {
    fn now(&self) -> u64 {
        // `period` MUST be read before `counter`, see comment at the top for details.
        let period = self.period.load(Ordering::Acquire);
        compiler_fence(Ordering::Acquire);
        let counter = self.counter_reg().read().bits();
        calc_now(period, counter)
    }

    fn schedule_wake(&self, at: u64, waker: &core::task::Waker) {
        critical_section::with(|cs| {
            let mut queue = self.queue.borrow(cs).borrow_mut();

            if queue.schedule_wake(at, waker) {
                let mut next = queue.next_expiration(self.now());
                while !self.set_alarm(cs, next) {
                    next = queue.next_expiration(self.now());
                }
            }
        })
    }
}

/// Represents a date and time.
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct Datetime {
    /// The year component of the date.
    pub year: u16,
    /// The month component of the date (1-12).
    pub month: u8,
    /// The day component of the date (1-31).
    pub day: u8,
    /// The hour component of the time (0-23).
    pub hour: u8,
    /// The minute component of the time (0-59).
    pub minute: u8,
    /// The second component of the time (0-59).
    pub second: u8,
}

/// Default implementation for `Datetime`.
impl Default for Datetime {
    fn default() -> Self {
        Datetime {
            year: 1970,
            month: 1,
            day: 1,
            hour: 0,
            minute: 0,
            second: 0,
        }
    }
}
/// Represents a real-time clock datetime.
pub struct RtcDatetime<'r> {
    _p: Peri<'r, peripherals::RTC>,
}
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[derive(PartialEq)]
/// Represents the result of a datetime validation.
pub enum Error {
    /// The year is invalid.
    InvalidYear,
    /// The month is invalid.
    InvalidMonth,
    /// The day is invalid.
    InvalidDay,
    /// The hour is invalid.
    InvalidHour,
    /// The minute is invalid.
    InvalidMinute,
    /// The second is invalid.
    InvalidSecond,
    /// RTC is not enabled.
    RTCNotEnabled,
}

/// Implementation for `RtcDatetime`.
impl<'r> RtcDatetime<'r> {
    /// Create a new `RtcDatetime` instance.
    pub fn new(rtc: Peri<'r, peripherals::RTC>) -> Self {
        Self { _p: rtc }
    }
    /// check valid datetime.
    pub fn is_valid_datetime(&self, time: &Datetime) -> Result<(), Error> {
        // Validate year
        if time.year < 1970 {
            return Err(Error::InvalidYear);
        }

        // Validate month
        if time.month < 1 || time.month > 12 {
            return Err(Error::InvalidMonth);
        }

        // Validate day
        if time.day < 1 {
            return Err(Error::InvalidDay);
        }

        match time.month {
            1 | 3 | 5 | 7 | 8 | 10 | 12 => {
                if time.day > 31 {
                    return Err(Error::InvalidDay);
                }
            }
            4 | 6 | 9 | 11 => {
                if time.day > 30 {
                    return Err(Error::InvalidDay);
                }
            }
            2 => {
                if self.is_leap_year(time.year) {
                    if time.day > 29 {
                        return Err(Error::InvalidDay);
                    }
                } else if time.day > 28 {
                    return Err(Error::InvalidDay);
                }
            }
            _ => return Err(Error::InvalidDay),
        }

        // Validate hour
        if time.hour > 23 {
            return Err(Error::InvalidHour);
        }

        // Validate minute
        if time.minute > 59 {
            return Err(Error::InvalidMinute);
        }

        // Validate second
        if time.second > 59 {
            return Err(Error::InvalidSecond);
        }
        Ok(())
    }

    /// Check if a year is a leap year.
    fn is_leap_year(&self, year: u16) -> bool {
        (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
    }

    /// Convert a datetime to seconds since 1970-01-01 00:00:00.
    pub fn convert_datetime_to_secs(&self, datetime: &Datetime) -> u32 {
        let mut days: u32 = 0;
        let mut year: u16 = datetime.year;
        let mut month: u8 = datetime.month;
        let day: u32 = datetime.day as u32;

        // Calculate days from 1970 to the current year
        while year > 1970 {
            days += 365;
            if self.is_leap_year(year) {
                days += 1;
            }
            year -= 1;
        }

        // Calculate days from January to the current month
        let days_in_month = [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30];
        while month > 1 {
            days += days_in_month[month as usize - 1];
            if month == 2 && self.is_leap_year(datetime.year) {
                days += 1;
            }
            month -= 1;
        }

        // Calculate days from the first day of the month to the current day
        days += day - 1;

        // Calculate seconds from the first day of the month to the current day
        let secs = datetime.second as u32 + datetime.minute as u32 * 60 + datetime.hour as u32 * 3600;

        days * 86400 + secs
    }

    /// Convert seconds since 1970-01-01 00:00:00 to a datetime.
    fn convert_secs_to_datetime(&self, secs: u32) -> Datetime {
        let mut days = secs / 86400;
        let mut secs = secs % 86400;

        let mut year = 1970;
        let mut month = 1;
        let mut day = 1;

        // Calculate year
        while days >= 365 {
            if self.is_leap_year(year) {
                if days >= 366 {
                    days -= 366;
                } else {
                    break;
                }
            } else {
                days -= 365;
            }
            year += 1;
        }

        // Calculate month
        let days_in_month = [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30];
        while days >= days_in_month[month as usize] {
            if month == 2 && self.is_leap_year(year) {
                if days >= 29 {
                    days -= 29;
                } else {
                    break;
                }
            } else {
                days -= days_in_month[month as usize];
            }
            month += 1;
        }

        // Calculate day
        day += days;

        // Calculate hour, minute, and second
        let hour = secs / 3600;
        secs %= 3600;
        let minute = secs / 60;
        let second = secs % 60;

        Datetime {
            year,
            month,
            day: day as u8,
            hour: hour as u8,
            minute: minute as u8,
            second: second as u8,
        }
    }

    /// Set the datetime.
    pub fn set_datetime(&self, datetime: &Datetime) -> Result<(), Error> {
        // SAFETY: Clear RTC_EN bit before setting time to handle race condition
        //         when the count is in middle of a transition
        //         There is 21 mS inacurracy in the time set
        //         Todo: https://github.com/OpenDevicePartnership/embassy-imxrt/issues/121
        self.is_valid_datetime(datetime)?;
        let secs = self.convert_datetime_to_secs(datetime);
        _ = self.set_datetime_in_secs(secs);
        Ok(())
    }

    ///Set the datetime in seconds
    pub fn set_datetime_in_secs(&self, secs: u32) {
        let r = rtc();
        r.ctrl().modify(|_r, w| w.rtc_en().disable());
        r.count().write(|w| unsafe { w.bits(secs) });
        r.ctrl().modify(|_r, w| w.rtc_en().enable());
    }

    /// Get the datetime.
    pub fn get_datetime(&self) -> Result<Datetime, Error> {
        let datetime;
        let res;
        match self.get_datetime_as_secs() {
            Ok(secs) => {
                datetime = self.convert_secs_to_datetime(secs);
                match self.is_valid_datetime(&datetime) {
                    Ok(()) => {
                        res = Ok(datetime);
                    }
                    Err(e) => {
                        res = Err(e);
                    }
                }
            }
            Err(e) => {
                res = Err(e);
            }
        }
        res
    }

    /// Get the datetime as UTC seconds
    pub fn get_datetime_as_secs(&self) -> Result<u32, Error> {
        let r = rtc();
        let secs;
        //  If RTC is not enabled return error
        if r.ctrl().read().rtc_en().bit_is_clear() {
            return Err(Error::RTCNotEnabled);
        }
        loop {
            let secs1 = r.count().read().bits();
            let secs2 = r.count().read().bits();
            if secs1 == secs2 {
                secs = secs1;
                break;
            }
        }
        Ok(secs)
    }
}

#[cfg(feature = "rt")]
#[allow(non_snake_case)]
#[interrupt]
fn RTC() {
    DRIVER.on_interrupt()
}

pub(crate) fn init(irq_prio: crate::interrupt::Priority) {
    DRIVER.init(irq_prio)
}
