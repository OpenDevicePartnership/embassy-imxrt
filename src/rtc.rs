//! RTC DateTime driver.

use crate::{pac, peripherals, Peri};

// SAFETY: This function allows access to the RTC peripheral's register block without ownership checks.
//         If a register is to be accessed from multiple locations (e.g. an interrupt), access to it
//         must be synchronized using a critical section or other synchronization mechanism.
unsafe fn rtc() -> &'static pac::rtc::RegisterBlock {
    unsafe { &*pac::Rtc::ptr() }
}

/// Represents a date and time.
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[derive(PartialEq, Debug)]
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
#[derive(PartialEq, Debug)]
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

        // Calculate days from full years from 1970 to the current year
        for year in 1970..datetime.year {
            days += 365;
            if self.is_leap_year(year) {
                days += 1;
            }
        }

        // Calculate days from January to the current month
        const DAYS_IN_MONTH: [u32; 12] = [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30];
        for month in 1..datetime.month {
            days += DAYS_IN_MONTH[month as usize];
            if month == 2 && self.is_leap_year(datetime.year) {
                days += 1;
            }
        }

        // Calculate days from the first day of the month to the current day
        days += datetime.day as u32 - 1;

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
        self.set_datetime_in_secs(secs);
        Ok(())
    }

    ///Set the datetime in seconds
    pub fn set_datetime_in_secs(&self, secs: u32) {
        // SAFETY: This is safe because calling this function requires an instance of an RtcDatetime,
        //         which takes ownership of the RTC peripheral, and we don't access any RTC registers from an interrupt.
        let r = unsafe { rtc() };
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
        // SAFETY: This is safe because calling this function requires an instance of an RtcDatetime,
        //         which takes ownership of the RTC peripheral, and we don't access any RTC registers from an interrupt.
        let r = unsafe { rtc() };
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
