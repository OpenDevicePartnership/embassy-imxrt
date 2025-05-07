//! Time Driver.
use core::cell::Cell;

#[cfg(feature = "time-driver-rtc")]
pub mod rtc;

#[cfg(feature = "time-driver-rtc")]
pub use rtc::*;

#[cfg(feature = "time-driver-os-timer")]
pub mod ostimer;

#[cfg(feature = "time-driver-os-timer")]
pub use ostimer::*;

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
