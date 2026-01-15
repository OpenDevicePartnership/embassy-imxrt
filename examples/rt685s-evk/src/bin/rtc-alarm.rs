#![no_std]
#![no_main]

use core::task::Poll;

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::rtc::{Rtc, RtcDatetimeClock};
use embassy_time::Timer;
use embedded_mcu_hal::time::{Datetime, DatetimeClock, DatetimeClockError, Month, UncheckedDatetime};
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

/// RTC alarm struct to await the time alarm wakeup location
/// This should be implemented by the user to handle RTC peripheral synchronization
struct RtcAlarm<'r> {
    expires_at: u64,
    rtc: &'r RtcDatetimeClock<'r>,
}

impl<'r> Future for RtcAlarm<'r> {
    type Output = Result<(), DatetimeClockError>;
    fn poll(self: core::pin::Pin<&mut Self>, cx: &mut core::task::Context<'_>) -> Poll<Self::Output> {
        match self.rtc.get_current_datetime() {
            Ok(now) => {
                if self.expires_at <= now.to_unix_time_seconds() {
                    Poll::Ready(Ok(()))
                } else {
                    info!("Alarm pending at time {}, expires at {}", now, self.expires_at);

                    // Register our waker to be called by the interrupt handler
                    self.rtc.register_alarm_waker(cx.waker());

                    Poll::Pending
                }
            }
            Err(e) => Poll::Ready(Err(e)),
        }
    }
}
#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    const ALARM_SECONDS: u64 = 10;

    let p = embassy_imxrt::init(Default::default());
    let mut r = Rtc::new(p.RTC);
    let (dt_clock, _rtc_nvram) = r.split();

    // Initialize the system RTC
    let datetime = Datetime::new(UncheckedDatetime {
        year: 2026,
        month: Month::January,
        day: 12,
        hour: 16,
        ..Default::default()
    })
    .unwrap();
    let ret = dt_clock.set_current_datetime(&datetime);
    info!("RTC set time: {:?}", datetime);
    assert!(ret.is_ok());

    // Show RTC functioning: Display current time before setting alarm
    let current_time = dt_clock.get_current_datetime().unwrap();
    info!("Current time before alarm: {:?}", current_time);

    info!("Waiting 5 seconds...");
    Timer::after_secs(5).await; // This timer uses the OsTimer peripheral

    info!(
        "Current time after waiting: {:?}",
        dt_clock.get_current_datetime().unwrap()
    );

    // Set an RTC alarm to trigger after ALARM_SECONDS
    info!("Setting alarm to trigger in {} seconds...", ALARM_SECONDS);
    let expires_at_secs = dt_clock.set_alarm_from_now(ALARM_SECONDS).expect("Failed to set alarm");

    let alarm = RtcAlarm {
        expires_at: expires_at_secs,
        rtc: dt_clock,
    };

    // Wait for the alarm to trigger
    info!("Waiting for alarm...");
    alarm.await.expect("Alarm failed");

    // Display time after alarm triggered
    let wake_time = dt_clock.get_current_datetime().unwrap();
    info!("Alarm triggered! Wake time: {:?}", wake_time);

    // Clear the alarm
    dt_clock.clear_alarm();
    info!("Alarm cleared");
}
