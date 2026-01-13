#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::rtc::Rtc;
use embassy_time::Timer;
use embedded_mcu_hal::time::{Datetime, DatetimeClock, Month, UncheckedDatetime};
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

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

    dt_clock.dump_registers();

    // Display current time before setting alarm
    let current_time = dt_clock.get_current_datetime().unwrap();
    info!("Current time before alarm: {:?}", current_time);
    info!("Waiting 5 seconds...");
    Timer::after_secs(5).await;
    info!(
        "Current time after waiting: {:?}",
        dt_clock.get_current_datetime().unwrap()
    );

    // Set an alarm to trigger after ALARM_SECONDS
    info!("Setting alarm to trigger in {} seconds...", ALARM_SECONDS);
    let alarm = dt_clock.set_alarm(ALARM_SECONDS).expect("Failed to set alarm");

    dt_clock.dump_registers();

    // Wait for the alarm to trigger
    info!("Waiting for alarm...");
    alarm.await.expect("Alarm failed");

    // Display time after alarm triggered
    let wake_time = dt_clock.get_current_datetime().unwrap();
    info!("Alarm triggered! Wake time: {:?}", wake_time);

    // Clear the alarm
    dt_clock.clear_alarm().expect("Failed to clear alarm");
    info!("Alarm cleared");

    dt_clock.dump_registers();

    info!("Demo complete!");
}
