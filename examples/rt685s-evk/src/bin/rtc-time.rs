#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::rtc::Rtc;
use embassy_time::Timer;
use mcu_traits::datetime::{Datetime, UncheckedDatetime};
use mcu_traits::{DatetimeClock, Nvram, NvramStorage};

use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    const DEMO_DELAY_MS: u64 = 5000;

    let p = embassy_imxrt::init(Default::default());
    let mut r = Rtc::new(p.RTC);
    let (dt_clock, rtc_nvram) = r.split();

    // Datetime clock example
    {
        let datetime = Datetime::new(UncheckedDatetime {
            year: 2024,
            month: 10,
            day: 4,
            hour: 16,
            ..Default::default()
        })
        .unwrap();

        let ret = dt_clock.set_current_datetime(&datetime);
        info!("RTC set time: {:?}", datetime);
        assert!(ret.is_ok());

        info!("Wait for 5 seconds");
        Timer::after_millis(DEMO_DELAY_MS).await;

        let result = dt_clock.get_current_datetime();
        assert!(result.is_ok());
        info!("RTC get time: {:?}", result.unwrap());
    }

    // NVRAM example
    {
        // Note that unused registers are handled with a '..' pattern, rather than explictly naming all registers.
        // This approach is recommended, because it allows the code to remain compatible with optional HAL features that
        // may consume some of these registers, so long as the total number of registers is not overcommitted.
        // If the number of registers is overcommitted, the code will not compile, which will help catch the issue early.
        let [gp0, gp1, ..] = rtc_nvram.storage();
        info!("RTC NVRAM GP0: {:?}", gp0.read());
        info!("RTC NVRAM GP1: {:?}", gp1.read());

        gp0.write(12345678);
        info!("RTC NVRAM GP0: {:?}", gp0.read());
    }

    // Example of interop with the `chrono` library.  Requires the `chrono` feature to be enabled in the HAL and embedded-mcu crates.
    {
        let chrono_dt = chrono::NaiveDateTime::new(
            chrono::NaiveDate::from_ymd_opt(2025, 6, 1).unwrap(),
            chrono::NaiveTime::from_hms_opt(10, 30, 0).unwrap(),
        );

        let embassy_dt = Datetime::try_from(chrono_dt).expect(
            "Conversion should always succeed because the date we provided above is within bounds (>= 1970-01-01).",
        );

        assert!(chrono::NaiveDateTime::from(embassy_dt) == chrono_dt);

        let ret = dt_clock.set_current_datetime(&embassy_dt);
        info!("RTC set time as chrono::NaiveDateTime: {:?}", embassy_dt);
        assert!(ret.is_ok());

        info!("Wait for 5 seconds");
        Timer::after_millis(DEMO_DELAY_MS).await;

        let result = dt_clock.get_current_datetime();
        assert!(result.is_ok());
        info!("RTC get time: {:?}", result.unwrap());
    }
}
