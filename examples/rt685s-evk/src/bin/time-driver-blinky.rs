#![no_main]
#![no_std]

use defmt::info;
use defmt_rtt as _;
use embassy_executor::Spawner;
use embassy_imxrt as _;
use embassy_imxrt::gpio;
use embassy_imxrt_examples as _;
use embassy_time::Timer;
use panic_probe as _;

#[embassy_executor::main]
async fn main(_spawner: Spawner) -> ! {
    let embassy_p = embassy_imxrt::init(Default::default());

    info!("Initializing GPIO");

    let mut led = gpio::Output::new(
        embassy_p.PIO0_26,
        gpio::Level::Low,
        gpio::DriveMode::PushPull,
        gpio::DriveStrength::Normal,
        gpio::SlewRate::Standard,
    );

    loop {
        info!("Toggling GPIO0_26 (Blue LED)");
        led.toggle();
        Timer::after_millis(5000).await;
    }
}
