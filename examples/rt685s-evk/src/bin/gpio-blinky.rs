#![no_std]
#![no_main]

use embassy_imxrt_examples as _;

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::gpio;
use embassy_time::Timer;
use {defmt_rtt as _, panic_probe as _};

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("Initializing GPIO");

    let mut led = gpio::Output::new(
        p.PIO0_26,
        gpio::Level::Low,
        gpio::DriveMode::PushPull,
        gpio::DriveStrength::Normal,
        gpio::SlewRate::Standard,
    );

    loop {
        info!("Toggling LED");
        led.toggle();
        Timer::after_millis(1000).await;
    }
}
