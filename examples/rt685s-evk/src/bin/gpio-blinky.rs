#![no_std]
#![no_main]

extern crate embassy_imxrt_examples;

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::gpio;
use embassy_time::Timer;

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("Initializing GPIO");
    // unsafe { gpio::init() };

    // let mut led = gpio::Output::new(
    //     p.PIO0_26,
    //     gpio::Level::Low,
    //     gpio::DriveMode::PushPull,
    //     gpio::DriveStrength::Normal,
    //     gpio::SlewRate::Standard,
    // );

    info!("Toggling LED");
    // led.toggle();
    Timer::after_millis(1000).await;
    assert!(false, "some failure");
    info!("SUCCESS: Example terminated successfully");
    defmt::flush();
    cortex_m::asm::bkpt();
}
