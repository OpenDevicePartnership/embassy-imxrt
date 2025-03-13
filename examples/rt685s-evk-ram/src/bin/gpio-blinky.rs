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

    let mut led = gpio::Output::new(
        p.PIO0_26,
        gpio::Level::Low,
        gpio::DriveMode::PushPull,
        gpio::DriveStrength::Normal,
        gpio::SlewRate::Standard,
    );

    let cortex = cortex_m::Peripherals::take().unwrap();

    loop {
        info!("Toggling LED");

        info!("VTOR = 0x{:X}", cortex.SCB.vtor.read());

        info!("MAIN PC = 0x{:X}", cortex_m::register::pc::read());
        led.toggle();
        Timer::after_millis(1000).await;
    }
}
