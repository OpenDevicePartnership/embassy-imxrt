#![no_std]
#![no_main]

extern crate embassy_imxrt_examples;

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::{gpio, pac};
use embassy_time::Timer;

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("Initializing GPIO");

    let cc1 = unsafe { pac::Clkctl1::steal() };

    assert!(
        cc1.pscctl1().read().hsgpio0_clk().is_disable_clock(),
        "GPIO port 0 clock was enabled before any GPIO pins were created!"
    );

    let mut led = gpio::Output::new(
        p.PIO0_26,
        gpio::Level::Low,
        gpio::DriveMode::PushPull,
        gpio::DriveStrength::Normal,
        gpio::SlewRate::Standard,
    );

    assert!(
        cc1.pscctl1().read().hsgpio0_clk().is_enable_clock(),
        "GPIO port 0 clock is still disabled even after a GPIO pin is created!"
    );

    loop {
        info!("Toggling LED");
        led.toggle();
        Timer::after_millis(1000).await;
    }
}
