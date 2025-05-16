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

    let monitor = gpio::Input::new(p.PIO1_0, gpio::Pull::None, gpio::Inverter::Disabled);

    loop {
        info!("Pin level is {}", monitor.get_level());
        Timer::after_millis(1000).await;
    }
}
