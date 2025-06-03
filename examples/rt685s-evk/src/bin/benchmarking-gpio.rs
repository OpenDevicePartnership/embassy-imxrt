#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::gpio;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("Benchmarking using gpio pins");

    // Use a pin that is not in use
    // Initialize the pin to make sure it is configured correctly
    let mut _output = gpio::Output::new(
        p.PIO1_0,
        gpio::Level::Low,
        gpio::DriveMode::PushPull,
        gpio::DriveStrength::Normal,
        gpio::SlewRate::Standard,
    );

    let n = 1000;

    // Steal the GPIO register map
    let gpio = unsafe { embassy_imxrt::pac::Gpio::steal() };

    loop {
        // Do direct write to toggle the pin
        gpio.not(1).write(|w| unsafe { w.notp().bits(1 << 0) });

        // Operation to be benchmarked
        for _h in 0..n {
            cortex_m::asm::nop();
        }

        // Do direct write to toggle the pin
        gpio.not(1).write(|w| unsafe { w.notp().bits(1 << 0) });

        // Operation to be benchmarked
        for _l in 0..n {
            cortex_m::asm::nop();
        }

        // Measure pulse width of pin using a scope to benchmark
        // Mutiple pins can be used to get the best measurement
    }
}
