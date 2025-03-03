#![no_std]
#![no_main]

extern crate embassy_imxrt_examples;

use defmt::{assert, info};
use embassy_executor::Spawner;
use embassy_imxrt::gpio::SenseDisabled;
use embassy_imxrt::{gpio, pac};
use embassy_time::Timer;

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("Initializing GPIO");

    let cc1 = unsafe { pac::Clkctl1::steal() };
    assert!(cc1.pscctl1().read().hsgpio1_clk().is_disable_clock());

    // Start with a level sensing disabled, output only state
    let flex = gpio::Flex::<SenseDisabled>::new(p.PIO1_0);

    assert!(cc1.pscctl1().read().hsgpio1_clk().is_enable_clock());

    // enable level sensing
    let mut flex = flex.enable_sensing();

    // set pin output bit to high before setting direction
    flex.set_high();

    // set direction as output
    flex.set_as_output(
        gpio::DriveMode::PushPull,
        gpio::DriveStrength::Normal,
        gpio::SlewRate::Standard,
    );

    // check pin level is high
    assert!(flex.is_high());

    // toggle pin
    flex.toggle();

    // check pin level is low
    assert!(flex.is_low());

    // set pin direction to output with reverse polarity
    flex.set_as_input(gpio::Pull::None, gpio::Inverter::Enabled);

    // check pin level is high
    assert!(flex.is_high());

    // set pin output bit to high
    flex.set_high();

    // check pin level is still high
    assert!(flex.is_high());

    // set pin direction to output again
    flex.set_as_output(
        gpio::DriveMode::PushPull,
        gpio::DriveStrength::Normal,
        gpio::SlewRate::Standard,
    );

    // check pin level is now low
    assert!(flex.is_low());

    // disable level sensing
    let mut flex = flex.disable_sensing();

    // set pin level high
    flex.set_high();
    flex.set_as_output(
        gpio::DriveMode::PushPull,
        gpio::DriveStrength::Normal,
        gpio::SlewRate::Standard,
    );

    // re-enable level sensing
    let mut flex = flex.enable_sensing();
    // set pin level high
    flex.set_high();
    flex.set_as_output(
        gpio::DriveMode::PushPull,
        gpio::DriveStrength::Normal,
        gpio::SlewRate::Standard,
    );

    // check pin level is high
    assert!(flex.is_high());

    // toggle pin
    flex.toggle();

    // check pin level is low
    assert!(flex.is_low());

    // toggle pin
    flex.toggle();

    flex.set_as_output(
        gpio::DriveMode::PushPull,
        gpio::DriveStrength::Normal,
        gpio::SlewRate::Standard,
    );

    // check pin level is high
    assert!(flex.is_high());

    assert!(cc1.pscctl1().read().hsgpio1_clk().is_enable_clock());
    drop(flex);
    assert!(cc1.pscctl1().read().hsgpio1_clk().is_disable_clock());

    loop {
        Timer::after_millis(1000).await;
    }
}
