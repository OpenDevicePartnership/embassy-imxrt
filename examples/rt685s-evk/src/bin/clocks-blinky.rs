#![no_main]
#![no_std]

use defmt::{error, info};
use embassy_executor::Spawner;
use embassy_imxrt::iopctl::IopctlPin;
use embassy_imxrt::{clocks, gpio};
use embassy_time::Timer;
use {defmt_rtt as _, embassy_imxrt as _, embassy_imxrt_examples as _, panic_probe as _};

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let embassy_p = embassy_imxrt::init(Default::default());

    info!("Initializing GPIO");

    let mut led = gpio::Output::new(
        embassy_p.PIO0_26,
        gpio::Level::Low,
        gpio::DriveMode::PushPull,
        gpio::DriveStrength::Normal,
        gpio::SlewRate::Standard,
    );

    let clk_out = embassy_p.PIO1_10;

    clk_out
        .disable_analog_multiplex()
        .disable_input_buffer()
        .set_drive_mode(embassy_imxrt::gpio::DriveMode::PushPull)
        .set_drive_strength(embassy_imxrt::gpio::DriveStrength::Normal)
        .set_input_inverter(embassy_imxrt::gpio::Inverter::Disabled)
        .set_function(embassy_imxrt::gpio::Function::F7)
        .set_slew_rate(embassy_imxrt::gpio::SlewRate::Standard)
        .set_pull(embassy_imxrt::gpio::Pull::None);

    let mut clk_out_config = clocks::ClockOutConfig::default_config();
    if let Err(e) = clk_out_config.enable_and_reset() {
        error!("Couldn't enable clock out {:?}", e);
    }

    if let Err(e) = clk_out_config.set_clkout_source_and_div(clocks::ClkOutSrc::Lposc, 0) {
        error!("Couldn't configure clock out {:?}", e);
    }
    info!("Clock out to LPOSC so 1MHz");
    for _i in 0..10 {
        led.toggle();
        Timer::after_millis(1000).await;
    }

    if let Err(e) = clk_out_config.set_clkout_source_and_div(clocks::ClkOutSrc::Sfro, 31) {
        error!("Couldn't configure clock out {:?}", e);
    }
    info!("switched Clock out to SFRO divided by 32 so 500KHz");
    for _i in 0..10 {
        led.toggle();
        Timer::after_millis(1000).await;
    }

    if let Err(e) = clk_out_config.set_clkout_source_and_div(clocks::ClkOutSrc::MainClk, 99) {
        error!("Couldn't configure clockout {:?}", e);
    }
    info!("switched Clock out to Main Clk div 100, expecting 5MHz");
    loop {
        info!("Toggling LED");
        led.toggle();
        Timer::after_millis(1000).await;
    }
}
