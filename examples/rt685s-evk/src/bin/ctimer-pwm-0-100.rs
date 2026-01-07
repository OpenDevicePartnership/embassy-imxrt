#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::gpio;
use embassy_imxrt::pwm::Pwm;
use embassy_imxrt::pwm::{CentiPercent, Channel, MicroSeconds, SCTClockSource, SCTPwm};
use embassy_imxrt::timer::{CTimerPwm, CTimerPwmPeriodChannel};
use embassy_time::{Duration, Timer, WithTimeout, with_timeout};
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("PWM test: SCTimer/CTimer based");

    let ctimerperiodchannel = CTimerPwmPeriodChannel::new(p.CTIMER4_COUNT_CHANNEL0, MicroSeconds(1_000)).unwrap();

    let mut monitor = gpio::Input::new(p.PIO1_0, gpio::Pull::None, gpio::Inverter::Disabled);

    let mut ctimer = CTimerPwm::new(p.CTIMER4_COUNT_CHANNEL2, &ctimerperiodchannel, p.PIO0_30).unwrap();

    ctimer.enable(());

    // By default, duty cycle should be 0%, always low, so no rising edges
    let res = with_timeout(Duration::from_secs(2), monitor.wait_for_rising_edge()).await;

    match res {
        Err(_) => info!("No rising edge detected as expected for 0% duty cycle"),
        Ok(_) => panic!("Unexpected rising edge detected at 0% duty cycle"),
    }

    let duty = CentiPercent(100, 0);
    ctimer.set_duty((), duty);

    // With 100% duty cycle, always high, so no falling edges
    let res = with_timeout(Duration::from_secs(2), monitor.wait_for_falling_edge()).await;

    match res {
        Err(_) => info!("No falling edge detected as expected for 100% duty cycle"),
        Ok(_) => panic!("Unexpected falling edge detected at 100% duty cycle"),
    }
}
