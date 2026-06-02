#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::pac;
use embassy_imxrt::pwm::{CentiPercent, Channel, MicroSeconds, SCTClockSource, SCTPwm};
use embassy_imxrt::timer::{CTimerPwm, CTimerPwmPeriodChannel};
use embassy_time::Timer;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

// TODO: connect with GPIO port when that is ready
fn setup_gpio() {
    // SAFETY: safe as only called on initialization
    let cc1 = unsafe { pac::Clkctl1::steal() };
    // SAFETY: safe as only called on initialization
    let rc1 = unsafe { pac::Rstctl1::steal() };

    // Enable GPIO0 Clock
    info!("Enabling GPIO0 clock");
    cc1.pscctl1_set().write(|w| w.hsgpio0_clk_set().set_clock());

    // Take GPIO0 out of reset
    info!("Clearing GPIO0 reset");
    rc1.prstctl1_clr().write(|w| w.hsgpio0_rst_clr().clr_reset());

    info!("GPIO0_26 is blue LED on rt685-evk");

    // SAFETY: safe as only executed during initialization
    let iopctl = unsafe { embassy_imxrt::pac::Iopctl::steal() };

    iopctl.pio0_26().modify(|_, w| {
        w.fsel()
            .function_3() // F3 = SCT0_OUT6
            .pupdena()
            .disabled()
            .pupdsel()
            .pull_down()
            .ibena()
            .disabled()
            .slewrate()
            .normal()
            .fulldrive()
            .normal_drive()
            .amena()
            .disabled()
            .odena()
            .disabled()
            .iiena()
            .disabled()
    });
}

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("PWM test: SCTimer/CTimer based");

    let mut sct0 = SCTPwm::new(p.SCT0, MicroSeconds(10_000), SCTClockSource::Main);

    let ctimerperiodchannel = CTimerPwmPeriodChannel::new(p.CTIMER4_COUNT_CHANNEL0, MicroSeconds(10_000)).unwrap();

    // CTIMER4_MAT3 configuration for PIO0_31
    info!("GPIO0_31 is red LED on rt685-evk");
    let mut ctimer = CTimerPwm::new(p.CTIMER4_COUNT_CHANNEL3, &ctimerperiodchannel, p.PIO0_31).unwrap();

    ctimer.enable(());

    // SCT0_OUT6: PIO0_9, PIO0_18, PIO0_26, PIO0_31, PIO2_12
    // ^-- SCT0 configuration allowed for PIO 0_26
    setup_gpio();

    use embassy_imxrt::pwm::Pwm;
    sct0.enable(Channel::Ch6);

    loop {
        info!("PWM: Verify Blue and Red LEDs are off.");
        let duty = CentiPercent(0, 0);
        sct0.set_duty(Channel::Ch6, duty);
        ctimer.set_duty((), duty);
        // verify blinky is off
        Timer::after_secs(5).await;

        info!("PWM: Verify Blue and Red LEDs are on.");
        let duty = CentiPercent(100, 0);
        sct0.set_duty(Channel::Ch6, duty);
        ctimer.set_duty((), duty);
        // verify blinky is on
        Timer::after_secs(5).await;

        info!("PWM: Verify Blue and Red LEDs are dimmed.");
        let duty = CentiPercent(10, 0);
        sct0.set_duty(Channel::Ch6, duty);
        ctimer.set_duty((), duty);
        // verify dimmed blinky
        Timer::after_secs(5).await;

        // perform ramp of LED brightness
        info!("PWM: Verify Blue and Red LEDs brightness ramp on.");
        for pct in 0..=100u8 {
            sct0.set_duty(Channel::Ch6, CentiPercent(pct, 0));
            ctimer.set_duty((), CentiPercent(pct, 0));
            Timer::after_millis(100).await;
        }

        info!("PWM: Verify Blue and Red LEDs brightness ramp off.");
        for pct in 0..=100u8 {
            sct0.set_duty(Channel::Ch6, CentiPercent(100 - pct, 0));
            ctimer.set_duty((), CentiPercent(100 - pct, 0));
            Timer::after_millis(100).await;
        }

        Timer::after_millis(1000).await;
    }
}
