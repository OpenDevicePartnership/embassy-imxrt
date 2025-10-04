#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::clocks::ClockConfig;
use embassy_imxrt::timer::{CaptureChEdge, CaptureTimer, CountingTimer};
use embassy_imxrt::{bind_interrupts, peripherals, timer};
use embassy_time::Timer;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

bind_interrupts!(struct Irqs {
    CTIMER0 => timer::InterruptHandler<peripherals::CTIMER0_COUNT_CHANNEL0>;
    CTIMER1 => timer::InterruptHandler<peripherals::CTIMER1_COUNT_CHANNEL0>;
    CTIMER4 => timer::InterruptHandler<peripherals::CTIMER4_CAPTURE_CHANNEL0>;
});

// Monitor task is created to demonstrate difference between Async and Blocking timer behavior
#[embassy_executor::task]
async fn monitor_task() {
    loop {
        info!("Secondary task running");
        Timer::after_millis(1000).await;
    }
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let mut p = embassy_imxrt::init(Default::default());

    spawner.spawn(monitor_task()).unwrap();

    let sfro = ClockConfig::crystal().sfro;
    let mut tmr1 = CountingTimer::new_blocking(p.CTIMER0_COUNT_CHANNEL0, sfro);

    let sfro = ClockConfig::crystal().sfro;
    let mut tmr2 = CountingTimer::new_async(p.CTIMER1_COUNT_CHANNEL0, sfro, Irqs);

    tmr1.wait_us(3000000); // 3 seoconds wait
    info!("First Counting timer expired");

    tmr2.wait_us(5000000).await; //  5 seconds wait
    info!("Second Counting timer expired");

    {
        let sfro = ClockConfig::crystal().sfro;
        let mut cap_async_tmr =
            CaptureTimer::new_async(p.CTIMER4_CAPTURE_CHANNEL0.reborrow(), p.PIO0_5.reborrow(), sfro, Irqs);
        let event_time_us = cap_async_tmr.capture_cycle_time_us(CaptureChEdge::Rising).await;
        info!("Capture timer expired, time between two capture = {} us", event_time_us);

        drop(cap_async_tmr);

        let sfro = ClockConfig::crystal().sfro;
        let mut cap_async_tmr =
            CaptureTimer::new_async(p.CTIMER4_CAPTURE_CHANNEL0.reborrow(), p.PIO0_5.reborrow(), sfro, Irqs);
        let event_time_us = cap_async_tmr.capture_cycle_time_us(CaptureChEdge::Rising).await;
        info!("Capture timer expired, time between two capture = {} us", event_time_us);
    }

    loop {
        // This code is showing how to use the timer in a periodic fashion
        tmr2.wait_us(5000000).await;
        info!("Primary task running");
    }
}
