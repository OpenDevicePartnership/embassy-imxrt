#![no_std]
#![no_main]

extern crate embassy_imxrt_perf_examples;

use core::sync::atomic::{AtomicBool, Ordering};
use embassy_executor::Spawner;
use embassy_imxrt::gpio;
use embassy_time::Timer;
use panic_probe as _;
use systemview_tracing::info;

// Trace Markers
#[repr(u32)]
enum TestTraceMarker {
    Test1 = 0x10,
    Test2,
}

// Shared state between tasks
static BUFFER_READY: AtomicBool = AtomicBool::new(false);
static PROCESSING_ACTIVE: AtomicBool = AtomicBool::new(false);

#[embassy_executor::task]
async fn data_processing_task() {
    loop {
        systemview_tracing::mark_trace(TestTraceMarker::Test1 as u32);
        if BUFFER_READY.load(Ordering::SeqCst) {
            PROCESSING_ACTIVE.store(true, Ordering::SeqCst);

            for _ in 0..1000000 {
                // CPU-intensive work without yielding
                let _ = core::hint::black_box(42u32 * 1337u32);
            }

            PROCESSING_ACTIVE.store(false, Ordering::SeqCst);
            BUFFER_READY.store(false, Ordering::SeqCst);
        }
        systemview_tracing::mark_trace(TestTraceMarker::Test2 as u32);

        // Frequent polling
        Timer::after_millis(1).await;
    }
}

// Communication task with poor timing behavior
#[embassy_executor::task]
async fn communication_task() {
    loop {
        for _ in 0..5000 {
            let _ = core::hint::black_box(42u32);
        }

        Timer::after_millis(20).await;
    }
}

#[embassy_executor::task]
async fn user_interface_task() {
    loop {
        let work_time = 30 + (embassy_time::Instant::now().as_millis() % 20);
        Timer::after_millis(work_time).await;

        for _ in 0..2000 {
            let _ = core::hint::black_box(42u32);
        }

        Timer::after_millis(50).await;
    }
}

#[embassy_executor::task]
async fn led_toggle_task(mut led: gpio::Output<'static>) {
    loop {
        led.toggle();
        Timer::after_millis(1000).await;
    }
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    systemview_tracing::init_tracing(250_000_000);

    let led = gpio::Output::new(
        p.PIO0_26,
        gpio::Level::Low,
        gpio::DriveMode::PushPull,
        gpio::DriveStrength::Normal,
        gpio::SlewRate::Standard,
    );

    info!("start multiple tasks example");

    let token = data_processing_task().unwrap();
    token.metadata().set_name("data_processing_task\0");
    spawner.spawn(token);

    let token = communication_task().unwrap();
    token.metadata().set_name("communication_task\0");
    spawner.spawn(token);

    let token = user_interface_task().unwrap();
    token.metadata().set_name("user_interface_task\0");
    spawner.spawn(token);

    let token = led_toggle_task(led).unwrap();
    token.metadata().set_name("led_toggle_task\0");
    spawner.spawn(token);
}
