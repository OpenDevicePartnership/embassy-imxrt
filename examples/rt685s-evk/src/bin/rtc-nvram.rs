#![no_std]
#![no_main]

use core::cell::RefCell;
use defmt::info;
use embassy_imxrt::rtc::RtcNvramStorage;
use embassy_sync::blocking_mutex::{CriticalSectionMutex, Mutex};
use embassy_sync::once_lock::OnceLock;
use embassy_time::{Duration, Timer};
use embedded_mcu_hal::{Nvram, NvramStorage};
use static_cell::StaticCell;

use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

// Tasks demonstrating a way to share an NVRAM storage cell between multiple tasks and/or interrupts
#[embassy_executor::task]
async fn reg_ticker(storage: &'static CriticalSectionMutex<RefCell<&'static mut RtcNvramStorage<'static>>>) {
    loop {
        storage.lock(|gp| {
            let value = gp.borrow().read();
            gp.borrow_mut().write(value + 1);
            info!("SHARED TICK VALUE: {:?}", gp.borrow().read());
        });
        Timer::after(Duration::from_millis(1000)).await;
    }
}

#[embassy_executor::task]
async fn reg_setter(storage: &'static CriticalSectionMutex<RefCell<&'static mut RtcNvramStorage<'static>>>) {
    loop {
        storage.lock(|gp| {
            gp.borrow_mut().write(0);
            info!("SHARED RESET VALUE: 0");
        });
        Timer::after(Duration::from_millis(5000)).await;
    }
}

/////

// Tasks demonstrating a way to give a task exclusive ownership of an NVRAM storage cell.
#[embassy_executor::task]
async fn unshared_ticker(storage: &'static mut RtcNvramStorage<'static>) {
    loop {
        let value = storage.read();
        storage.write(value + 1);
        info!("UNSHARED TICK VALUE: {}", value);

        Timer::after(Duration::from_millis(1000)).await;
    }
}

/////

// Task demonstrating a way to share an NVRAM storage cell between one or more tasks and an interrupt handler.
#[embassy_executor::task]
async fn reg_interrupt_ticker(storage: &'static CriticalSectionMutex<RefCell<&'static mut RtcNvramStorage<'static>>>) {
    loop {
        storage.lock(|gp| {
            let value = gp.borrow().read();
            gp.borrow_mut().write(value + 1);
            info!("INTERRUPT TASK TICK VALUE: {:?}", gp.borrow().read());
        });
        Timer::after(Duration::from_millis(1000)).await;
    }
}

static INTERRUPT_SHARED_TICKER: OnceLock<CriticalSectionMutex<RefCell<&'static mut RtcNvramStorage<'static>>>> =
    OnceLock::new();

// TODO actually make this handle an interrupt
fn EXAMPLE_INTERRUPT_HANDLER() {
    // This is a placeholder for the interrupt handler that would use the shared ticker.
    // In a real application, you would implement the logic to handle the interrupt and
    // access the shared NVRAM storage cell here.
    if let Some(ticker) = INTERRUPT_SHARED_TICKER.try_get() {
        ticker.lock(|gp| {
            info!("INTERRUPT RESET TICKER VALUE");
            gp.borrow_mut().write(0);
        });
    }
}

#[embassy_executor::main]
async fn main(spawner: embassy_executor::Spawner) {
    let p = embassy_imxrt::init(Default::default());

    // We want to pass NVRAM cells to tasks/interrupts, so the RTC needs to have a static lifetime.
    static RTC: StaticCell<embassy_imxrt::rtc::Rtc> = StaticCell::new();
    let rtc = RTC.init(embassy_imxrt::rtc::Rtc::new(p.RTC));

    let (_dt_clock, rtc_nvram) = rtc.split();

    // Note: it's recommended to use the lower registers first and use .. for register that you don't need;
    //       that way, if you later want to enable an optional HAL feature that consumes some of the registers
    //       provide some functionality, you won't have to change your code to accommodate as long as you're
    //       not overcommitting the number of registers.
    //       If you do overcommit, the code will not compile, which will help catch the issue early.
    let [shared_ticker_register, unshared_ticker_register, interrupt_ticker_register, ..] = rtc_nvram.storage();

    // Unshared ticker example - you can just give the mutable borrow of the storage cell to the task.
    spawner.must_spawn(unshared_ticker(unshared_ticker_register));

    // Shared ticker example - you need a mutex to protect access to the storage cell.
    static TICKER_MUTEX: StaticCell<CriticalSectionMutex<RefCell<&mut RtcNvramStorage>>> = StaticCell::new();
    let ticker_mutex = TICKER_MUTEX.init(Mutex::new(RefCell::new(shared_ticker_register)));

    spawner.must_spawn(reg_setter(ticker_mutex));
    spawner.must_spawn(reg_ticker(ticker_mutex));

    // Shared with interrupt example - you need to put a static reference in the global scope so the interrupt handler can access it
    spawner.must_spawn(reg_interrupt_ticker(
        INTERRUPT_SHARED_TICKER.get_or_init(|| Mutex::new(RefCell::new(interrupt_ticker_register))),
    ));

    loop {
        // TODO make this actually handle an interrupt; for now, we're just calling a static function that takes no args to sort-of simulate one
        EXAMPLE_INTERRUPT_HANDLER();
        Timer::after(Duration::from_millis(6000)).await;
    }
}
