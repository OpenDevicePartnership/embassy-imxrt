#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::uart::{Async, Uart, UartRx};
use embassy_imxrt::{bind_interrupts, peripherals, uart};
use embassy_time::Timer;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

const BUFLEN: usize = 2048;
const POLLING_RATE_US: u64 = 1000;

bind_interrupts!(struct Irqs {
    FLEXCOMM4 => uart::InterruptHandler<peripherals::FLEXCOMM4>;
});

#[embassy_executor::task]
async fn reader(mut rx: UartRx<'static, Async>) {
    info!("Reading...");
    let mut expected_counter = 0;
    loop {
        let mut buf = [0; BUFLEN / 2];
        rx.read(&mut buf).await.unwrap();
        info!("RX {:?}", buf);

        for &b in buf.iter() {
            assert_eq!(b, expected_counter);
        }
        expected_counter = expected_counter.wrapping_add(1);

        Timer::after_millis(1).await;
    }
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("UART test start");

    static mut RX_BUF: [u8; BUFLEN] = [0; BUFLEN];
    let uart = Uart::new_async_with_buffer(
        p.FLEXCOMM4,
        p.PIO0_29,
        p.PIO0_30,
        Irqs,
        p.DMA0_CH9,
        p.DMA0_CH8,
        Default::default(),
        unsafe { &mut *core::ptr::addr_of_mut!(RX_BUF) },
        POLLING_RATE_US,
    )
    .unwrap();
    let (mut tx, rx) = uart.split();
    spawner.must_spawn(reader(rx));

    info!("Writing...");

    let mut counter = 1;
    loop {
        let mut data: [u8; BUFLEN / 2] = [0; BUFLEN / 2];
        for (_i, b) in data.iter_mut().enumerate() {
            *b = counter;
        }
        tx.write(&data).await.unwrap();

        counter = counter.wrapping_add(1);
    }
}
