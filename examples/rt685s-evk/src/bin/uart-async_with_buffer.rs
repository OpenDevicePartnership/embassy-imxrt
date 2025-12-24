#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::uart::{Async, Uart, UartRx};
use embassy_imxrt::{bind_interrupts, peripherals, uart};
use embassy_time::Timer;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

const BUFLEN: usize = 32;
const POLLING_RATE_US: u64 = 1000;

bind_interrupts!(struct Irqs {
    FLEXCOMM4 => uart::InterruptHandler<peripherals::FLEXCOMM4>;
});

#[embassy_executor::task]
async fn reader(mut rx: UartRx<'static, Async>) {
    info!("Reading...");
    loop {
        let mut buf = [0; 32];
        rx.read(&mut buf).await.unwrap();
        info!("RX {:?}", buf);
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
    loop {
        let data = [
            1u8, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
            29, 30, 31,
        ];
        info!("TX {:?}", data);
        tx.write(&data).await.unwrap();
        Timer::after_secs(1).await;
    }
}
