#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::uart::{Uart, UartTx};
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("UART test start");

    let usart4 = Uart::new_blocking(p.FLEXCOMM4, p.PIO0_29, p.PIO0_30, Default::default()).unwrap();

    let (_, mut usart4) = usart4.split();

    let mut usart2 = UartTx::new_blocking(p.FLEXCOMM2, p.PIO0_15, Default::default()).unwrap();

    loop {
        let buf = "Testing\0".as_bytes();

        usart2.blocking_write(buf).unwrap();

        let mut buf = [0; 8];

        usart4.blocking_read(&mut buf).unwrap();

        let s = core::str::from_utf8(&buf).unwrap();

        info!("Received '{}'", s);
    }
}
