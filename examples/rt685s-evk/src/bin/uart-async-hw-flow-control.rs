#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::uart::{Async, Uart};
use embassy_imxrt::{bind_interrupts, peripherals, uart};
use embassy_time::Timer;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

bind_interrupts!(struct Irqs {
    FLEXCOMM2 => uart::InterruptHandler<peripherals::FLEXCOMM2>;
    FLEXCOMM4 => uart::InterruptHandler<peripherals::FLEXCOMM4>;
});

const BUFLEN: usize = 16;

#[embassy_executor::task]
async fn usart4_task(mut uart: Uart<'static, Async>) {
    loop {
        let mut rx_buf = [0; BUFLEN];
        uart.read(&mut rx_buf).await.unwrap();
        assert!(rx_buf.iter().all(|b| *b == 0x55));
        info!("usart4_task read");

        Timer::after_millis(10).await;

        let tx_buf = [0xaa; BUFLEN];
        uart.write(&tx_buf).await.unwrap();
        info!("usart4_task write");
    }
}

#[embassy_executor::task]
async fn usart2_task(mut uart: Uart<'static, Async>) {
    loop {
        let tx_buf = [0x55; BUFLEN];
        uart.write(&tx_buf).await.unwrap();
        info!("usart2_task write");

        Timer::after_millis(10).await;

        let mut rx_buf = [0x00; BUFLEN];
        uart.read(&mut rx_buf).await.unwrap();
        assert!(rx_buf.iter().all(|b| *b == 0xaa));
        info!("usart2_task read");
    }
}

/* WARNING: to enable HW flow control, a 0 ohm resistor on the EVK needs to moved to the neighboring pad.
 */
#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("UART test start");

    let usart4 = Uart::new_with_rtscts(
        p.FLEXCOMM4,
        p.PIO0_29,
        p.PIO0_30,
        p.PIO1_0,
        p.PIO0_31,
        Irqs,
        p.DMA0_CH9,
        p.DMA0_CH8,
        Default::default(),
    )
    .unwrap();
    spawner.must_spawn(usart4_task(usart4));

    let usart2 = Uart::new_with_rtscts(
        p.FLEXCOMM2,
        p.PIO0_15,
        p.PIO0_16,
        p.PIO0_18,
        p.PIO0_17,
        Irqs,
        p.DMA0_CH5,
        p.DMA0_CH4,
        Default::default(),
    )
    .unwrap();
    spawner.must_spawn(usart2_task(usart2));
}
