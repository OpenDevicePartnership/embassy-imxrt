#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::uart::{Async, Uart, UartRx};
use embassy_imxrt::{bind_interrupts, pac, peripherals, uart};
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

const BUFLEN: usize = 512;
const POLLING_RATE_US: u64 = 1000;

bind_interrupts!(struct Irqs {
    FLEXCOMM4 => uart::InterruptHandler<peripherals::FLEXCOMM4>;
});

static mut RX_BUF: [u8; BUFLEN] = [0; BUFLEN];

#[embassy_executor::task]
async fn reader(mut rx: UartRx<'static, Async>) {
    info!("Reading...");
    let mut byte_counter: usize = 0;
    let mut loop_counter: usize = 0;
    let mut buf = [0; BUFLEN / 2];

    loop {
        let read_len = loop_counter % (BUFLEN / 2) + 1;

        info!("Total bytes read: {}, read length: {}", byte_counter, read_len);

        let res = rx.read(&mut buf[..read_len]).await;

        if res.is_err() {
            info!("Read error: {:?}", res);
            panic!("Read error");
        }

        let data_len = res.unwrap();
        info!("Data length: {}", data_len);

        for (i, b) in buf[..data_len].iter().enumerate() {
            if *b != (byte_counter % 256) as u8 {
                info!("buf: {:?}", &buf[..data_len]);

                info!(
                    "Data mismatch at index {}: expected {}, got {}",
                    i,
                    (byte_counter % 256) as u8,
                    *b
                );

                info!("dma_buffer: {:?}", unsafe { RX_BUF });

                for (j, s) in unsafe { RX_BUF }.iter().enumerate() {
                    if *s != (j % 256) as u8 {
                        info!(
                            "RX_BUF mismatch at index {}: expected {}, got {}",
                            j,
                            (j % 256) as u8,
                            *s
                        );
                    }
                }

                let regs = unsafe { &*crate::pac::Usart4::ptr() };

                info!("fifostat = 0x{:X}", regs.fifostat().read().bits());

                panic!(
                    "data corruption detected at byte_counter {} (loop_counter {})",
                    byte_counter, loop_counter
                );
            }
            byte_counter = byte_counter.wrapping_add(1);
        }
        loop_counter = loop_counter.wrapping_add(1);
    }
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("UART test start");

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

    let mut data: [u8; BUFLEN / 2] = [0; BUFLEN / 2];
    for (i, b) in data.iter_mut().enumerate() {
        *b = (i % 256) as u8;
    }

    info!("data = {:?}", data);

    let mut index = 0;
    loop {
        tx.write(&data).await.unwrap();
        embassy_time::Timer::after_micros((index % 20 + 10) * POLLING_RATE_US).await;
        index = index.wrapping_add(1);
    }
}
