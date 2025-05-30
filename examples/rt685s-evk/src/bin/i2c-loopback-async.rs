#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::i2c::master::{DutyCycle, I2cMaster};
use embassy_imxrt::i2c::slave::AsyncI2cSlave;
use embassy_imxrt::i2c::{self, Async};
use embassy_imxrt::{bind_interrupts, peripherals};
use embedded_hal_async::i2c::I2c;
use embedded_hal_i2c::{
    AnyAddress, AsyncI2cTarget, AsyncReadTransaction, AsyncWriteTransaction, ReadResult, Transaction, WriteResult,
};
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

const ADDR: u8 = 0x20;
const MASTER_BUFLEN: usize = 8;
// slave buffer has to be 1 bigger than master buffer because master does not
// handle end of read properly
const SLAVE_BUFLEN: usize = MASTER_BUFLEN + 1;
const SLAVE_ADDR: Option<AnyAddress> = Some(AnyAddress::Seven(ADDR));

bind_interrupts!(struct Irqs {
    FLEXCOMM2 => i2c::InterruptHandler<peripherals::FLEXCOMM2>;
    FLEXCOMM4 => i2c::InterruptHandler<peripherals::FLEXCOMM4>;
});

#[embassy_executor::task]
async fn slave_service(mut slave: AsyncI2cSlave<'static>) {
    loop {
        let mut r_buf = [0xAA; SLAVE_BUFLEN];
        let mut t_buf = [0xAA; SLAVE_BUFLEN];

        // Initialize write buffer with increment numbers
        for (i, e) in t_buf.iter_mut().enumerate() {
            *e = i as u8;
        }

        match slave.listen().await.unwrap() {
            Transaction::Deselect => {
                info!("Probe, nothing to do");
            }
            Transaction::Read { mut handler, .. } => {
                info!("Read");
                loop {
                    match handler.handle_part(&t_buf).await.unwrap() {
                        ReadResult::Complete(n) => {
                            info!("Response complete read with {} bytes", n);
                            break;
                        }
                        ReadResult::Partial(next_handler) => {
                            handler = next_handler;
                            info!("Response to read got {} bytes, more bytes to fill", t_buf.len())
                        }
                    }
                }
            }
            Transaction::Write { mut handler, .. } => {
                info!("Write");
                loop {
                    match handler.handle_part(&mut r_buf).await.unwrap() {
                        WriteResult::Complete(n) => {
                            info!("Response complete write with {} bytes", n);
                            break;
                        }
                        WriteResult::Partial(next_handler) => {
                            handler = next_handler;
                            info!("Response to write got {} bytes, more bytes pending", r_buf.len())
                        }
                    }
                }
            }
        }
    }
}

#[embassy_executor::task]
async fn master_service(mut master: I2cMaster<'static, Async>) {
    const ADDR: u8 = 0x20;

    let mut w_buf = [0xAA; MASTER_BUFLEN];
    let mut r_buf = [0xAA; MASTER_BUFLEN];

    // Initialize write buffer with increment numbers
    for (i, e) in w_buf.iter_mut().enumerate() {
        *e = i as u8;
    }

    let mut i: usize = 0;
    loop {
        if i % 300 < 100 {
            let w_end = i % w_buf.len();
            info!("i2cm write {} bytes", w_end);
            master.write(ADDR, &w_buf[0..w_end]).await.unwrap();
        } else if i % 300 < 200 {
            let r_end = i % (r_buf.len() - 1) + 2;
            info!("i2cm read {} bytes", r_end);
            master.read(ADDR, &mut r_buf[0..r_end]).await.unwrap();
        } else {
            let tend = i % w_buf.len() + 1;
            let r_end = i % (r_buf.len() - 1) + 2;
            info!("i2cm write {} bytes, read {} bytes", tend, r_end);
            master
                .write_read(ADDR, &w_buf[0..tend], &mut r_buf[0..r_end])
                .await
                .unwrap();
        }
        i += 1;
    }
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    info!("i2c loopback example");
    let p = embassy_imxrt::init(Default::default());

    let slave = AsyncI2cSlave::new(p.FLEXCOMM2, p.PIO0_18, p.PIO0_17, Irqs, SLAVE_ADDR.unwrap(), p.DMA0_CH4).unwrap();

    let config = i2c::master::Config {
        speed: i2c::master::Speed::Fast,
        duty_cycle: DutyCycle::new(50).unwrap(),
    };
    let master = I2cMaster::new_async(p.FLEXCOMM4, p.PIO0_29, p.PIO0_30, Irqs, config, p.DMA0_CH9).unwrap();

    spawner.must_spawn(master_service(master));
    spawner.must_spawn(slave_service(slave));
}
