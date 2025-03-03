#![no_std]
#![no_main]

extern crate embassy_imxrt_examples;

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::i2c::master::{I2cMaster, Speed};
use embassy_imxrt::i2c::slave::{Address, Command, I2cSlave, Response};
use embassy_imxrt::i2c::{self, Async};
use embassy_imxrt::{bind_interrupts, peripherals};
use embedded_hal_async::i2c::I2c;

const ADDR: u8 = 0x20;
const MAX_I2C_CHUNK_SIZE: usize = 512;
const MASTER_BUFLEN: usize = 2000;
// slave buffer has to be 1 bigger than master buffer for each chunk
//because master does not handle end of read properly
const SLAVE_BUFLEN: usize = MASTER_BUFLEN + (MASTER_BUFLEN / MAX_I2C_CHUNK_SIZE) + 1;
const SLAVE_ADDR: Option<Address> = Address::new(ADDR);

bind_interrupts!(struct Irqs {
    FLEXCOMM2 => i2c::InterruptHandler<peripherals::FLEXCOMM2>;
    FLEXCOMM4 => i2c::InterruptHandler<peripherals::FLEXCOMM4>;
});

#[embassy_executor::task]
async fn slave_service(mut slave: I2cSlave<'static, Async>) {
    let mut r_buf = [0xAA; SLAVE_BUFLEN];
    let mut t_buf = [0xAA; SLAVE_BUFLEN];

    // Initialize write buffer with increment numbers
    for (i, e) in t_buf.iter_mut().enumerate() {
        *e = ((i / MAX_I2C_CHUNK_SIZE) as u8) + 1;
    }
    for (i, e) in r_buf.iter_mut().enumerate() {
        *e = ((i as u8) % 255) + 1;
    }

    let mut r_offset = 0;
    let mut t_offset = 0;

    loop {
        match slave.listen().await.unwrap() {
            Command::Probe => {
                info!("Probe, nothing to do");
            }
            Command::Read => {
                info!("Read");
                loop {
                    let end = (t_offset + MAX_I2C_CHUNK_SIZE + 1).min(t_buf.len());
                    let t_chunk = &t_buf[t_offset..end];
                    match slave.respond_to_read(t_chunk).await.unwrap() {
                        Response::Complete(n) => {
                            t_offset += n;
                            info!("Response complete read with {} bytes", n);
                            break;
                        }
                        Response::Pending(n) => {
                            t_offset += n;
                            info!("Response to read got {} bytes, more bytes to fill", n);
                        }
                    }
                }
            }
            Command::Write => {
                info!("Write");
                loop {
                    let end = (r_offset + MAX_I2C_CHUNK_SIZE).min(r_buf.len());
                    let r_chunk = &mut r_buf[r_offset..end];
                    match slave.respond_to_write(r_chunk).await.unwrap() {
                        Response::Complete(n) => {
                            r_offset += n;
                            if n == 0 {
                                info!("Restart detected");
                            } else {
                                info!("Response complete write with {} bytes", n);
                            }
                            break;
                        }
                        Response::Pending(n) => {
                            r_offset += n;
                            info!("Response to write got {} bytes, more bytes pending", n);
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
        *e = ((i / MAX_I2C_CHUNK_SIZE) as u8) + 1;
    }

    let w_end = w_buf.len();
    info!("i2cm write {} bytes", w_end);
    master.write(ADDR, &w_buf[0..w_end]).await.unwrap();

    let r_end = r_buf.len();
    info!("i2cm read {} bytes", r_end);
    master.read(ADDR, &mut r_buf[0..r_end]).await.unwrap();
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    info!("i2c loopback bigbuffer example");
    let p = embassy_imxrt::init(Default::default());

    let slave = I2cSlave::new_async(p.FLEXCOMM2, p.PIO0_18, p.PIO0_17, Irqs, SLAVE_ADDR.unwrap(), p.DMA0_CH4).unwrap();

    let master = I2cMaster::new_async(p.FLEXCOMM4, p.PIO0_29, p.PIO0_30, Irqs, Speed::Standard, p.DMA0_CH9).unwrap();

    spawner.must_spawn(master_service(master));
    spawner.must_spawn(slave_service(slave));
}
