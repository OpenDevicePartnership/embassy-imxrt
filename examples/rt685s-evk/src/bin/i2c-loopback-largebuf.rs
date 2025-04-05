#![no_std]
#![no_main]

extern crate embassy_imxrt_examples;

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::i2c::master::{I2cMaster, Speed};
use embassy_imxrt::i2c::slave::{Address, Command, I2cSlave, Response};
use embassy_imxrt::i2c::{self, Async, MAX_I2C_CHUNK_SIZE};
use embassy_imxrt::{bind_interrupts, peripherals};
use embedded_hal_async::i2c::I2c;

const ADDR: u8 = 0x20;
const BUFLEN: usize = 2000;
const SLAVE_BUFLEN: usize = 2500; // Larger than master buffer to test end of buffer handling
const SLAVE_ADDR: Option<Address> = Address::new(ADDR);

bind_interrupts!(struct Irqs {
    FLEXCOMM2 => i2c::InterruptHandler<peripherals::FLEXCOMM2>;
    FLEXCOMM4 => i2c::InterruptHandler<peripherals::FLEXCOMM4>;
});

/// Generate a buffer with increment numbers in each segment
fn generate_buffer<const SIZE: usize>() -> [u8; SIZE] {
    let mut buf = [0xAA; SIZE];
    for (i, e) in buf.iter_mut().enumerate() {
        *e = ((i / MAX_I2C_CHUNK_SIZE) as u8) + 1;
    }
    buf
}

#[embassy_executor::task]
async fn slave_service(mut slave: I2cSlave<'static, Async>) {
    // Buffer containing data read by the master
    let t_buf: [u8; SLAVE_BUFLEN] = generate_buffer();

    // Buffer that the master writes to
    let mut r_buf = [0xAA; SLAVE_BUFLEN];
    // Buffer to compare with written data
    let expected_buf: [u8; BUFLEN] = generate_buffer();

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
                    let end = (t_offset + MAX_I2C_CHUNK_SIZE).min(t_buf.len());
                    let t_chunk = &t_buf[t_offset..end];
                    match slave.respond_to_read(t_chunk).await.unwrap() {
                        Response::Complete(n) => {
                            info!("Response complete read with {} bytes", n);
                            t_offset += n;

                            if t_offset == expected_buf.len() {
                                // Prepare for next read
                                t_offset = 0;
                            }
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
                            info!("Response complete write with {} bytes", n);

                            // Compare written data with expected data
                            assert_eq!(&r_buf[r_offset..r_offset + n], &expected_buf[r_offset..r_offset + n]);
                            r_offset += n;

                            // Check if we have received all data
                            if r_offset == expected_buf.len() {
                                // Prepare for next write
                                r_offset = 0;
                                r_buf.fill(0xAA);
                            }
                            break;
                        }
                        Response::Pending(n) => {
                            info!("Response to write got {} bytes, more bytes pending", n);

                            // Compare written data with expected data
                            assert_eq!(&r_buf[r_offset..r_offset + n], &expected_buf[r_offset..r_offset + n]);
                            r_offset += n;
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

    // Buffer containing data to write to slave
    let w_buf: [u8; BUFLEN] = generate_buffer();

    // Buffer to compare with read data
    let expected_buf: [u8; BUFLEN] = generate_buffer();
    // Buffer to store data read from slave
    let mut r_buf = [0xAA; BUFLEN];

    let mut i = 0;
    loop {
        if i < 10 {
            let w_end = w_buf.len();
            info!("i2cm write {} bytes", w_end);
            master.write(ADDR, &w_buf[0..w_end]).await.unwrap();
        } else if i < 20 {
            let r_end = r_buf.len();
            info!("i2cm read {} bytes", r_end);
            master.read(ADDR, &mut r_buf[0..r_end]).await.unwrap();

            assert_eq!(r_buf[0..r_end], expected_buf[0..r_end]);
            r_buf.fill(0xAA);
        } else {
            let w_end = w_buf.len();
            let r_end = r_buf.len();
            info!("i2cm write {} bytes, read {} bytes", w_end, r_end);
            master
                .write_read(ADDR, &w_buf[0..w_end], &mut r_buf[0..r_end])
                .await
                .unwrap();

            assert_eq!(r_buf[0..r_end], expected_buf[0..r_end]);
            r_buf.fill(0xAA);
        }
        i += 1;

        if i > 30 {
            info! {"i2c loopback largebuf test end, exiting"};
            break;
        }
    }
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
