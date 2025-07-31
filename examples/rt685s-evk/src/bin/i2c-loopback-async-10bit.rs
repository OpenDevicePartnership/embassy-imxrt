#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::i2c::master::I2cMaster;
use embassy_imxrt::i2c::slave::{Address, Command, I2cSlave, Response};
use embassy_imxrt::i2c::{self, Async};
use embassy_imxrt::{bind_interrupts, peripherals};
use embedded_hal_async::i2c::I2c;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

const ADDR: u16 = 0x0123;
const MASTER_BUFLEN: usize = 8;
// slave buffer has to be 1 bigger than master buffer because master does not
// handle end of read properly
const SLAVE_BUFLEN: usize = MASTER_BUFLEN + 1;
const SLAVE_ADDR: Option<Address> = Address::new_10bit(ADDR);

bind_interrupts!(struct Irqs {
    FLEXCOMM2 => i2c::InterruptHandler<peripherals::FLEXCOMM2>;
    FLEXCOMM4 => i2c::InterruptHandler<peripherals::FLEXCOMM4>;
});

/// Generate a buffer with increment numbers
fn generate_buffer<const SIZE: usize>() -> [u8; SIZE] {
    let mut buf = [0xAA; SIZE];
    for (i, e) in buf.iter_mut().enumerate() {
        *e = i as u8;
    }
    buf
}

#[embassy_executor::task]
async fn slave_service(mut slave: I2cSlave<'static, Async>) {
    loop {
        // Buffer containing data read by the master
        let t_buf: [u8; SLAVE_BUFLEN] = generate_buffer();

        // Buffer that the master writes to
        let mut r_buf = [0xAA; SLAVE_BUFLEN];
        // Buffer to compare with written data
        let expected_buf: [u8; SLAVE_BUFLEN] = generate_buffer();

        match slave.listen().await.unwrap() {
            Command::Probe => {
                info!("Probe, nothing to do");
            }
            Command::Read => {
                info!("Read");
                loop {
                    match slave.respond_to_read(&t_buf).await.unwrap() {
                        Response::Complete(n) => {
                            info!("Response complete read with {} bytes", n);
                            break;
                        }
                        Response::Pending(n) => info!("Response to read got {} bytes, more bytes to fill", n),
                    }
                }
            }
            Command::Write => {
                info!("Write");
                loop {
                    match slave.respond_to_write(&mut r_buf).await.unwrap() {
                        Response::Complete(n) => {
                            info!("Response complete write with {} bytes", n);
                            info!("i2cm write data: {:x}", r_buf[0..n]);

                            // Compare written data with expected data
                            // Ensures that the second byte of 10 bit address is handled properly
                            assert!(r_buf[0..n] == expected_buf[0..n]);
                            break;
                        }
                        Response::Pending(n) => info!("Response to write got {} bytes, more bytes pending", n),
                    }
                }
            }
        }
    }
}

#[embassy_executor::task]
async fn master_service(mut master: I2cMaster<'static, Async>) {
    const ADDR: u16 = 0x0123;

    // Buffer containing data to write to slave
    let w_buf: [u8; MASTER_BUFLEN] = generate_buffer();

    // Buffer to compare with read data
    let expected_buf: [u8; SLAVE_BUFLEN] = generate_buffer();

    let mut i: usize = 0;
    loop {
        // Reset read buffer to ensure fresh data
        let mut r_buf = [0xAA; MASTER_BUFLEN];

        if i < 10 {
            let w_end = i % w_buf.len();
            info!("i2cm write {} bytes", w_end);
            master.write(ADDR, &w_buf[0..w_end]).await.unwrap();
        } else if i < 20 {
            let r_end = i % (r_buf.len() - 1) + 2;
            info!("i2cm read {} bytes", r_end);
            master.read(ADDR, &mut r_buf[0..r_end]).await.unwrap();
            info!("i2cm read data: {:x}", r_buf[0..r_end]);

            // Compare read data with expected data
            // Ensures that the second byte of 10 bit address is handled properly
            assert!(r_buf[0..r_end] == expected_buf[0..r_end]);
        } else {
            let tend = i % w_buf.len() + 1;
            let r_end = i % (r_buf.len() - 1) + 2;
            info!("i2cm write {} bytes, read {} bytes", tend, r_end);
            master
                .write_read(ADDR, &w_buf[0..tend], &mut r_buf[0..r_end])
                .await
                .unwrap();
            info!("i2cm read data: {:x}", r_buf[0..r_end]);

            // Compare read data with expected data
            // Ensures that the second byte of 10 bit address is handled properly
            assert!(r_buf[0..r_end] == expected_buf[0..r_end]);
        }
        i += 1;

        if i == 30 {
            info!("i2c 10 bit loopback test end");
            break;
        }
    }
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("i2c loopback example");

    let slave = I2cSlave::new_async(p.FLEXCOMM2, p.PIO0_18, p.PIO0_17, Irqs, SLAVE_ADDR.unwrap(), p.DMA0_CH4).unwrap();

    let master = I2cMaster::new_async(p.FLEXCOMM4, p.PIO0_29, p.PIO0_30, Irqs, Default::default(), p.DMA0_CH9).unwrap();

    spawner.must_spawn(master_service(master));
    spawner.must_spawn(slave_service(slave));
}
