#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::i2c::slave::{Address, Command, I2cSlave, Response};
use embassy_imxrt::i2c::Blocking;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

const SLAVE_ADDR: Option<Address> = Address::new(0x20);
const BUFLEN: usize = 8;

#[embassy_executor::task]
async fn slave_service(i2c: I2cSlave<'static, Blocking>) {
    loop {
        let mut buf: [u8; BUFLEN] = [0xAA; BUFLEN];

        for (i, e) in buf.iter_mut().enumerate() {
            *e = i as u8;
        }

        match i2c.listen().unwrap() {
            Command::Probe => {
                info!("Probe, nothing to do");
            }
            Command::Read => {
                info!("Read");
                loop {
                    match i2c.respond_to_read(&buf).unwrap() {
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
                    match i2c.respond_to_write(&mut buf).unwrap() {
                        Response::Complete(n) => {
                            info!("Response complete write with {} bytes", n);
                            break;
                        }
                        Response::Pending(n) => info!("Response to write got {} bytes, more bytes pending", n),
                    }
                }
            }
        }
    }
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    // NOTE: Tested with a raspberry pi 5 as master controller connected FC2 to i2c on Pi5
    //       Test program here: https://github.com/jerrysxie/pi5-i2c-test
    info!("i2cs example - I2c::new");
    let i2c = I2cSlave::new_blocking(p.FLEXCOMM2, p.PIO0_18, p.PIO0_17, SLAVE_ADDR.unwrap()).unwrap();

    spawner.must_spawn(slave_service(i2c));
}
