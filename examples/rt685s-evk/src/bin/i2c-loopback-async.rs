#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::i2c::master::{DutyCycle, I2cMaster};
use embassy_imxrt::i2c::slave::{Address, Command, I2cSlave, Response};
use embassy_imxrt::i2c::{self, Async};
use embassy_imxrt::{bind_interrupts, peripherals};
use embedded_hal_async::i2c::I2c;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

const ADDR: u8 = 0x20;
const MASTER_BUFLEN: usize = 8;
// slave buffer has to be 1 bigger than master buffer because master does not
// handle end of read properly
const SLAVE_BUFLEN: usize = MASTER_BUFLEN + 1;
const SLAVE_ADDR: Option<Address> = Address::new(ADDR);

bind_interrupts!(struct Irqs {
    FLEXCOMM2 => i2c::InterruptHandler<peripherals::FLEXCOMM2>;
    FLEXCOMM4 => i2c::InterruptHandler<peripherals::FLEXCOMM4>;
});

#[embassy_executor::task]
async fn slave_service(mut slave: I2cSlave<'static, Async>) {
    loop {
        let mut r_buf = [0xAA; SLAVE_BUFLEN];
        let mut t_buf = [0xAA; SLAVE_BUFLEN];

        // Initialize write buffer with increment numbers
        for (i, e) in t_buf.iter_mut().enumerate() {
            *e = i as u8;
        }

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
    let p = embassy_imxrt::init(Default::default());

    info!("i2c loopback example");

    let slave = I2cSlave::new_async(p.FLEXCOMM2, p.PIO0_18, p.PIO0_17, Irqs, SLAVE_ADDR.unwrap(), p.DMA0_CH4).unwrap();

    let config = i2c::master::Config {
        speed: i2c::master::Speed::Fast,
        duty_cycle: DutyCycle::new(50).unwrap(),
        ..Default::default()
    };
    let master = I2cMaster::new_async(p.FLEXCOMM4, p.PIO0_29, p.PIO0_30, Irqs, config, p.DMA0_CH9).unwrap();

    spawner.must_spawn(master_service(master));
    spawner.must_spawn(slave_service(slave));
}
