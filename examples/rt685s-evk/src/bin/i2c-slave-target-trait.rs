//! Blocking I2C slave example using the `embedded_mcu_hal::i2c::target` trait.
//!
//! This is the trait-based counterpart to `i2c-slave.rs`. It drives the
//! same FC2 hardware in the same listen → respond → re-listen loop, but it
//! goes through the `embedded_mcu_hal::i2c::target::blocking::I2c` trait
//! instead of the inherent `I2cSlave` methods.
//!
//! Tested against the same Raspberry Pi 5 master rig as the existing
//! `i2c-slave.rs` example
//! (https://github.com/jerrysxie/pi5-i2c-test).

#![no_std]
#![no_main]

use defmt::info;
use defmt_rtt as _;
use embassy_executor::Spawner;
use embassy_imxrt::i2c::Blocking;
use embassy_imxrt::i2c::slave::{Address, I2cSlave};
use embassy_imxrt_examples as _;
use embedded_mcu_hal::i2c::SevenBitAddress;
use embedded_mcu_hal::i2c::target::Request;
use embedded_mcu_hal::i2c::target::blocking::I2c as TargetI2c;
use panic_probe as _;

const SLAVE_ADDR: Option<Address> = Address::new(0x20);
const BUFLEN: usize = 8;

#[embassy_executor::task]
async fn slave_service(mut i2c: I2cSlave<'static, Blocking>) {
    loop {
        let mut buf: [u8; BUFLEN] = [0xAA; BUFLEN];

        for (i, e) in buf.iter_mut().enumerate() {
            *e = i as u8;
        }

        let req: Request<SevenBitAddress> = match TargetI2c::<SevenBitAddress>::listen(&mut i2c) {
            Ok(r) => r,
            Err(e) => {
                info!("listen error: {:?}", defmt::Debug2Format(&e));
                continue;
            }
        };

        match req {
            Request::Stop(addr) => {
                info!("Stop @ 0x{:02X} (probe)", addr);
            }
            Request::RepeatedStart(prev_addr) => {
                info!("RepeatedStart from prev @ 0x{:02X}", prev_addr);
            }
            Request::Read(addr) => {
                info!("Read @ 0x{:02X}", addr);
                loop {
                    use embedded_mcu_hal::i2c::target::ReadStatus;
                    match TargetI2c::<SevenBitAddress>::respond_to_read(&mut i2c, &buf) {
                        Ok(ReadStatus::Complete(n)) => {
                            info!("Read complete with {} bytes", n);
                            break;
                        }
                        Ok(ReadStatus::EarlyStop(n)) => {
                            info!("Read terminated by controller after {} bytes", n);
                            break;
                        }
                        Ok(ReadStatus::NeedMore(n)) => {
                            info!("Read NeedMore: sent {} bytes so far, more requested", n);
                        }
                        Ok(_) => {
                            info!("Read: unknown status variant");
                            break;
                        }
                        Err(e) => {
                            info!("respond_to_read error: {:?}", defmt::Debug2Format(&e));
                            break;
                        }
                    }
                }
            }
            Request::Write(addr) => {
                info!("Write @ 0x{:02X}", addr);
                loop {
                    use embedded_mcu_hal::i2c::target::WriteStatus;
                    match TargetI2c::<SevenBitAddress>::respond_to_write(&mut i2c, &mut buf) {
                        Ok(WriteStatus::Stopped(n)) => {
                            info!("Write stopped after {} bytes", n);
                            break;
                        }
                        Ok(WriteStatus::Restarted(n)) => {
                            info!("Write restarted after {} bytes", n);
                            // Do NOT call recover() here: a Restarted is a
                            // healthy continuation of an in-flight master
                            // transaction (Sr + ADDR+R/W is queued on the
                            // wire). recover() would NAK the new address
                            // byte and drop the queued RepeatedStart edge,
                            // causing the master to see a spurious NACK.
                            // Reserve recover() for wedged/cancelled
                            // transfers — e.g. after dropping a
                            // respond_to_* future mid-transaction.
                            break;
                        }
                        Ok(WriteStatus::BufferFull(n)) => {
                            info!("Write BufferFull after {} bytes — supplying more buffer space", n);
                        }
                        Ok(_) => {
                            info!("Write: unknown status variant");
                            break;
                        }
                        Err(e) => {
                            info!("respond_to_write error: {:?}", defmt::Debug2Format(&e));
                            break;
                        }
                    }
                }
            }
            _ => {
                info!("unhandled request variant");
            }
        }
    }
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("i2cs target-trait example (blocking) - I2c::new");
    let i2c = I2cSlave::new_blocking(p.FLEXCOMM2, p.PIO0_18, p.PIO0_17, SLAVE_ADDR.unwrap()).unwrap();

    spawner.spawn(slave_service(i2c).unwrap());
}
