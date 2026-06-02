//! I2C slave async example using the `embedded_mcu_hal::i2c::target` trait.
//!
//! This is the trait-based counterpart to `i2c-slave-async.rs`. It drives
//! the same FC2 hardware in the same listen → respond → re-listen loop, but
//! it goes through the `embedded_mcu_hal::i2c::target::asynch::I2c` trait
//! instead of the inherent `I2cSlave` methods. Differences from the
//! inherent example:
//!
//! * `listen()` returns a `Request<SevenBitAddress>` carrying the matched
//!   address; the example logs it.
//! * `respond_to_write()` / `respond_to_read()` return `WriteStatus` /
//!   `ReadStatus` enums that distinguish `Stopped` / `Restarted` /
//!   `BufferFull` (for writes) and `Complete` / `NeedMore` / `EarlyStop`
//!   (for reads).
//! * `RepeatedStart(prev_addr)` is surfaced as a separate `listen()` event
//!   between a write and a read on the same controller transaction.
//! * `recover()` is called from the `Restarted` branch as a no-op
//!   demonstration; in production it would only be needed after a
//!   cancelled `respond_*` future.
//!
//! Tested against the same Raspberry Pi 5 master rig as the existing
//! `i2c-slave-async.rs` example
//! (https://github.com/jerrysxie/pi5-i2c-test).

#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::i2c::slave::{Address, I2cSlave};
use embassy_imxrt::i2c::{self, Async};
use embassy_imxrt::{bind_interrupts, peripherals};
// Bring the target trait methods into scope so we go through the trait
// instead of the inherent API.
use embedded_mcu_hal::i2c::SevenBitAddress;
use embedded_mcu_hal::i2c::target::Request;
use embedded_mcu_hal::i2c::target::asynch::I2c as TargetI2c;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

const SLAVE_ADDR: Option<Address> = Address::new(0x20);
const BUFLEN: usize = 8;

bind_interrupts!(struct Irqs {
    FLEXCOMM2 => i2c::InterruptHandler<peripherals::FLEXCOMM2>;
});

#[embassy_executor::task]
async fn slave_service(mut i2c: I2cSlave<'static, Async>) {
    loop {
        let mut buf: [u8; BUFLEN] = [0xAA; BUFLEN];

        for (i, e) in buf.iter_mut().enumerate() {
            *e = i as u8;
        }

        // Go through the target trait — note `<_ as TargetI2c<SevenBitAddress>>`
        // disambiguates between the 7-bit and 10-bit trait impls. The
        // address mode is checked at runtime against the address the slave
        // was constructed with; a mismatch returns `ErrorKind::Other`.
        let req: Request<SevenBitAddress> = match TargetI2c::<SevenBitAddress>::listen(&mut i2c).await {
            Ok(r) => r,
            Err(e) => {
                info!("listen error: {:?}", defmt::Debug2Format(&e));
                continue;
            }
        };

        match req {
            Request::Stop(addr) => {
                // A probe (address-only transaction terminated by STOP)
                // surfaces here. The inherent API reports the same event
                // as `Command::Probe { addr }`.
                info!("Stop @ 0x{:02X} (probe)", addr);
            }
            Request::RepeatedStart(prev_addr) => {
                // Surfaced when a previous respond_to_* observed a Sr.
                info!("RepeatedStart from prev @ 0x{:02X}", prev_addr);
            }
            Request::Read(addr) => {
                info!("Read @ 0x{:02X}", addr);
                loop {
                    use embedded_mcu_hal::i2c::target::ReadStatus;
                    match TargetI2c::<SevenBitAddress>::respond_to_read(&mut i2c, &buf).await {
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
                            // Loop and supply more bytes. In a real
                            // application you would prepare the next chunk
                            // here; for the demo we just resend `buf`.
                        }
                        Ok(_) => {
                            // ReadStatus is `#[non_exhaustive]`; future
                            // variants are gracefully ignored.
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
                    match TargetI2c::<SevenBitAddress>::respond_to_write(&mut i2c, &mut buf).await {
                        Ok(WriteStatus::Stopped(n)) => {
                            info!("Write stopped after {} bytes", n);
                            break;
                        }
                        Ok(WriteStatus::Restarted(n)) => {
                            info!(
                                "Write restarted after {} bytes — next listen will surface RepeatedStart",
                                n
                            );
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
                            // Loop and continue draining.
                        }
                        Ok(_) => {
                            // WriteStatus is `#[non_exhaustive]`; future
                            // variants are gracefully ignored.
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
            // GeneralCall / SmbusAlert are not produced by this peripheral
            // in v1; the catch-all covers any future variants.
            _ => {
                info!("unhandled request variant");
            }
        }
    }
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("i2cs target-trait example - I2c::new");
    let i2c = I2cSlave::new_async(p.FLEXCOMM2, p.PIO0_18, p.PIO0_17, Irqs, SLAVE_ADDR.unwrap(), p.DMA0_CH4).unwrap();

    spawner.spawn(slave_service(i2c).unwrap());
}
