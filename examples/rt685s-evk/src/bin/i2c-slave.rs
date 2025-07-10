#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::i2c::slave::{Address, BlockingI2cSlave, Transaction, WriteResult};
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

const SLAVE_ADDR: Option<Address> = Address::new(0x20);
const BUFLEN: usize = 16;

#[embassy_executor::task]
async fn slave_service(mut i2c: BlockingI2cSlave<'static>) {
    // Implement a simple i2c RAM, demonstrating the features
    // of the new interface.

    let mut buf = [0u8; BUFLEN];
    let mut cur_addr = 0usize;

    loop {
        match i2c.listen().unwrap() {
            Transaction::Deselect => {
                info!("Deselection detected");
            }
            Transaction::Read { handler, .. } => {
                if cur_addr >= BUFLEN {
                    // No valid address, so can't facilitate a read, nack it.
                    info!("Rejected read transaction, no valid start address");
                    drop(handler);
                } else {
                    // Provide the data for the read, and then let go of the bus after.
                    let size = handler.handle_complete(&buf[cur_addr..], 0xFF).unwrap();
                    info!(
                        "Read transaction starting at addr {}, provided {} bytes",
                        cur_addr, size
                    );
                    cur_addr = cur_addr.saturating_add(size).min(BUFLEN);
                }
            }
            Transaction::Write { handler, .. } => {
                info!("Write request");
                let mut addr_byte = 0u8;
                match handler.handle_part(core::slice::from_mut(&mut addr_byte)).unwrap() {
                    WriteResult::Partial(handler) => {
                        if (addr_byte as usize) < BUFLEN {
                            cur_addr = addr_byte as usize;
                            info!("Received addr {}", cur_addr);

                            let size_written = handler.handle_complete(&mut buf[cur_addr..]).unwrap();
                            cur_addr += size_written;
                            info!("Received write of {} bytes to ram", size_written);
                        } else {
                            // Invalid address, nack it
                            drop(handler);
                        }
                    }
                    WriteResult::Complete(size) => {
                        assert!(size == 0);
                        info!("Empty write received");
                    }
                };
            }
        }
    }
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    info!("i2cs example - embassy_imxrt::init");
    let p = embassy_imxrt::init(Default::default());

    // NOTE: Tested with a raspberry pi 5 as master controller connected FC2 to i2c on Pi5
    //       Test program here: https://github.com/jerrysxie/pi5-i2c-test
    info!("i2cs example - I2c::new");
    let i2c = BlockingI2cSlave::new(p.FLEXCOMM2, p.PIO0_18, p.PIO0_17, SLAVE_ADDR.unwrap()).unwrap();

    spawner.must_spawn(slave_service(i2c));
}
