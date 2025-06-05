#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::i2c::slave::AsyncI2cSlave;
use embassy_imxrt::{bind_interrupts, i2c, peripherals};
use embedded_hal_i2c::{
    AnyAddress, AsyncI2cTarget, AsyncReadTransaction, AsyncWriteTransaction, TransactionExpectEither, WriteResult,
};
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

const SLAVE_ADDR: Option<AnyAddress> = Some(AnyAddress::Seven(0x20));
const BUFLEN: usize = 512;

bind_interrupts!(struct Irqs {
    FLEXCOMM2 => i2c::InterruptHandler<peripherals::FLEXCOMM2>;
});

#[embassy_executor::task]
async fn slave_service(mut i2c: AsyncI2cSlave<'static>) {
    // Implement a simple i2c RAM, demonstrating the features
    // of the new interface.

    let mut buf = [0u8; BUFLEN];
    let mut cur_addr = 0usize;

    let mut expect_read = false;

    loop {
        let mut addr = [0u8; 2];
        let result: TransactionExpectEither<_, _> = if expect_read && cur_addr < BUFLEN {
            i2c.listen_expect_read(SLAVE_ADDR.unwrap(), buf.get(cur_addr..).unwrap_or_default())
                .await
                .unwrap()
                .into()
        } else {
            i2c.listen_expect_write(SLAVE_ADDR.unwrap(), &mut addr)
                .await
                .unwrap()
                .into()
        };

        use TransactionExpectEither::*;
        match result {
            Deselect => {
                expect_read = false;
                info!("Deselection detected");
            }
            Read { handler, .. } => {
                if cur_addr >= BUFLEN {
                    // No valid address, so can't facilitate a read, nack it.
                    info!("Rejected read transaction, no valid start address");
                    drop(handler);
                } else {
                    // Provide the data for the read, and then let go of the bus after.
                    let size = handler.handle_complete(&buf[cur_addr..], 0xFF).await.unwrap();
                    info!(
                        "Read transaction starting at addr {}, provided {} bytes",
                        cur_addr, size
                    );
                    cur_addr = cur_addr.saturating_add(size).min(BUFLEN);
                }
            }
            ExpectedCompleteRead { size } => {
                info!(
                    "Expected read transaction starting at addr {}, provided {} bytes",
                    cur_addr, size
                );
                cur_addr = cur_addr.saturating_add(size).min(BUFLEN);
            }
            ExpectedPartialRead { handler } => {
                let size =
                    buf.get(cur_addr..).unwrap_or_default().len() + handler.handle_complete(&[], 0xFF).await.unwrap();
                info!(
                    "Expected partial read transaction starting at addr {}, provided {} bytes",
                    cur_addr, size
                );
                cur_addr = cur_addr.saturating_add(size).min(BUFLEN);
            }
            Write { handler, .. } => {
                info!("Write request");
                let mut addr = [0u8; 2];
                match handler.handle_part(&mut addr).await.unwrap() {
                    WriteResult::Partial(handler) => {
                        let new_addr: usize = u16::from_le_bytes(addr).into();
                        if new_addr < BUFLEN {
                            cur_addr = new_addr;
                            info!("Received addr {}", cur_addr);
                            expect_read = true;

                            let size_written = handler.handle_complete(&mut buf[cur_addr..]).await.unwrap();
                            cur_addr += size_written;
                            info!("Received write of {} bytes to ram", size_written);
                        } else {
                            // Invalid address, nack it
                            drop(handler);
                        }
                    }
                    WriteResult::Complete(size) => {
                        info!("Incomplete address write of size {} received, ignoring", size);
                    }
                };
            }
            ExpectedCompleteWrite { size } => {
                info!("Expected incomplete address write of size {} received, ignoring", size);
            }
            ExpectedPartialWrite { handler } => {
                info!("Expected partial write");
                let new_addr: usize = u16::from_le_bytes(addr).into();
                if new_addr < BUFLEN {
                    cur_addr = new_addr;
                    info!("Received addr {}", cur_addr);
                    expect_read = true;

                    let size_written = handler.handle_complete(&mut buf[cur_addr..]).await.unwrap();
                    cur_addr += size_written;
                    info!("Received write of {} bytes to ram", size_written);
                } else {
                    // Invalid address, nack it
                    drop(handler);
                }
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
    let i2c = AsyncI2cSlave::new(p.FLEXCOMM2, p.PIO0_18, p.PIO0_17, Irqs, SLAVE_ADDR.unwrap(), p.DMA0_CH4).unwrap();

    spawner.must_spawn(slave_service(i2c));
}
