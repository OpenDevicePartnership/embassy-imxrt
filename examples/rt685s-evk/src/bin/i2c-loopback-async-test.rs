#![no_std]
#![no_main]

extern crate embassy_imxrt_examples;

use cortex_m::asm::delay;
use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::gpio::{DriveMode, DriveStrength, Flex, GpioPin, SenseEnabled, SlewRate};
use embassy_imxrt::i2c::slave::{
    Address, AsyncI2cSlave, ReadResult, Transaction, TransactionExpectRead, TransactionExpectWrite, WriteResult,
};
use embassy_imxrt::peripherals::{DMA0_CH4, FLEXCOMM2, PIO0_17, PIO0_18, PIO0_29, PIO0_30};
use embassy_imxrt::{bind_interrupts, i2c, peripherals, Peri};
use embassy_sync::blocking_mutex::raw::CriticalSectionRawMutex;
use embassy_sync::semaphore::{GreedySemaphore, Semaphore as _};

bind_interrupts!(struct Irqs {
    FLEXCOMM2 => i2c::InterruptHandler<peripherals::FLEXCOMM2>;
});

type Semaphore = GreedySemaphore<CriticalSectionRawMutex>;

struct I2CTester {
    scl: Flex<'static, SenseEnabled>,
    sda: Flex<'static, SenseEnabled>,
}

impl I2CTester {
    fn new(scl: Peri<'static, impl GpioPin>, sda: Peri<'static, impl GpioPin>) -> Self {
        let mut scl = Flex::<'_, SenseEnabled>::new(scl);
        let mut sda = Flex::<'_, SenseEnabled>::new(sda);

        scl.set_high();
        scl.set_as_output(DriveMode::OpenDrain, DriveStrength::Normal, SlewRate::Standard);

        sda.set_high();
        sda.set_as_output(DriveMode::OpenDrain, DriveStrength::Normal, SlewRate::Standard);

        I2CTester { scl, sda }
    }

    async fn start(&mut self) {
        self.sda.set_high();
        delay(1500);

        self.scl.set_high();
        self.scl.wait_for_high().await;
        delay(1500);

        self.sda.set_low();
        delay(1500);

        self.scl.set_low();
        delay(1500);
    }

    async fn stop(&mut self) {
        self.sda.set_low();
        delay(1500);

        self.scl.set_high();
        self.scl.wait_for_high().await;
        delay(1500);

        self.sda.set_high();
        delay(1500);
    }

    async fn i2c_byte(&mut self, mut send: u8, ack: bool) -> (u8, bool) {
        // Send bits
        for _ in 0..8 {
            self.sda.set_level((send & 0x80 != 0).into());
            delay(1500);
            self.scl.set_high();
            self.scl.wait_for_high().await;
            delay(1500);
            send = (send << 1) | if self.sda.is_high() { 1 } else { 0 };
            self.scl.set_low();
            delay(1500);
        }

        self.sda.set_level((!ack).into());
        delay(1500);
        self.scl.set_high();
        self.scl.wait_for_high().await;
        delay(1500);
        let ack = self.sda.is_low();
        self.scl.set_low();
        delay(1500);

        (send, ack)
    }

    async fn i2c_byte_checked(&mut self, send: u8, ack: bool, expected: u8, expected_ack: bool) {
        let (res, ack) = self.i2c_byte(send, ack).await;
        assert_eq!(res, expected);
        assert_eq!(ack, expected_ack);
    }
}

macro_rules! test_cases {
    ($slave_name:ident, $slave_struct:ident, $tester_name:ident, $tester_struct:ident, [$(($addr:expr, $slave:tt, $tester:tt)),* $(,)?]) => {
        #[embassy_executor::task]
        async fn $slave_name(
            mut flexcomm: Peri<'static, FLEXCOMM2>,
            mut scl: Peri<'static, PIO0_18>,
            mut sda: Peri<'static, PIO0_17>,
            mut dma: Peri<'static, DMA0_CH4>,
        ) {
            $(
                {
                    let mut $slave_struct = AsyncI2cSlave::new(flexcomm.reborrow(), scl.reborrow(), sda.reborrow(), Irqs, $addr, dma.reborrow()).unwrap();

                    test_sync_slave().await;

                    $slave
                }
            )*

            defmt::info!("Slave completed tests");
        }

        #[embassy_executor::task]
        async fn $tester_name(scl: Peri<'static, PIO0_29>, sda: Peri<'static, PIO0_30>) {
            let mut $tester_struct = I2CTester::new(scl, sda);

            $(
                {
                    test_sync_master().await;

                    $tester
                }
            )*

            defmt::info!("Tester completed tests");
        }
    }
}

test_cases!(
    slave_under_test,
    i2c,
    tester,
    tester,
    [
        //
        // == Basic transactions ==
        //
        // 7 bit write
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [1, 2, 3, 4]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.stop().await;
            }
        ),
        // 7 bit read
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(handler.handle_complete(&[1, 2, 3, 4], 0xff).await.unwrap(), 4);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 2, true).await;
                tester.i2c_byte_checked(0xff, true, 3, true).await;
                tester.i2c_byte_checked(0xff, false, 4, false).await;
                tester.stop().await;
            }
        ),
        // 7 bit write then read with restart (should give single deselect)
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [1, 2, 3, 4]);
                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(handler.handle_complete(&[5, 6, 7, 8], 0xff).await.unwrap(), 4);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 5, true).await;
                tester.i2c_byte_checked(0xff, true, 6, true).await;
                tester.i2c_byte_checked(0xff, true, 7, true).await;
                tester.i2c_byte_checked(0xff, false, 8, false).await;
                tester.stop().await;
            }
        ),
        // 7 bit write then read with stop and start inbetween (should give two deselect)
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [1, 2, 3, 4]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(handler.handle_complete(&[5, 6, 7, 8], 0xff).await.unwrap(), 4);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.stop().await;
                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 5, true).await;
                tester.i2c_byte_checked(0xff, true, 6, true).await;
                tester.i2c_byte_checked(0xff, true, 7, true).await;
                tester.i2c_byte_checked(0xff, false, 8, false).await;
                tester.stop().await;
            }
        ),
        // 7bit write then write with restart
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [1, 2, 3, 4]);
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [5, 6, 7, 8]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(5, false, 5, true).await;
                tester.i2c_byte_checked(6, false, 6, true).await;
                tester.i2c_byte_checked(7, false, 7, true).await;
                tester.i2c_byte_checked(8, false, 8, true).await;
                tester.stop().await;
            }
        ),
        // 7bit write then write with start stop
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [1, 2, 3, 4]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [5, 6, 7, 8]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.stop().await;
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(5, false, 5, true).await;
                tester.i2c_byte_checked(6, false, 6, true).await;
                tester.i2c_byte_checked(7, false, 7, true).await;
                tester.i2c_byte_checked(8, false, 8, true).await;
                tester.stop().await;
            }
        ),
        // 10 bit write
        (
            Address::TenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [1, 2, 3, 4]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0xF0, false, 0xF0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.stop().await;
            }
        ),
        // 10 bit read with only a zero sized write beforehand
        (
            Address::TenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(handler.handle_complete(&mut []).await.unwrap(), 0);
                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(handler.handle_complete(&[1, 2, 3, 4], 0xff).await.unwrap(), 4);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0xF0, false, 0xF0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.start().await;
                tester.i2c_byte_checked(0xF1, false, 0xF1, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 2, true).await;
                tester.i2c_byte_checked(0xff, true, 3, true).await;
                tester.i2c_byte_checked(0xff, false, 4, false).await;
                tester.stop().await;
            }
        ),
        // 10 bit write then read with restart
        (
            Address::TenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [1, 2, 3, 4]);
                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(handler.handle_complete(&[5, 6, 7, 8], 0xff).await.unwrap(), 4);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0xF0, false, 0xF0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.start().await;
                tester.i2c_byte_checked(0xf1, false, 0xf1, true).await;
                tester.i2c_byte_checked(0xff, true, 5, true).await;
                tester.i2c_byte_checked(0xff, true, 6, true).await;
                tester.i2c_byte_checked(0xff, true, 7, true).await;
                tester.i2c_byte_checked(0xff, false, 8, false).await;
                tester.stop().await;
            }
        ),
        // 10bit write then write with restart
        (
            Address::TenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [1, 2, 3, 4]);
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [5, 6, 7, 8]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.i2c_byte_checked(5, false, 5, true).await;
                tester.i2c_byte_checked(6, false, 6, true).await;
                tester.i2c_byte_checked(7, false, 7, true).await;
                tester.i2c_byte_checked(8, false, 8, true).await;
                tester.stop().await;
            }
        ),
        // 10bit write then write with start stop
        (
            Address::TenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [1, 2, 3, 4]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [5, 6, 7, 8]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.stop().await;
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.i2c_byte_checked(5, false, 5, true).await;
                tester.i2c_byte_checked(6, false, 6, true).await;
                tester.i2c_byte_checked(7, false, 7, true).await;
                tester.i2c_byte_checked(8, false, 8, true).await;
                tester.stop().await;
            }
        ),
        // 10 bit read without write first (should nack)
        // additional zero byte write after to end listen
        (
            Address::TenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(handler.handle_complete(&mut []).await.unwrap(), 0);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0xf1, false, 0xf1, false).await;
                tester.stop().await;
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.stop().await;
            }
        ),
        // 10 bit read after write with start stop in between (should nack)
        // additional zero byte write after to end listen
        (
            Address::TenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [1, 2, 3, 4]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(handler.handle_complete(&mut []).await.unwrap(), 0);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.stop().await;
                tester.start().await;
                tester.i2c_byte_checked(0xf1, false, 0xf1, false).await;
                tester.stop().await;
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.stop().await;
            }
        ),
        //
        // == Behaviour when nacking ==
        //

        // Nack address on handler drop (write)
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                drop(handler);
            },
            {
                tester.start().await;
                let (addr, ack) = tester.i2c_byte(0x40, false).await;
                assert_eq!(addr, 0x40);
                assert!(!ack);
                tester.stop().await;
            }
        ),
        // Nack address on handler drop (read)
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                drop(handler);
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, false).await;
                tester.stop().await;
            }
        ),
        // Nack multiple bytes on write handler drop after accepting a byte
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let WriteResult::Partial(_) = handler.handle_part(&mut [0]).await.unwrap() else {
                    panic!("Unexpected handle_part result on write.");
                };
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(0, false, 0, false).await;
                tester.i2c_byte_checked(1, false, 1, false).await;
                tester.i2c_byte_checked(2, false, 2, false).await;
                tester.stop().await;
            }
        ),
        // Provide overrun on dropping a read handler after providing a byte
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let ReadResult::Partial(_) = handler.handle_part(&[0]).await.unwrap() else {
                    panic!("Unexpected handle_part result on read.");
                };
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 0, true).await;
                tester.i2c_byte_checked(0xff, true, 0xff, true).await;
                tester.i2c_byte_checked(0xff, true, 0xff, true).await;
                tester.i2c_byte_checked(0xff, true, 0xff, true).await;
                tester.i2c_byte_checked(0xff, false, 0xff, false).await;
                tester.stop().await;
            }
        ),
        // Nack first transaction, then ack second
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                drop(handler);
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [1, 2, 3, 4]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, false).await;
                tester.stop().await;
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.stop().await;
            }
        ),
        //
        // == Automatic acknowledgement tests
        //

        // 7bit Expect write, receive a matching write
        (
            Address::SevenBit(0x20),
            {
                let mut data = [0u8; 4];
                let TransactionExpectWrite::ExpectedPartialWrite { handler } = i2c
                    .listen_expect_write(Address::SevenBit(0x20), &mut data)
                    .await
                    .unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(data, [1, 2, 3, 4]);
                assert_eq!(handler.handle_complete(&mut []).await.unwrap(), 0);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.stop().await;
            }
        ),
        // 7bit Expect read, receive a matching read
        (
            Address::SevenBit(0x20),
            {
                let TransactionExpectRead::ExpectedCompleteRead { size: 4 } = i2c
                    .listen_expect_read(Address::SevenBit(0x20), &[1, 2, 3, 4])
                    .await
                    .unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 2, true).await;
                tester.i2c_byte_checked(0xff, true, 3, true).await;
                tester.i2c_byte_checked(0xff, false, 4, false).await;
                tester.stop().await;
            }
        ),
        // 7bit Expect write, receive read
        (
            Address::SevenBit(0x20),
            {
                let mut data = [0u8; 4];
                let TransactionExpectWrite::Read { handler, .. } = i2c
                    .listen_expect_write(Address::SevenBit(0x20), &mut data)
                    .await
                    .unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(data, [0; 4]);
                assert_eq!(handler.handle_complete(&[1, 2, 3, 4], 0xff).await.unwrap(), 4);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 2, true).await;
                tester.i2c_byte_checked(0xff, true, 3, true).await;
                tester.i2c_byte_checked(0xff, false, 4, false).await;
                tester.stop().await;
            }
        ),
        // 7bit Expect read, receive write
        (
            Address::SevenBit(0x20),
            {
                let TransactionExpectRead::Write { handler, .. } = i2c
                    .listen_expect_read(Address::SevenBit(0x20), &[5, 6, 7, 8])
                    .await
                    .unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [1, 2, 3, 4]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.stop().await;
            }
        ),
        // 10bit Expected write-read transaction
        (
            Address::TenBit(0x20),
            {
                let mut data = [0u8; 4];
                let TransactionExpectWrite::ExpectedPartialWrite { handler, .. } =
                    i2c.listen_expect_write(Address::TenBit(0x20), &mut data).await.unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(data, [1, 2, 3, 4]);
                assert_eq!(handler.handle_complete(&mut []).await.unwrap(), 0);
                let TransactionExpectRead::ExpectedCompleteRead { size: 4 } = i2c
                    .listen_expect_read(Address::TenBit(0x20), &[5, 6, 7, 8])
                    .await
                    .unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.start().await;
                tester.i2c_byte_checked(0xf1, false, 0xf1, true).await;
                tester.i2c_byte_checked(0xff, true, 5, true).await;
                tester.i2c_byte_checked(0xff, true, 6, true).await;
                tester.i2c_byte_checked(0xff, true, 7, true).await;
                tester.i2c_byte_checked(0xff, false, 8, false).await;
                tester.stop().await;
            }
        ),
        // 10bit Expected write-write transaction
        (
            Address::TenBit(0x20),
            {
                let mut data = [0u8; 4];
                let TransactionExpectWrite::ExpectedPartialWrite { handler, .. } =
                    i2c.listen_expect_write(Address::TenBit(0x20), &mut data).await.unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(data, [1, 2, 3, 4]);
                assert_eq!(handler.handle_complete(&mut []).await.unwrap(), 0);
                let TransactionExpectWrite::ExpectedPartialWrite { handler, .. } =
                    i2c.listen_expect_write(Address::TenBit(0x20), &mut data).await.unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(data, [5, 6, 7, 8]);
                assert_eq!(handler.handle_complete(&mut []).await.unwrap(), 0);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.i2c_byte_checked(5, false, 5, true).await;
                tester.i2c_byte_checked(6, false, 6, true).await;
                tester.i2c_byte_checked(7, false, 7, true).await;
                tester.i2c_byte_checked(8, false, 8, true).await;
                tester.stop().await;
            }
        ),
        // 10bit Expected write-read transaction, got write-write
        (
            Address::TenBit(0x20),
            {
                let mut data = [0u8; 4];
                let TransactionExpectWrite::ExpectedPartialWrite { handler, .. } =
                    i2c.listen_expect_write(Address::TenBit(0x20), &mut data).await.unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(data, [1, 2, 3, 4]);
                assert_eq!(handler.handle_complete(&mut []).await.unwrap(), 0);
                let TransactionExpectRead::Write { handler, .. } = i2c
                    .listen_expect_read(Address::TenBit(0x20), &[5, 6, 7, 8])
                    .await
                    .unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [5, 6, 7, 8]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.i2c_byte_checked(5, false, 5, true).await;
                tester.i2c_byte_checked(6, false, 6, true).await;
                tester.i2c_byte_checked(7, false, 7, true).await;
                tester.i2c_byte_checked(8, false, 8, true).await;
                tester.stop().await;
            }
        ),
        // 10bit Expected write-write transaction, got write-read
        (
            Address::TenBit(0x20),
            {
                let mut data = [0u8; 4];
                let TransactionExpectWrite::ExpectedPartialWrite { handler, .. } =
                    i2c.listen_expect_write(Address::TenBit(0x20), &mut data).await.unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(data, [1, 2, 3, 4]);
                assert_eq!(handler.handle_complete(&mut []).await.unwrap(), 0);
                let TransactionExpectWrite::Read { handler, .. } =
                    i2c.listen_expect_write(Address::TenBit(0x20), &mut data).await.unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(data, [1, 2, 3, 4]);
                assert_eq!(handler.handle_complete(&[5, 6, 7, 8], 0xff).await.unwrap(), 4);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.start().await;
                tester.i2c_byte_checked(0xf1, false, 0xf1, true).await;
                tester.i2c_byte_checked(0xff, true, 5, true).await;
                tester.i2c_byte_checked(0xff, true, 6, true).await;
                tester.i2c_byte_checked(0xff, true, 7, true).await;
                tester.i2c_byte_checked(0xff, false, 8, false).await;
                tester.stop().await;
            }
        ),
        //
        // == DMA edge cases ==
        //

        // handle_part small sizes
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let WriteResult::Partial(handler) = handler.handle_part(&mut []).await.unwrap() else {
                    panic!("Unexpected write result");
                };
                let mut data1 = [0u8; 1];
                let WriteResult::Partial(handler) = handler.handle_part(&mut data1).await.unwrap() else {
                    panic!("Unexpected write result");
                };
                assert_eq!(data1, [1]);
                let mut data2 = [0u8; 2];
                let WriteResult::Partial(handler) = handler.handle_part(&mut data2).await.unwrap() else {
                    panic!("Unexpected write result");
                };
                assert_eq!(data2, [2, 3]);
                let WriteResult::Complete(1) = handler.handle_part(&mut data2).await.unwrap() else {
                    panic!("Unexpected write result");
                };
                assert_eq!(data2, [4, 3]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let ReadResult::Partial(handler) = handler.handle_part(&[]).await.unwrap() else {
                    panic!("Unexpected read result");
                };
                let ReadResult::Partial(handler) = handler.handle_part(&[1]).await.unwrap() else {
                    panic!("Unexpected read result");
                };
                let ReadResult::Partial(handler) = handler.handle_part(&[2, 3]).await.unwrap() else {
                    panic!("Unexpected read result");
                };
                let ReadResult::Complete(1) = handler.handle_part(&[4, 5]).await.unwrap() else {
                    panic!("Unexpected read result");
                };
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 2, true).await;
                tester.i2c_byte_checked(0xff, true, 3, true).await;
                tester.i2c_byte_checked(0xff, false, 4, false).await;
                tester.stop().await;
            }
        ),
        // handle part of size 0 doesn't ack address or last byte
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let WriteResult::Partial(handler) = handler.handle_part(&mut []).await.unwrap() else {
                    panic!("Unexpected write result");
                };
                drop(handler);

                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data1 = [0u8; 1];
                let WriteResult::Partial(handler) = handler.handle_part(&mut data1).await.unwrap() else {
                    panic!("Unexpected write result");
                };
                assert_eq!(data1, [1]);
                let WriteResult::Partial(handler) = handler.handle_part(&mut []).await.unwrap() else {
                    panic!("Unexpected write result");
                };
                drop(handler);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let ReadResult::Partial(handler) = handler.handle_part(&[]).await.unwrap() else {
                    panic!("Unexpected read result");
                };
                drop(handler);
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, false).await;
            }
        ),
        // handle_complete small sizes
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(handler.handle_complete(&mut []).await.unwrap(), 0);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data1 = [0u8; 1];
                assert_eq!(handler.handle_complete(&mut data1).await.unwrap(), 1);
                assert_eq!(data1, [1]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data2 = [0u8; 2];
                assert_eq!(handler.handle_complete(&mut data2).await.unwrap(), 2);
                assert_eq!(data2, [1, 2]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(handler.handle_complete(&[], 0xff).await.unwrap(), 4);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(handler.handle_complete(&[1], 0xff).await.unwrap(), 4);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(handler.handle_complete(&[1, 2], 0xff).await.unwrap(), 4);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, false).await;
                tester.i2c_byte_checked(2, false, 2, false).await;
                tester.i2c_byte_checked(3, false, 3, false).await;
                tester.i2c_byte_checked(4, false, 4, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, false).await;
                tester.i2c_byte_checked(3, false, 3, false).await;
                tester.i2c_byte_checked(4, false, 4, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, false).await;
                tester.i2c_byte_checked(4, false, 4, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 0xff, true).await;
                tester.i2c_byte_checked(0xff, true, 0xff, true).await;
                tester.i2c_byte_checked(0xff, true, 0xff, true).await;
                tester.i2c_byte_checked(0xff, false, 0xff, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 0xff, true).await;
                tester.i2c_byte_checked(0xff, true, 0xff, true).await;
                tester.i2c_byte_checked(0xff, false, 0xff, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 2, true).await;
                tester.i2c_byte_checked(0xff, true, 0xff, true).await;
                tester.i2c_byte_checked(0xff, false, 0xff, false).await;
                tester.stop().await;
            }
        ),
        // listen_expect small sizes
        (
            Address::SevenBit(0x20),
            {
                let TransactionExpectWrite::ExpectedPartialWrite { handler, .. } =
                    i2c.listen_expect_write(Address::SevenBit(0x20), &mut []).await.unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                drop(handler);

                let mut data1 = [0u8; 1];
                let TransactionExpectWrite::ExpectedPartialWrite { handler, .. } = i2c
                    .listen_expect_write(Address::SevenBit(0x20), &mut data1)
                    .await
                    .unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(data1, [1]);
                drop(handler);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let mut data2 = [0u8; 2];
                let TransactionExpectWrite::ExpectedPartialWrite { handler, .. } = i2c
                    .listen_expect_write(Address::SevenBit(0x20), &mut data2)
                    .await
                    .unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(data2, [1, 2]);
                drop(handler);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let TransactionExpectRead::ExpectedPartialRead { handler, .. } =
                    i2c.listen_expect_read(Address::SevenBit(0x20), &[]).await.unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                drop(handler);

                let TransactionExpectRead::ExpectedPartialRead { handler, .. } =
                    i2c.listen_expect_read(Address::SevenBit(0x20), &[1]).await.unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                drop(handler);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let TransactionExpectRead::ExpectedPartialRead { handler, .. } =
                    i2c.listen_expect_read(Address::SevenBit(0x20), &[1, 2]).await.unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                drop(handler);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, false).await;
                tester.i2c_byte_checked(0xff, true, 0xff, true).await;
                tester.i2c_byte_checked(0xff, true, 0xff, true).await;
                tester.i2c_byte_checked(0xff, true, 0xff, true).await;
                tester.i2c_byte_checked(0xff, false, 0xff, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 0xff, true).await;
                tester.i2c_byte_checked(0xff, true, 0xff, true).await;
                tester.i2c_byte_checked(0xff, false, 0xff, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 2, true).await;
                tester.i2c_byte_checked(0xff, true, 0xff, true).await;
                tester.i2c_byte_checked(0xff, false, 0xff, false).await;
                tester.stop().await;
            }
        ),
        //
        // == Byte count edge cases
        //

        // Handle part near boundaries
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                let WriteResult::Complete(3) = handler.handle_part(&mut data).await.unwrap() else {
                    panic!("Unexpected write result");
                };
                assert_eq!(data, [1, 2, 3, 0]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                let WriteResult::Partial(handler) = handler.handle_part(&mut data).await.unwrap() else {
                    panic!("Unexpected write result");
                };
                assert_eq!(data, [1, 2, 3, 4]);
                assert_eq!(handler.handle_complete(&mut []).await.unwrap(), 0);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                let WriteResult::Partial(handler) = handler.handle_part(&mut data).await.unwrap() else {
                    panic!("Unexpected write result");
                };
                assert_eq!(data, [1, 2, 3, 4]);
                assert_eq!(handler.handle_complete(&mut []).await.unwrap(), 0);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let ReadResult::Complete(3) = handler.handle_part(&[1, 2, 3, 4]).await.unwrap() else {
                    panic!("Unexpected read result.");
                };
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let ReadResult::Complete(4) = handler.handle_part(&[1, 2, 3, 4]).await.unwrap() else {
                    panic!("Unexpected read result.");
                };
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let ReadResult::Partial(handler) = handler.handle_part(&[1, 2, 3, 4]).await.unwrap() else {
                    panic!("Unexpected read result.");
                };
                assert_eq!(handler.handle_complete(&[], 0xff).await.unwrap(), 1);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.i2c_byte_checked(5, false, 5, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 2, true).await;
                tester.i2c_byte_checked(0xff, false, 3, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 2, true).await;
                tester.i2c_byte_checked(0xff, true, 3, true).await;
                tester.i2c_byte_checked(0xff, false, 4, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 2, true).await;
                tester.i2c_byte_checked(0xff, true, 3, true).await;
                tester.i2c_byte_checked(0xff, true, 4, true).await;
                tester.i2c_byte_checked(0xff, false, 0xff, false).await;
                tester.stop().await;
            }
        ),
        // handle complete near boundaries
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 3);
                assert_eq!(data, [1, 2, 3, 0]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [1, 2, 3, 4]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [1, 2, 3, 4]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(handler.handle_complete(&[1, 2, 3, 4], 0xff).await.unwrap(), 3);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(handler.handle_complete(&[1, 2, 3, 4], 0xff).await.unwrap(), 4);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(handler.handle_complete(&[1, 2, 3, 4], 0xff).await.unwrap(), 5);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.i2c_byte_checked(5, false, 5, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 2, true).await;
                tester.i2c_byte_checked(0xff, false, 3, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 2, true).await;
                tester.i2c_byte_checked(0xff, true, 3, true).await;
                tester.i2c_byte_checked(0xff, false, 4, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 2, true).await;
                tester.i2c_byte_checked(0xff, true, 3, true).await;
                tester.i2c_byte_checked(0xff, true, 4, true).await;
                tester.i2c_byte_checked(0xff, false, 0xff, false).await;
                tester.stop().await;
            }
        ),
        // listen_expect near boundaries
        (
            Address::SevenBit(0x20),
            {
                let mut data = [0u8; 4];
                let TransactionExpectWrite::ExpectedCompleteWrite { size: 3 } = i2c
                    .listen_expect_write(Address::SevenBit(0x20), &mut data)
                    .await
                    .unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(data, [1, 2, 3, 0]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let mut data = [0u8; 4];
                let TransactionExpectWrite::ExpectedPartialWrite { handler } = i2c
                    .listen_expect_write(Address::SevenBit(0x20), &mut data)
                    .await
                    .unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(data, [1, 2, 3, 4]);
                drop(handler);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let mut data = [0u8; 4];
                let TransactionExpectWrite::ExpectedPartialWrite { handler } = i2c
                    .listen_expect_write(Address::SevenBit(0x20), &mut data)
                    .await
                    .unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                assert_eq!(data, [1, 2, 3, 4]);
                drop(handler);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let TransactionExpectRead::ExpectedCompleteRead { size: 3 } = i2c
                    .listen_expect_read(Address::SevenBit(0x20), &[1, 2, 3, 4])
                    .await
                    .unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let TransactionExpectRead::ExpectedCompleteRead { size: 4 } = i2c
                    .listen_expect_read(Address::SevenBit(0x20), &[1, 2, 3, 4])
                    .await
                    .unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };

                let TransactionExpectRead::ExpectedPartialRead { handler } = i2c
                    .listen_expect_read(Address::SevenBit(0x20), &[1, 2, 3, 4])
                    .await
                    .unwrap()
                else {
                    panic!("Unexpected transaction");
                };
                drop(handler);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, true).await;
                tester.i2c_byte_checked(2, false, 2, true).await;
                tester.i2c_byte_checked(3, false, 3, true).await;
                tester.i2c_byte_checked(4, false, 4, false).await;
                tester.i2c_byte_checked(5, false, 5, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 2, true).await;
                tester.i2c_byte_checked(0xff, false, 3, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 2, true).await;
                tester.i2c_byte_checked(0xff, true, 3, true).await;
                tester.i2c_byte_checked(0xff, false, 4, false).await;
                tester.stop().await;

                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 2, true).await;
                tester.i2c_byte_checked(0xff, true, 3, true).await;
                tester.i2c_byte_checked(0xff, true, 4, true).await;
                tester.i2c_byte_checked(0xff, false, 0xff, false).await;
                tester.stop().await;
            }
        ),
        //
        // == Peripheral drop behaviour ==
        //

        // Dropping peripheral during write releases bus
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 1];
                let WriteResult::Partial(handler) = handler.handle_part(&mut data).await.unwrap() else {
                    panic!("Unexpected write handle_part result");
                };
                assert_eq!(data, [1]);
                core::mem::forget(handler);
                drop(i2c);
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x40, false, 0x40, true).await;
                tester.i2c_byte_checked(1, false, 1, false).await;
                tester.i2c_byte_checked(2, false, 2, false).await;
                tester.i2c_byte_checked(3, false, 3, false).await;
                tester.i2c_byte_checked(4, false, 4, false).await;
                tester.stop().await;
            }
        ),
        // Dropping peripheral during read releases bus
        (
            Address::SevenBit(0x20),
            {
                let Transaction::Read { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let ReadResult::Partial(handler) = handler.handle_part(&[1, 2]).await.unwrap() else {
                    panic!("Unexpected read handle_part result");
                };
                core::mem::forget(handler);
                drop(i2c);
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0x41, false, 0x41, true).await;
                tester.i2c_byte_checked(0xff, true, 1, true).await;
                tester.i2c_byte_checked(0xff, true, 2, true).await;
                tester.i2c_byte_checked(0xff, true, 0xff, true).await;
                tester.i2c_byte_checked(0xff, false, 0xff, false).await;
            }
        ),
        //
        // == Ten bit addressing overlaps ==
        //

        // 10 bit write to slave with partial overlapping address
        // An additional write of size 0 is done after to ensure listen finishes
        (
            Address::TenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let WriteResult::Complete(0) = handler.handle_part(&mut [0]).await.unwrap() else {
                    panic!("Unexpected handle_part result on write.");
                };
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x21, true, 0x21, true).await;
                tester.i2c_byte_checked(0xaa, true, 0xaa, true).await;
                tester.i2c_byte_checked(0x55, true, 0x55, true).await;
                tester.stop().await;
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.stop().await;
            }
        ),
        // 10 bit write to us, then restart and then ten bit write
        // to different slave with partial overlapping address, then restart and
        // ten bit write to us (should provide deselect event)
        (
            Address::TenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [4, 5, 6, 7]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [8, 9, 10, 11]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.i2c_byte_checked(5, false, 5, true).await;
                tester.i2c_byte_checked(6, false, 6, true).await;
                tester.i2c_byte_checked(7, false, 7, true).await;
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x21, true, 0x21, true).await;
                tester.i2c_byte_checked(2, true, 2, true).await;
                tester.i2c_byte_checked(3, true, 3, true).await;
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.i2c_byte_checked(8, false, 8, true).await;
                tester.i2c_byte_checked(9, false, 9, true).await;
                tester.i2c_byte_checked(10, false, 10, true).await;
                tester.i2c_byte_checked(11, false, 11, true).await;
                tester.stop().await;
            }
        ),
        // 10 bit write to us, then restart and then ten bit write to
        // different slave with partial overlapping address, then restart and
        // ten bit read (we should nack read)
        // An additional write of size 0 is done after to ensure listen finishes
        (
            Address::TenBit(0x20),
            {
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let mut data = [0u8; 4];
                assert_eq!(handler.handle_complete(&mut data).await.unwrap(), 4);
                assert_eq!(data, [4, 5, 6, 7]);
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let Transaction::Write { handler, .. } = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
                let WriteResult::Complete(0) = handler.handle_part(&mut [0]).await.unwrap() else {
                    panic!("Unexpected handle_part result on write.");
                };
                let Transaction::Deselect = i2c.listen().await.unwrap() else {
                    panic!("Unexpected transaction");
                };
            },
            {
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.i2c_byte_checked(4, false, 4, true).await;
                tester.i2c_byte_checked(5, false, 5, true).await;
                tester.i2c_byte_checked(6, false, 6, true).await;
                tester.i2c_byte_checked(7, false, 7, true).await;
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x21, true, 0x21, true).await;
                tester.i2c_byte_checked(2, true, 2, true).await;
                tester.i2c_byte_checked(3, true, 3, true).await;
                tester.start().await;
                tester.i2c_byte_checked(0xf1, false, 0xf1, false).await;
                tester.stop().await;
                tester.start().await;
                tester.i2c_byte_checked(0xf0, false, 0xf0, true).await;
                tester.i2c_byte_checked(0x20, false, 0x20, true).await;
                tester.stop().await;
            }
        ),
    ]
);

async fn test_sync_master() {
    MASTER_READY.release(1);
    SLAVE_READY.acquire(1).await.unwrap().disarm();
}

async fn test_sync_slave() {
    SLAVE_READY.release(1);
    MASTER_READY.acquire(1).await.unwrap().disarm();
}

static MASTER_READY: Semaphore = Semaphore::new(0);
static SLAVE_READY: Semaphore = Semaphore::new(0);

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    info!("i2c loopback example");
    let p = embassy_imxrt::init(Default::default());

    let (slave_flexcomm, slave_scl, slave_sda, slave_dma) = (p.FLEXCOMM2, p.PIO0_18, p.PIO0_17, p.DMA0_CH4);

    let (master_scl, master_sda) = (p.PIO0_29, p.PIO0_30);

    spawner.must_spawn(slave_under_test(slave_flexcomm, slave_scl, slave_sda, slave_dma));
    spawner.must_spawn(tester(master_scl, master_sda));
}
