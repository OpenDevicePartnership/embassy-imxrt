#![no_std]
#![no_main]

use embassy_imxrt_examples as _;

use defmt::*;
use embassy_executor::Spawner;
use embassy_imxrt::dma::channel::Channel;
use embassy_imxrt::dma::transfer::{Priority, Transfer, TransferOptions, Width};
use embassy_imxrt::dma::Dma;
use embassy_imxrt::peripherals::*;
use {defmt_rtt as _, panic_probe as _};

const TEST_LEN: usize = 16;

macro_rules! test_dma_channel {
    ($peripherals:expr, $instance:ident, $number:expr) => {
        let ch = Dma::reserve_channel::<$instance>($peripherals.$instance).unwrap();
        dma_test(ch, $number).await;
    };
}

async fn dma_test(ch: Channel<'static>, number: usize) {
    for width in [Width::Bit8, Width::Bit16, Width::Bit32] {
        let mut srcbuf: [u8; TEST_LEN] = [0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let mut dstbuf = [0u8; TEST_LEN];
        srcbuf[0] = number as u8;

        let mut options = TransferOptions::default();
        options.width = width;
        options.priority = Priority::Priority0;

        Transfer::new_write_mem(&ch, &srcbuf, &mut dstbuf, options).await;

        if srcbuf == dstbuf {
            info!(
                "DMA transfer width: {}, on channel {} completed successfully: {:02x}",
                width.byte_width(),
                number,
                dstbuf.iter().as_slice()
            );
        } else {
            error!(
                "DMA transfer width: {}, on channel {} failed!",
                width.byte_width(),
                number
            );
        }
    }
}

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("Test memory-to-memory DMA transfers");

    test_dma_channel!(p, DMA0_CH0, 0);
    test_dma_channel!(p, DMA0_CH1, 1);
    test_dma_channel!(p, DMA0_CH2, 2);
    test_dma_channel!(p, DMA0_CH3, 3);
    test_dma_channel!(p, DMA0_CH4, 4);
    test_dma_channel!(p, DMA0_CH5, 5);
    test_dma_channel!(p, DMA0_CH6, 6);
    test_dma_channel!(p, DMA0_CH7, 7);
    test_dma_channel!(p, DMA0_CH8, 8);
    test_dma_channel!(p, DMA0_CH9, 9);
    test_dma_channel!(p, DMA0_CH10, 10);
    test_dma_channel!(p, DMA0_CH11, 11);
    test_dma_channel!(p, DMA0_CH12, 12);
    test_dma_channel!(p, DMA0_CH13, 13);
    test_dma_channel!(p, DMA0_CH14, 14);
    test_dma_channel!(p, DMA0_CH15, 15);
    test_dma_channel!(p, DMA0_CH16, 16);
    test_dma_channel!(p, DMA0_CH17, 17);
    test_dma_channel!(p, DMA0_CH18, 18);
    test_dma_channel!(p, DMA0_CH19, 19);
    test_dma_channel!(p, DMA0_CH20, 20);
    test_dma_channel!(p, DMA0_CH21, 21);
    test_dma_channel!(p, DMA0_CH22, 22);
    test_dma_channel!(p, DMA0_CH23, 23);
    test_dma_channel!(p, DMA0_CH24, 24);
    test_dma_channel!(p, DMA0_CH25, 25);
    test_dma_channel!(p, DMA0_CH26, 26);
    test_dma_channel!(p, DMA0_CH27, 27);
    test_dma_channel!(p, DMA0_CH28, 28);
    test_dma_channel!(p, DMA0_CH29, 29);
    test_dma_channel!(p, DMA0_CH30, 30);
    test_dma_channel!(p, DMA0_CH31, 31);

    info!("DMA transfer tests completed");
}
