#![no_std]
#![no_main]

use defmt::{error, info};
use embassy_executor::Spawner;
use embassy_imxrt::Peri;
use embassy_imxrt::dma::Dma;
use embassy_imxrt::dma::transfer::{Priority, Transfer, TransferOptions, Width};
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

const TEST_LEN: usize = 16;

async fn dma_test<DMA: embassy_imxrt::dma::Instance>(peripheral: Peri<'_, DMA>, number: usize) {
    let ch = Dma::reserve_channel(peripheral).unwrap();
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

    dma_test(p.DMA0_CH0, 0).await;
    dma_test(p.DMA0_CH1, 1).await;
    dma_test(p.DMA0_CH2, 2).await;
    dma_test(p.DMA0_CH3, 3).await;
    dma_test(p.DMA0_CH4, 4).await;
    dma_test(p.DMA0_CH5, 5).await;
    dma_test(p.DMA0_CH6, 6).await;
    dma_test(p.DMA0_CH7, 7).await;
    dma_test(p.DMA0_CH8, 8).await;
    dma_test(p.DMA0_CH9, 9).await;
    dma_test(p.DMA0_CH10, 10).await;
    dma_test(p.DMA0_CH11, 11).await;
    dma_test(p.DMA0_CH12, 12).await;
    dma_test(p.DMA0_CH13, 13).await;
    dma_test(p.DMA0_CH14, 14).await;
    dma_test(p.DMA0_CH15, 15).await;
    dma_test(p.DMA0_CH16, 16).await;
    dma_test(p.DMA0_CH17, 17).await;
    dma_test(p.DMA0_CH18, 18).await;
    dma_test(p.DMA0_CH19, 19).await;
    dma_test(p.DMA0_CH20, 20).await;
    dma_test(p.DMA0_CH21, 21).await;
    dma_test(p.DMA0_CH22, 22).await;
    dma_test(p.DMA0_CH23, 23).await;
    dma_test(p.DMA0_CH24, 24).await;
    dma_test(p.DMA0_CH25, 25).await;
    dma_test(p.DMA0_CH26, 26).await;
    dma_test(p.DMA0_CH27, 27).await;
    dma_test(p.DMA0_CH28, 28).await;
    dma_test(p.DMA0_CH29, 29).await;
    dma_test(p.DMA0_CH30, 30).await;
    dma_test(p.DMA0_CH31, 31).await;

    info!("DMA transfer tests completed");
}
