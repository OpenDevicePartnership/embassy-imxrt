//! This example shows how to use SPI (Serial Peripheral Interface) in the RT632.
//!
//!

#![no_std]
#![no_main]

extern crate embassy_imxrt_examples;

use core::option::Option;
use defmt::{error, info};
use embassy_executor::Spawner;
use embassy_imxrt::spi::{self, SpiController};
use embedded_hal_1::spi::SpiBus;
use {defmt_rtt as _, panic_probe as _};

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());
    info!("Hello Spi Demo!");

    // configure gpio pins
    board_init_pin_clocks();

    use embassy_imxrt::gpio::*;

    // create SPI
    let mut configb = spi::Config::default();
    configb.frequency = 2_000_000;
    // new_blocking(fc, config, sclk, miso, mosi, ssel0)
    //let mut spi = SpiController::new_blocking(p.FLEXCOMM14, configb, p.PIO1_11, p.PIO1_12, p.PIO1_13, Some(p.PIO1_14)).unwrap();
    let mut spi =
        SpiController::new_blocking(p.FLEXCOMM5, configb, p.PIO1_3, p.PIO1_4, p.PIO1_5, Some(p.PIO1_6)).unwrap();

    let mut rdata: [u8; 10] = [0; 10];
    let wrdata: [u8; 10] = [0x12, 0x34, 0x56, 0x78, 0x89, 0xAB, 0xCD, 0xEF, 0xFE, 0xDC];
    let _ = spi.transfer(&mut rdata, &wrdata);

    info!("Blocking transfer done");

    let len = rdata.len();
    for i in 0..len {
        info!("iter {} rd {:#02X}", i, rdata[i]);
    }

    /*
        let mut configa = spi::Config::default();
        configa.frequency = 2_000_000;
        // new_async(fc, config, sclk, miso, mosi, ssel0, ssel1, ssel2, ssel3, dma rx, dma tx)
        let mut _spi = SpiController::new_async(
            p.FLEXCOMM4,
            configa,
            p.PIO0_7,
            p.PIO0_8,
            p.PIO0_9,
            Some(p.PIO0_10),
            Some(p.PIO0_11),
            Some(p.PIO0_12),
            Some(p.PIO0_13),
            p.DMA0_CH2,
            p.DMA0_CH3,
        )
        .await
        .unwrap();

    */
}

fn board_init_pin_clocks() {}
