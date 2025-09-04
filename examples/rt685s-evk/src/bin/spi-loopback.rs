#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::spi::Spi;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("Initializing SPI");

    let mut spi = Spi::new_blocking_loopback(p.FLEXCOMM5, Default::default());

    let mut rxbuf = [0; 256];
    let txbuf = [0xaa; 256];

    loop {
        spi.blocking_transfer(&mut rxbuf, &txbuf).unwrap();
    }
}
