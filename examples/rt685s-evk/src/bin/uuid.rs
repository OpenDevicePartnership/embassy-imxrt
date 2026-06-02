#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::uuid::Uuid;
use embassy_time::Timer;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let _p = embassy_imxrt::init(Default::default());

    info!("UUID: {:016x}", Uuid::read().to_u128());
    info!("UUID: {:02x}", Uuid::read().to_ne_bytes());
    info!("UUID: {:02x}", Uuid::read().to_be_bytes());
    info!("UUID: {:02x}", Uuid::read().to_le_bytes());

    loop {
        Timer::after_millis(1000).await;
    }
}
