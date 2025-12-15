#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::rng::Rng;
use embassy_imxrt::{bind_interrupts, peripherals, rng};
use rand::TryRngCore;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

bind_interrupts!(struct Irqs {
    RNG => rng::InterruptHandler<peripherals::RNG>;
});

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("Initializing RNG");
    let mut rng = Rng::new(p.RNG, Irqs);
    let mut buf = [0u8; 65];

    let mut count = 0;

    // Async interface
    while rng.async_fill_bytes(&mut buf).await.is_err() {
        count += 1;
    }
    info!("random bytes: {:02x} (succeeded after {} retries)", buf, count);

    // RngCore interface
    let mut random_bytes = [0; 16];

    count = 0;
    let random_u32 = loop {
        match rng.try_next_u32() {
            Ok(r) => break r,
            Err(_) => {
                count += 1;
            }
        }
    };

    info!("random_u32 {} (succeeded after {} retries)", random_u32, count);

    count = 0;
    let random_u64 = loop {
        match rng.try_next_u64() {
            Ok(r) => break r,
            Err(_) => {
                count += 1;
            }
        }
    };

    info!("random_u64 {} (succeeded after {} retries)", random_u64, count);

    count = 0;
    while rng.try_fill_bytes(&mut random_bytes).is_err() {
        count += 1;
    }

    info!("random_bytes {} (succeeded after {} retries)", random_u64, count);
}
