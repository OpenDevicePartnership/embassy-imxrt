#![no_std]
#![no_main]

use embassy_executor::Spawner;
use embassy_imxrt::dma::transfer::TransferOptions;
use embassy_imxrt::interrupt::Interrupt;
use nonsecure_app::SECURE_MEMORY;
use panic_probe as _;
use rtt_target::rprintln;

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let (p, mut cp) = nonsecure_app::init();

    // Make DMA0 lower priority than SECUREVIOLATION.
    unsafe {
        cp.NVIC.set_priority(Interrupt::DMA0, 32);
    }

    let channel = embassy_imxrt::dma::Dma::reserve_channel(p.DMA0_CH0).unwrap();

    let buf = 0x1337u32;

    rprintln!("Trying to get DMA access to secure memory (should fail with SECUREVIOLATION (ns)!)");
    let mut options = TransferOptions::default();
    options.width = embassy_imxrt::dma::transfer::Width::Bit32;
    options.priority = embassy_imxrt::dma::transfer::Priority::Priority0;

    embassy_imxrt::dma::transfer::Transfer::new_raw_transfer(
        &channel,
        embassy_imxrt::dma::transfer::Direction::MemoryToMemory,
        &buf,
        SECURE_MEMORY,
        core::mem::size_of_val(&buf),
        options,
    )
    .await;

    rprintln!("!!! SHOULD NOT BE REACHABLE !!!");
}
