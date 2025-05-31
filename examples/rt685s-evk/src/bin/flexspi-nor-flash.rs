#![no_std]
#![no_main]

use embassy_imxrt::flexspi::nor_flash::{FlashAlignment, FlexSpiNorFlash};
use {defmt_rtt as _, panic_probe as _};

const FCB_ADDRESS: u32 = 0x0000_0400;
const FCB_SIZE: usize = 512;

#[embassy_executor::main]
async fn main(_spawner: embassy_executor::Spawner) {
    let p = embassy_imxrt::init(Default::default());

    // NOTE: Make sure to adjust the alignment for the actual flash chip you are using.
    let alignment = FlashAlignment {
        read_alignment: 2,
        write_alignment: 2,
        sector_size: 4096,
        block_size: 64 * 1024,
        page_size: 256,
    };

    // Create a new FlexSPI NOR flash driver.
    // NOTE: This relies of the FlexSPI having been configured already by having a valid FCB in the flash memory.
    let mut flash = unsafe { FlexSpiNorFlash::new_unchecked(p.FLEXSPI, alignment) };

    // Read the FCB.
    let mut fcb = [0; FCB_SIZE];
    match flash.read(FCB_ADDRESS, &mut fcb) {
        Ok(()) => defmt::info!("FCB: {:02X}", fcb),
        Err(e) => defmt::error!("Failed to read FCB from flash: {}", e),
    }
}
