#![no_std]
#![no_main]

use defmt::{error, info};
use embassy_executor::Spawner;
use embassy_imxrt::flexspi::nor_flash::FlexSpiNorFlash;
use embassy_imxrt::gpio;
use embassy_time::Timer;
use {defmt_rtt as _, panic_probe as _, rt633_examples as _};

/* This example demonstrates usage of the FlexSPI NOR flash driver to read, erase, and program.
  This is for the lower level flash operations that is not safe. Application should use the
  embedded-storage traits wrapper instead.
*/
#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let mut p = embassy_imxrt::init(Default::default());

    info!("Hello world");

    let mut led = gpio::Output::new(
        p.PIO1_5,
        gpio::Level::Low,
        gpio::DriveMode::PushPull,
        gpio::DriveStrength::Normal,
        gpio::SlewRate::Standard,
    );

    let button = gpio::Input::new(p.PIO1_2, gpio::Pull::Down, gpio::Inverter::Disabled);

    // Create a new FlexSPI NOR flash driver.
    // NOTE: This relies on the FlexSPI having been configured already by having a valid FCB in the flash memory.
    // SAFETY: The FCB for example rt633 is completedly valid.
    let mut flash = unsafe { FlexSpiNorFlash::with_probed_config(p.FLEXSPI.reborrow(), 2, 2) }
        .map_err(|e| error!("Failed to initialize FlexSPI peripheral: {}", e))
        .unwrap();

    // Read last sector.
    let mut last_sector = [0; 16];
    let last_sector_addr = 0x1F_F000;
    flash
        .read(last_sector_addr, &mut last_sector)
        .map_err(|e| error!("Failed to read last sector from flash: {}", e))
        .unwrap();
    info!("Last sector[0..16] (pre-erase): {}", last_sector[0..16]);

    // SAFETY: Last sector of the flash is excluded from the memory map so it's safe to erase/program it.
    unsafe { flash.erase_sector(last_sector_addr) }
        .map_err(|e| error!("Failed to erase last sector from flash: {}", e))
        .unwrap();

    flash
        .read(last_sector_addr, &mut last_sector)
        .map_err(|e| error!("Failed to read last sector from flash: {}", e))
        .unwrap();
    info!("Last sector[0..16] (post-erase): {}", last_sector);

    // Program last sector.
    info!("Programming first chunk of last sector");
    // SAFETY: Last sector of the flash is excluded from the memory map so it's safe to erase/program it.
    unsafe {
        flash.page_program(
            last_sector_addr,
            &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
        )
    }
    .map_err(|e| error!("Failed to program first chunk of last sector: {}", e))
    .unwrap();
    info!("Programmed first chunk of last sector");

    flash
        .read(last_sector_addr, &mut last_sector)
        .map_err(|e| error!("Failed to read last sector from flash: {}", e))
        .unwrap();
    info!("Last sector[0..16] (post-program): {}", last_sector);

    loop {
        info!("Toggling LED");
        led.toggle();
        Timer::after_millis(1000).await;

        if button.is_low() {
            info!("Button pressed");
        } else {
            info!("Button not pressed");
        }
    }
}
