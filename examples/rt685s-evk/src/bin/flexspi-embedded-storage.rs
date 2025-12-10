#![no_std]
#![no_main]

use embassy_imxrt::flexspi::nor_flash::FlexSpiNorFlash;
use embassy_imxrt::gpio;
use embedded_storage::nor_flash::{NorFlash, ReadNorFlash};
use futures::FutureExt as _;
use {defmt_rtt as _, panic_probe as _};

#[embassy_executor::main]
async fn main(_spawner: embassy_executor::Spawner) {
    let mut p = embassy_imxrt::init(Default::default());

    let mut led = match do_main(&mut p).await {
        Ok(()) => gpio::Output::new(
            p.PIO0_14, // Green LED.
            gpio::Level::Low,
            gpio::DriveMode::PushPull,
            gpio::DriveStrength::Normal,
            gpio::SlewRate::Standard,
        ),
        Err(()) => gpio::Output::new(
            p.PIO0_31, // Red LED.
            gpio::Level::Low,
            gpio::DriveMode::PushPull,
            gpio::DriveStrength::Normal,
            gpio::SlewRate::Standard,
        ),
    };

    // Blink green LED if do_main() reported success, red LED otherwise.
    blink(&mut led, 100, 100).await
}

async fn do_main(p: &mut embassy_imxrt::Peripherals) -> Result<(), ()> {
    defmt::info!("Application started");

    let mut blue = gpio::Output::new(
        p.PIO0_26.reborrow(),
        gpio::Level::Low,
        gpio::DriveMode::PushPull,
        gpio::DriveStrength::Normal,
        gpio::SlewRate::Standard,
    );

    let mut button1 = gpio::Input::new(p.PIO1_1.reborrow(), gpio::Pull::None, gpio::Inverter::Disabled);
    let mut button2 = gpio::Input::new(p.PIO0_10.reborrow(), gpio::Pull::None, gpio::Inverter::Disabled);

    // Create a new FlexSPI NOR flash driver.
    // NOTE: This relies on the FlexSPI having been configured already by having a valid FCB in the flash memory.
    let flash = unsafe { FlexSpiNorFlash::with_probed_config(p.FLEXSPI.reborrow(), 2, 2) }
        .map_err(|e| defmt::error!("Failed to initialize FlexSPI peripheral: {}", e))?;
    let mut flash = unsafe { embassy_imxrt::flexspi::embedded_storage::FlexSpiNorStorage::<2, 2, 4096>::new(flash) }
        .map_err(|e| defmt::error!("Failed to wrap FlexSPI flash in embedded_storage adaptor: {}", e))?;

    // Read last sector.
    let mut last_sector = [0; 16];
    let last_sector_addr = 0x3FFF000;
    flash
        .read(last_sector_addr, &mut last_sector)
        .map_err(|e| defmt::error!("Failed to read last sector from flash: {}", e))?;
    blue.toggle();
    defmt::info!("Last sector[0..16] (pre-erase): {}", last_sector[0..16]);

    // Wait for buttons before erasing.
    defmt::info!(
        "Press button User_1 to erase and program last sector (0x{:08X}) of flash",
        last_sector_addr
    );
    blink_until_button(&mut button1, &mut blue, 100, 900).await;
    defmt::info!(
        "Button User_1 pressed. Now press and release button User_2 to continue erasing and programming last sector (0x{:08X}) of flash",
        last_sector_addr
    );
    blink_until_button(&mut button2, &mut blue, 100, 200).await;
    defmt::info!(
        "Button User_2 pressed. Erasing and programming last sector (0x{:08X}) of flash",
        last_sector_addr
    );

    // Erase last sector
    defmt::info!("Erasing last sector");
    flash
        .erase(last_sector_addr, last_sector_addr + 4096)
        .map_err(|e| defmt::error!("Failed to erase last sector from flash: {}", e))?;

    // // Read last sector again.
    flash
        .read(last_sector_addr, &mut last_sector)
        .map_err(|e| defmt::error!("Failed to read last sector from flash: {}", e))?;
    defmt::info!("Last sector[0..16] (post-erase): {}", last_sector);

    // Program last sector.
    defmt::info!("Programming first chunk of last sector");
    flash
        .write(
            last_sector_addr,
            &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
        )
        .map_err(|e| defmt::error!("Failed to program first chunk of last sector: {}", e))?;
    defmt::info!("Programmed first chunk of last sector");

    // Read last sector again.
    flash
        .read(last_sector_addr, &mut last_sector)
        .map_err(|e| defmt::error!("Failed to read last sector from flash: {}", e))?;
    defmt::info!("Last sector[0..16] (post-program): {}", last_sector);

    Ok(())
}

// Blink an LED with the given on/off time in milliseconds.
async fn blink(led: &mut gpio::Output<'_>, on_ms: u32, off_ms: u32) -> ! {
    let mut ticker = embassy_time::Ticker::every(embassy_time::Duration::from_millis(
        u64::from(on_ms) + u64::from(off_ms),
    ));
    loop {
        led.set_high();
        embassy_time::Timer::after_millis(on_ms.into()).await;
        led.set_low();
        ticker.next().await;
    }
}

// Blink an LED with given on/off time in milliseconds, until a button is pressed and released.
async fn blink_until_button(button: &mut gpio::Input<'_>, led: &mut gpio::Output<'_>, on_ms: u32, off_ms: u32) {
    futures::select_biased! {
        _ = blink(led, on_ms, off_ms).fuse() => (),
        _ = button.wait_for_falling_edge().fuse() => (),
    }
}
