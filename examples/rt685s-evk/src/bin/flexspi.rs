#![no_std]
#![no_main]

use core::arch::asm;

use defmt::*;
use embassy_executor::Spawner;
use embassy_imxrt::flexspi::{FlexSpiBusWidth, FlexSpiFlashPort, FlexSpiFlashPortDeviceInstance, FlexspiStorage};
use embassy_time::Timer;
use embedded_storage::nor_flash::{NorFlash as BlockingNorFlash, ReadNorFlash as BlockingReadNorFlash};
use {defmt_rtt as _, panic_probe as _};

static ADDR: u32 = 0x2F000;

fn copy_flexspi_ramcode_to_ram() {
    unsafe {
        let mut flash_code_start = 0;
        let mut flash_code_end = 0;
        let mut ram_code_start = 0;
        asm!("ldr {}, =__flexspi_flash_start_addr__", out(reg) flash_code_start);
        asm!("ldr {}, =__flexspi_flash_end_addr__", out(reg) flash_code_end);
        asm!("ldr {}, =__flexspi_ram_start_addr__", out(reg) ram_code_start);
        info!(
            "code flash addr start = {:08X} end = {:08X}",
            flash_code_start, flash_code_end
        );
        info!("ram addr start = {:08X}", ram_code_start);
        let mut flash_code_start_ptr = flash_code_start as *const u8;
        let flash_code_end_ptr = flash_code_end as *const u8;
        let mut ram_code_start_ptr = ram_code_start as *mut u8;
        loop {
            if flash_code_start_ptr >= flash_code_end_ptr {
                break;
            }
            *ram_code_start_ptr = *flash_code_start_ptr;
            ram_code_start_ptr = ram_code_start_ptr.add(1);
            flash_code_start_ptr = flash_code_start_ptr.add(1);
        }
    }
}

#[embassy_executor::main]
#[no_mangle]
async fn main(_spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    let mut read_data = [0; 32];
    let mut write_data = [0; 32];

    let mut flexspi = FlexspiStorage::new_blocking_xip(
        p.FLEXSPI,                                       // FlexSPI peripheral
        FlexSpiFlashPort::PortB,                         // FlexSPI port
        FlexSpiFlashPortDeviceInstance::DeviceInstance0, // FlexSPI device instance
    );

    // Copy the Ram code to .flexspi_code partition
    copy_flexspi_ramcode_to_ram();

    unsafe { asm!("cpsid i") }

    cortex_m::asm::dsb();

    flexspi.write_enable();
    let status = flexspi.read_status_register();
    info!("Status = {:02X} after write enable", status[0]);

    flexspi.erase_sector(ADDR);

    let status = flexspi.read_status_register();
    info!("Status = {:02X} after erase", status[0]);

    for i in 0..5 {
        flexspi.read(ADDR + i as u32, &mut read_data);
        info!("Read data = {:02X} after erase", read_data[0]);
    }

    flexspi.write_enable();

    for i in 0..32 {
        let mut temp_array = [0_u8; 1];
        temp_array[0] += i;
        write_data[i as usize] = temp_array[0] as u8;
        flexspi.write(ADDR + i as u32, &temp_array);
        flexspi.wait_for_operation_completion();
        flexspi.write_enable();
    }

    for i in 0..32 {
        let mut temp_array: [u8; 1] = [0; 1];
        flexspi.read(ADDR + i as u32, &mut temp_array);
        read_data[i] = temp_array[0];
    }

    for i in 0..32 {
        if read_data[i] != write_data[i] {
            crate::panic!("Data mismatch idx = {} addr = {}", i, ADDR + i as u32);
        }
    }
    info!("Data matched");

    cortex_m::asm::dsb();

    unsafe { asm!("cpsie i") }

    loop {
        Timer::after_millis(2000).await;
    }
}
