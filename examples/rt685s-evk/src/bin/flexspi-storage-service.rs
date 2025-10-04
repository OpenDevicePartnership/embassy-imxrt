#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::flexspi::nor_storage_bus::{
    AhbConfig, FlexSpiFlashPort, FlexSpiFlashPortDeviceInstance, FlexspiAhbBufferConfig, FlexspiConfig,
    FlexspiConfigPortData, FlexspiDeviceConfig, FlexspiNorStorageBus,
};
use embassy_imxrt::pac::flexspi::ahbcr::{Bufferableen, Cachableen, Readaddropt};
use embassy_imxrt::pac::flexspi::flshcr1::Csintervalunit;
use embassy_imxrt::pac::flexspi::flshcr2::Awrwaitunit;
use embassy_imxrt::pac::flexspi::flshcr4::{Wmena, Wmenb};
use embassy_imxrt::pac::flexspi::mcr0::{Dozeen, Hsen, Rxclksrc, Sckfreerunen};
use embassy_imxrt::pac::flexspi::mcr2::{Clrahbbufopt, Samedeviceen, Sckbdiffopt};
use embassy_time::Timer;
use embedded_storage::nor_flash::{
    ErrorType, NorFlash as BlockingNorFlash, NorFlashError, NorFlashErrorKind, ReadNorFlash as BlockingReadNorFlash,
};
use storage_bus::nor::{
    BlockingNorStorageBusDriver, NorStorageBusWidth, NorStorageCmd, NorStorageCmdMode, NorStorageCmdType,
    NorStorageDummyCycles,
};
use {defmt_rtt as _, panic_probe as _};

static ADDR: u32 = 0x3FD0000;

mod sealed {
    /// simply seal a trait
    pub trait Sealed {}
}

impl sealed::Sealed for Blocking {}
impl sealed::Sealed for Async {}

/// Driver mode.
#[allow(private_bounds)]
pub trait Mode: sealed::Sealed {}

/// Blocking mode.
pub struct Blocking;
impl Mode for Blocking {}

/// Async mode.
pub struct Async;
impl Mode for Async {}

struct MacronixDeviceDriver<T: BlockingNorStorageBusDriver, M: Mode> {
    // Bus driver dependency
    storagebusdriver: T,
    capacity: usize,
    _phantom: core::marker::PhantomData<M>,
}
#[derive(Debug)]
pub enum NorErrorType {
    /// Nor flash error object for other errors
    FlashStorageErrorOther,

    /// Error object for overflow errror
    FlashStorageErrorOutOfBounds,

    /// Error object for alignment error
    FlashStorageErrorNotAligned,
}

impl<T: BlockingNorStorageBusDriver, M: Mode> ErrorType for MacronixDeviceDriver<T, M> {
    type Error = NorErrorType;
}

impl NorFlashError for NorErrorType {
    fn kind(&self) -> NorFlashErrorKind {
        match self {
            NorErrorType::FlashStorageErrorOther => NorFlashErrorKind::Other,
            NorErrorType::FlashStorageErrorOutOfBounds => NorFlashErrorKind::OutOfBounds,
            NorErrorType::FlashStorageErrorNotAligned => NorFlashErrorKind::NotAligned,
        }
    }
}

impl<T: BlockingNorStorageBusDriver> MacronixDeviceDriver<T, Blocking> {
    pub fn get_jedec_id(&mut self, jedec: &mut [u8]) {
        let read_cread_jedec_id_cmd = NorStorageCmd {
            cmd_lb: 0x9F,
            cmd_ub: Some(0x60),
            addr: Some(0x0),
            addr_width: Some(32),
            bus_width: NorStorageBusWidth::Octal, // 3 - Octal
            mode: NorStorageCmdMode::DDR,
            dummy: NorStorageDummyCycles::Clocks(0x18),
            cmdtype: Some(NorStorageCmdType::Read),
            data_bytes: Some(4),
        };

        let _ = self
            .storagebusdriver
            .send_command(read_cread_jedec_id_cmd, Some(jedec), None);
    }
}

impl<T: BlockingNorStorageBusDriver> BlockingReadNorFlash for MacronixDeviceDriver<T, Blocking> {
    const READ_SIZE: usize = 1;

    fn read(&mut self, offset: u32, bytes: &mut [u8]) -> Result<(), Self::Error> {
        #[allow(const_evaluatable_unchecked)]
        let mut read_start_ptr = 0;

        if offset > self.capacity as u32 {
            return Err(NorErrorType::FlashStorageErrorOutOfBounds);
        }
        if offset + bytes.len() as u32 > self.capacity as u32 {
            return Err(NorErrorType::FlashStorageErrorOutOfBounds);
        }

        while read_start_ptr < bytes.len() {
            // Read data from the storage device
            let read_cmd = NorStorageCmd {
                cmd_lb: 0xEE,
                cmd_ub: Some(0x11),
                addr: Some(offset + read_start_ptr as u32),
                addr_width: Some(0x20),
                bus_width: NorStorageBusWidth::Octal,
                mode: NorStorageCmdMode::DDR,
                dummy: NorStorageDummyCycles::Clocks(0x29),
                cmdtype: Some(NorStorageCmdType::Read),
                data_bytes: Some(Self::READ_SIZE as u32),
            };

            let _ = self.storagebusdriver.send_command(
                read_cmd,
                Some(&mut bytes[read_start_ptr..read_start_ptr + Self::READ_SIZE]),
                None,
            );

            read_start_ptr += Self::READ_SIZE;
        }

        Ok(())
    }

    fn capacity(&self) -> usize {
        self.capacity
    }
}

impl<T: BlockingNorStorageBusDriver> BlockingNorFlash for MacronixDeviceDriver<T, Blocking> {
    const WRITE_SIZE: usize = 1;
    const ERASE_SIZE: usize = 4096;

    fn erase(&mut self, from: u32, to: u32) -> Result<(), Self::Error> {
        // subtracting 1 as align will give next sector start address
        let mut sector_start_addr = from;
        let sector_end_addr = to;
        let mut status = [0_u8; 4];

        info!("Erase data");

        if from > to {
            return Err(NorErrorType::FlashStorageErrorOther);
        }

        if from > self.capacity as u32 {
            return Err(NorErrorType::FlashStorageErrorOutOfBounds);
        }

        if to > self.capacity as u32 {
            return Err(NorErrorType::FlashStorageErrorOutOfBounds);
        }

        if !from.is_multiple_of(Self::ERASE_SIZE as u32) {
            return Err(NorErrorType::FlashStorageErrorNotAligned);
        }

        if !to.is_multiple_of(Self::ERASE_SIZE as u32) {
            return Err(NorErrorType::FlashStorageErrorNotAligned);
        }

        // Enable Write
        let write_enable_cmd = NorStorageCmd {
            cmd_lb: 0x06,
            cmd_ub: Some(0xF9),
            addr: None,
            addr_width: None,
            bus_width: NorStorageBusWidth::Octal,
            mode: NorStorageCmdMode::DDR,
            dummy: NorStorageDummyCycles::Clocks(0),
            cmdtype: None,
            data_bytes: None,
        };
        let _ = self.storagebusdriver.send_command(write_enable_cmd, None, None);

        // Check write enable status
        let read_status_cmd = NorStorageCmd {
            cmd_lb: 0x05,
            cmd_ub: Some(0xFA),
            addr: Some(0),
            addr_width: Some(0x20),
            bus_width: NorStorageBusWidth::Octal,
            mode: NorStorageCmdMode::DDR,
            dummy: NorStorageDummyCycles::Clocks(0x14),
            cmdtype: Some(NorStorageCmdType::Read),
            data_bytes: Some(0x4),
        };
        let _ = self
            .storagebusdriver
            .send_command(read_status_cmd, Some(&mut status), None);

        loop {
            if sector_start_addr > sector_end_addr {
                break;
            }
            let _ = self.storagebusdriver.send_command(
                NorStorageCmd {
                    cmd_lb: 0x21,
                    cmd_ub: Some(0xDE),
                    addr: Some(sector_start_addr),
                    addr_width: Some(0x20),
                    bus_width: NorStorageBusWidth::Octal,
                    mode: NorStorageCmdMode::DDR,
                    dummy: NorStorageDummyCycles::Clocks(0),
                    cmdtype: None,
                    data_bytes: None,
                },
                None,
                None,
            );
            loop {
                // Check Erase status
                let read_status_cmd = NorStorageCmd {
                    cmd_lb: 0x05,
                    cmd_ub: Some(0xFA),
                    addr: Some(0),
                    addr_width: Some(0x20),
                    bus_width: NorStorageBusWidth::Octal,
                    mode: NorStorageCmdMode::DDR,
                    dummy: NorStorageDummyCycles::Clocks(0x14),
                    cmdtype: Some(NorStorageCmdType::Read),
                    data_bytes: Some(0x4),
                };
                let _ = self
                    .storagebusdriver
                    .send_command(read_status_cmd, Some(&mut status), None);

                if status[0] & 0x01 == 0 {
                    break;
                }
            }
            sector_start_addr += Self::ERASE_SIZE as u32;
        }

        Ok(())
    }

    fn write(&mut self, offset: u32, bytes: &[u8]) -> Result<(), Self::Error> {
        let bus_ref = &mut self.storagebusdriver;
        let mut status = [0_u8; 3];

        if offset > self.capacity as u32 {
            return Err(NorErrorType::FlashStorageErrorOutOfBounds);
        }

        if offset + bytes.len() as u32 > self.capacity as u32 {
            return Err(NorErrorType::FlashStorageErrorOutOfBounds);
        }

        // Enable Write
        let write_enable_cmd = NorStorageCmd {
            cmd_lb: 0x06,
            cmd_ub: Some(0xF9),
            addr: None,
            addr_width: None,
            bus_width: NorStorageBusWidth::Octal,
            mode: NorStorageCmdMode::DDR,
            dummy: NorStorageDummyCycles::Clocks(0),
            cmdtype: None,
            data_bytes: None,
        };
        let _ = bus_ref.send_command(write_enable_cmd, None, None);

        // Check write enable status
        let read_status_cmd = NorStorageCmd {
            cmd_lb: 0x05,
            cmd_ub: Some(0xFA),
            addr: None,
            addr_width: Some(0x20),
            bus_width: NorStorageBusWidth::Octal,
            mode: NorStorageCmdMode::DDR,
            dummy: NorStorageDummyCycles::Clocks(0x18),
            cmdtype: Some(NorStorageCmdType::Read),
            data_bytes: Some(1),
        };
        let _ = bus_ref.send_command(read_status_cmd, Some(&mut status), None);

        // Page Program
        let mut write_start_ptr = 0;
        let mut write_end_ptr = bytes.len() as u32;

        loop {
            if write_start_ptr > bytes.len() as u32 {
                break;
            }
            let write_cmd = NorStorageCmd {
                cmd_lb: 0x12,
                cmd_ub: Some(0xED),
                addr: Some(offset),
                addr_width: Some(4),
                bus_width: NorStorageBusWidth::Octal,
                mode: NorStorageCmdMode::DDR,
                dummy: NorStorageDummyCycles::Clocks(0),
                cmdtype: Some(NorStorageCmdType::Write),
                data_bytes: Some(Self::WRITE_SIZE as u32),
            };
            let _ = bus_ref.send_command(
                write_cmd,
                None,
                Some(&bytes[write_start_ptr as usize..write_end_ptr as usize]),
            );
            write_end_ptr += Self::WRITE_SIZE as u32;
            write_start_ptr = write_end_ptr;
        }

        Ok(())
    }
}

impl<T: BlockingNorStorageBusDriver> MacronixDeviceDriver<T, Blocking> {
    pub fn new_blocking(storagebusdriver: T, capacity: usize) -> Result<Self, ()> {
        Ok(Self {
            storagebusdriver,
            capacity,
            _phantom: core::marker::PhantomData,
        })
    }
}

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    // Consider this is a storage service or file system service
    // As per the design, this service is supposed to instantiate low level bus object and configure the bus
    // and pass it to the storage device driver when creating it as a dependency injection
    // Bus drivers -
    //      1. FlexspiNorStorageBus
    //      2. SpiNorStorageBus

    let mut read_data = [0_u8; 4];
    let write_data = [0x55_u8; 4];

    let flash_config = FlexspiDeviceConfig {
        flexspi_root_clk: 48000000,
        is_sck2_enabled: false,
        // Flash size in this struct is in KB, so divide by 1KB
        flash_size_kb: 0x10000, // 64 MB
        cs_interval_unit: Csintervalunit::Csintervalunit0,
        cs_interval: 0,
        cs_hold_time: 3,
        cs_setup_time: 3,
        data_valid_time: 2,
        columnspace: 0,
        enable_word_address: false,
        awr_seq_index: 0,
        awr_seq_number: 0,
        ard_seq_index: 0,
        ard_seq_number: 0,
        ahb_write_wait_unit: Awrwaitunit::Awrwaitunit2,
        ahb_write_wait_interval: 0,
        enable_write_mask_port_a: Wmena::Wmena0,
        enable_write_mask_port_b: Wmenb::Wmenb0,
    };
    let ahb_buffer_config = FlexspiAhbBufferConfig {
        priority: 0,
        master_index: 0,
        buffer_size: 256,
        enable_prefetch: true,
    };

    let ahb_config = AhbConfig {
        enable_ahb_write_ip_rx_fifo: false,
        enable_ahb_write_ip_tx_fifo: false,
        ahb_grant_timeout_cycle: 0xff,
        ahb_bus_timeout_cycle: 0xffff,
        resume_wait_cycle: 0x20,
        buffer: [ahb_buffer_config; 8],
        enable_clear_ahb_buffer_opt: Clrahbbufopt::Clrahbbufopt0,
        enable_read_address_opt: Readaddropt::Readaddropt1,
        enable_ahb_prefetch: true,
        enable_ahb_bufferable: Bufferableen::Bufferableen1,
        enable_ahb_cachable: Cachableen::Cachableen1,
    };

    let flexspi_config = FlexspiConfig {
        rx_sample_clock: Rxclksrc::Rxclksrc0,
        enable_sck_free_running: Sckfreerunen::Sckfreerunen0,
        enable_combination: false,
        enable_doze: Dozeen::Dozeen0, // TODO - Check back after analyzing system low power mode requirements
        enable_half_speed_access: Hsen::Hsen0,
        enable_sck_b_diff_opt: Sckbdiffopt::Sckbdiffopt0,
        enable_same_config_for_all: Samedeviceen::Samedeviceen0,
        seq_timeout_cycle: 0xFFFF,
        ip_grant_timeout_cycle: 0xff,
        ahb_config,
    };

    let mut flexspi_storage = FlexspiNorStorageBus::new_blocking_octal_config(
        p.FLEXSPI, // FlexSPI peripheral
        p.PIO1_11,
        p.PIO1_12,
        p.PIO1_13,
        p.PIO1_14,
        p.PIO2_17,
        p.PIO2_18,
        p.PIO2_22,
        p.PIO2_23,
        p.PIO1_29,
        p.PIO2_19,
        FlexspiConfigPortData {
            port: FlexSpiFlashPort::PortB,                                 // FlexSPI port
            dev_instance: FlexSpiFlashPortDeviceInstance::DeviceInstance0, // FlexSPI device instance
            rx_watermark: 0x8,
            tx_watermark: 0x8,
        },
    );

    // Configure the Flexspi controller
    let _ = flexspi_storage.configport.configure_flexspi(&flexspi_config); // Configure the Flexspi controller

    let _ = flexspi_storage
        .configport
        .configure_device_port(&flash_config, &flexspi_config); // Configure the Flash device specific parameters like CS time, etc

    // Instantiate the storage device driver and inject the bus driver dependency
    let mut device_driver = MacronixDeviceDriver::new_blocking(flexspi_storage, 0x4000000).unwrap();

    // Read JEDEC ID
    let mut jedec_id = [0_u8; 4];
    device_driver.get_jedec_id(&mut jedec_id);

    info!("Jedec Mfg ID = {:02X}", jedec_id[0]);
    info!("Jedec Memory Type = {:02X}", jedec_id[1]);
    info!("Jedec Capacity = {:02X}", jedec_id[2]);

    // Erase the flash sectors
    let _ = device_driver.erase(ADDR, ADDR);

    // Program the flash
    let _ = device_driver.write(ADDR, &write_data);

    info!("Array after writing");
    let _ = device_driver.read(ADDR, &mut read_data);
    for (i, item) in read_data.iter().enumerate() {
        info!("data[{}]: {:02X}", i, *item);
    }

    loop {
        Timer::after_millis(2000).await;
    }
}
