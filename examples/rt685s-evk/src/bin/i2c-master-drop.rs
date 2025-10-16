#![no_std]
#![no_main]

use defmt::{error, info};
use embassy_executor::Spawner;
use embassy_imxrt::{bind_interrupts, i2c, peripherals};
use embassy_time::Timer;
use embedded_hal_async::i2c::I2c;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

const ACC_ADDR: u8 = 0x1E;
const ACC_ID_REG: u8 = 0x0D;
const ACC_ID: u8 = 0xC7;

bind_interrupts!(struct Irqs {
    FLEXCOMM2 => i2c::InterruptHandler<peripherals::FLEXCOMM2>;
});

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    // Link to data sheet for accelerometer on the RT685S-EVK
    // https://www.nxp.com/docs/en/data-sheet/FXOS8700CQ.pdf
    // Max Freq is 400 kHz
    // Address is 0x1E, 0x1D, 0x1C or 0x1F

    // Link to schematics for RT685S-EVK
    // https://www.nxp.com/downloads/en/design-support/RT685-DESIGNFILES.zip
    // File: SPF-35099_E2.pdf
    // Page 10 shows ACC Sensor at I2C address 0x1E

    // Link to RT6xx User Manual
    // https://www.nxp.com/webapp/Download?colCode=UM11147

    // Acc is connected to P0_18_FC2_SCL and P0_17_FC2_SDA for I2C

    let mut p = embassy_imxrt::init(Default::default());

    {
        info!("i2c example - I2cMaster::new");
        let mut i2c = i2c::master::I2cMaster::new_async(
            p.FLEXCOMM2.reborrow(),
            p.PIO0_18.reborrow(),
            p.PIO0_17.reborrow(),
            Irqs,
            Default::default(),
            p.DMA0_CH5.reborrow(),
        )
        .unwrap();

        info!("i2c example - ACC WHO_AM_I register check");
        let mut reg = [0u8; 1];
        reg[0] = 0xAA;
        let result = i2c.write_read(ACC_ADDR, &[ACC_ID_REG], &mut reg).await;
        if result.is_ok() && reg[0] == ACC_ID {
            info!("i2c example - Read WHO_AM_I register: {:02X}", reg[0]);
        } else {
            error!("i2c example - Error reading WHO_AM_I register {}", result.unwrap_err());
        }
    }

    // i2c peripheral is dropped here, so we can re-initialize it to verify that it works after being dropped.
    info!("i2c example - I2cMaster dropped");

    {
        let config = i2c::master::Config {
            speed: i2c::master::Speed::Fast,
            duty_cycle: i2c::master::DutyCycle::new(50).unwrap(),
            ..Default::default()
        };

        info!("i2c example - I2cMaster::new after drop");
        let mut i2c = i2c::master::I2cMaster::new_async(
            p.FLEXCOMM2.reborrow(),
            p.PIO0_18.reborrow(),
            p.PIO0_17.reborrow(),
            Irqs,
            config,
            p.DMA0_CH5.reborrow(),
        )
        .unwrap();

        info!("i2c example - ACC WHO_AM_I register check");
        let mut reg = [0u8; 1];
        reg[0] = 0xAA;
        let result = i2c.write_read(ACC_ADDR, &[ACC_ID_REG], &mut reg).await;
        if result.is_ok() && reg[0] == ACC_ID {
            info!("i2c example - Read WHO_AM_I register: {:02X}", reg[0]);
        } else {
            error!("i2c example - Error reading WHO_AM_I register {}", result.unwrap_err());
        }
    }

    info!("i2c example - Done!  Busy Loop...");
    loop {
        Timer::after_millis(1000).await;
    }
}
