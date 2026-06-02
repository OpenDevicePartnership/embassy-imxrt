#![no_std]
#![no_main]

use defmt::{error, info};
use embassy_executor::Spawner;
use embassy_imxrt::i2c;
use embassy_time::Timer;
use embedded_hal_1::i2c::I2c;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

const ACC_ADDR: u8 = 0x1E;

const ACC_ID_REG: u8 = 0x0D;
const ACC_CTRL_REG: u8 = 0x2A;
const ACC_XYZ_DATA_CFG_REG: u8 = 0x0E;
const ACC_STATUS_REG: u8 = 0x00;

const ACC_ID: u8 = 0xC7;
const ACC_STATUS_DATA_READY: u8 = 0xFF;

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
    // Acc RESET gpio is P1_7_RST
    let p = embassy_imxrt::init(Default::default());

    info!("i2c example - Configure GPIOs");
    use embassy_imxrt::gpio::*;

    // Set GPIO1_7 (Reset) as output
    // Configure IO Pad Control 1_7 for ACC Reset Pin
    //
    // Pin is configured as PIO1_7
    // Disable pull-up / pull-down function
    // Enable pull-down function
    // Disable input buffer function
    // Normal mode
    // Normal drive
    // Analog mux is disabled
    // Pseudo Output Drain is disabled
    // Input function is not inverted
    info!("Configuring GPIO1_7 as output");
    info!("Configuring GPIO1_7 as low");
    let mut _reset_pin = Output::new(
        p.PIO1_7,
        Level::Low,
        DriveMode::PushPull,
        DriveStrength::Normal,
        SlewRate::Standard,
    );

    // Set GPIO1_5 (Interrupt) as input
    // Configure IO Pad Control 1_5 for ACC Interrupt Pin
    //
    // Pin is configured as PIO1_5
    // Disable pull-up / pull-down function
    // Enable pull-down function
    // Disable input buffer function
    // Normal mode
    // Normal drive
    // Analog mux is disabled
    // Pseudo Output Drain is disabled
    // Input function is not inverted
    info!("Configuring GPIO1_5 as input");
    let _isr_pin = Input::new(p.PIO1_5, Pull::Down, Inverter::Disabled);

    info!("i2c example - I2c::new");
    let mut i2c = i2c::master::I2cMaster::new_blocking(p.FLEXCOMM2, p.PIO0_18, p.PIO0_17, Default::default()).unwrap();

    // Read WHO_AM_I register, 0x0D to get value 0xC7 (1100 0111)
    info!("i2c example - ACC WHO_AM_I register check");
    let mut reg = [0u8; 1];
    reg[0] = 0xAA;
    let result = i2c.write_read(ACC_ADDR, &[ACC_ID_REG], &mut reg);
    if result.is_ok() && reg[0] == ACC_ID {
        info!("i2c example - Read WHO_AM_I register: {:02X}", reg[0]);
    } else {
        error!("i2c example - Error reading WHO_AM_I register {}", result.unwrap_err());
    }

    //  Write 0x00 to accelerometer control register 1
    info!("i2c example - Write 0x00 to ACC control register");
    let mut reg = [0u8; 2];
    reg[0] = ACC_CTRL_REG;
    reg[1] = 0x00;
    let result = i2c.write(ACC_ADDR, &reg);
    if result.is_ok() {
        info!("i2c example - Write ctrl reg");
    } else {
        error!("i2c example - Error writing ctrl reg {}", result.unwrap_err());
    }

    //  Write 0x01 to XYZ_DATA_CFG register, set acc range of +/- 4g range and no hpf
    /*  [7]: reserved */
    /*  [6]: reserved */
    /*  [5]: reserved */
    /*  [4]: hpf_out=0 */
    /*  [3]: reserved */
    /*  [2]: reserved */
    /*  [1-0]: fs=01 for accelerometer range of +/-4g range with 0.488mg/LSB */
    /*  databyte = 0x01; */
    info!("i2c example - Write 0x01 to ACC XYZ_DATA_CFG register");
    let mut reg = [0u8; 2];
    reg[0] = ACC_XYZ_DATA_CFG_REG;
    reg[1] = 0x01;
    let result = i2c.write(ACC_ADDR, &reg);
    if result.is_ok() {
        info!("i2c example - Write xyz data cfg reg");
    } else {
        error!("i2c example - Error xyz data cfg reg {}", result.unwrap_err());
    }

    // Write 0x0D to accelerometer control register
    /*  [7-6]: aslp_rate=00 */
    /*  [5-3]: dr=001 for 200Hz data rate (when in hybrid mode) */
    /*  [2]: lnoise=1 for low noise mode */
    /*  [1]: f_read=0 for normal 16 bit reads */
    /*  [0]: active=1 to take the part out of standby and enable sampling */
    /*   databyte = 0x0D; */
    info!("i2c example - Write 0x0D to ACC control register");
    let mut reg = [0u8; 2];
    reg[0] = ACC_CTRL_REG;
    reg[1] = 0x0D;
    let result = i2c.write(ACC_ADDR, &reg);
    if result.is_ok() {
        info!("i2c example - Write ctrl reg");
    } else {
        error!("i2c example - Error writing control reg {}", result.unwrap_err());
    }

    info!("i2c example - Read ACC status register until is ready (0xFF)");
    let mut reg = [0u8; 1];
    reg[0] = 0xAA;
    while reg[0] != ACC_STATUS_DATA_READY {
        let result = i2c.write_read(ACC_ADDR, &[ACC_STATUS_REG], &mut reg);
        if result.is_ok() {
            info!("i2c example - Read status register: {:02X}", reg[0]);
        } else {
            error!("i2c example - Error reading status register {}", result.unwrap_err());
        }
    }

    /* Accelerometer status register, first byte always 0xFF, then X:Y:Z each 2 bytes, in total 7 bytes */
    info!("i2c example - Read XYZ data from ACC status register");
    for _ in 0..10 {
        let mut reg: [u8; 7] = [0xAA; 7];
        let result = i2c.write_read(ACC_ADDR, &[ACC_STATUS_REG], &mut reg);
        if result.is_ok() {
            info!("i2c example - Read XYZ data: {:02X}", reg);
        } else {
            error!("i2c example - Error reading XYZ data {}", result.unwrap_err());
        }
    }

    info!("i2c example - Done!  Busy Loop...");
    loop {
        Timer::after_millis(1000).await;
    }
}
