#![no_std]

use mimxrt600_fcb::FlexSpiLutOpcode::{
    CMD_DDR, CMD_SDR, DUMMY_DDR, RADDR_DDR, READ_DDR, READ_SDR, STOP, WRITE_DDR, WRITE_SDR,
};
use mimxrt600_fcb::FlexSpiNumPads::{Octal, Single};
use mimxrt600_fcb::{flexspi_lut_seq, FlexSPIFlashConfigurationBlock};
use {defmt_rtt as _, panic_probe as _};

// auto-generated version information from Cargo.toml
include!(concat!(env!("OUT_DIR"), "/biv.rs"));

#[link_section = ".otfad"]
#[used]
static OTFAD: [u8; 256] = [0; 256];

#[rustfmt::skip]
#[link_section = ".fcb"]
#[used]
static FCB_685EVK: FlexSPIFlashConfigurationBlock = FlexSPIFlashConfigurationBlock::build().lookup_table([
    // Read
    flexspi_lut_seq(CMD_DDR, Octal, 0xee, CMD_DDR, Octal, 0x11),
    flexspi_lut_seq(RADDR_DDR, Octal, 0x20, DUMMY_DDR, Octal, 0x29),
    flexspi_lut_seq(READ_DDR, Octal, 0x04, STOP, Single, 0x00),
    0,
    // Read status SPI
    flexspi_lut_seq(CMD_SDR, Single, 0x05, READ_SDR, Single, 0x04),
    0,
    0,
    0,
    // Read status OPI
    flexspi_lut_seq(CMD_DDR, Octal, 0x05, CMD_DDR, Octal, 0xFA),
    flexspi_lut_seq(RADDR_DDR, Octal, 0x20, DUMMY_DDR, Octal, 0x14),
    flexspi_lut_seq(READ_DDR, Octal, 0x04, STOP, Single, 0x00),
    0,
    // Write enable
    flexspi_lut_seq(CMD_SDR, Single, 0x06, STOP, Single, 0x00),
    0,
    0,
    0,
    // Write enable - OPI
    flexspi_lut_seq(CMD_DDR, Octal, 0x06, CMD_DDR, Octal, 0xF9),
    0,
    0,
    0,
    // Erase Sector
    flexspi_lut_seq(CMD_DDR, Octal, 0x21, CMD_DDR, Octal, 0xDE),
    flexspi_lut_seq(RADDR_DDR, Octal, 0x20, STOP, Single, 0x00),
    0,
    0,
    // Enable OPI DDR mode
    flexspi_lut_seq(CMD_SDR, Single, 0x72, CMD_SDR, Single, 0x00),
    flexspi_lut_seq(CMD_SDR, Single, 0x00, CMD_SDR, Single, 0x00),
    flexspi_lut_seq(CMD_SDR, Single, 0x00, WRITE_SDR, Single, 0x01),
    0,
    // Unused
    0,
    0,
    0,
    0,
    // Erase block
    flexspi_lut_seq(CMD_DDR, Octal, 0xDC, CMD_DDR, Octal, 0x23),
    flexspi_lut_seq(RADDR_DDR, Octal, 0x20, STOP, Single, 0x00),
    0,
    0,
    // Page program
    flexspi_lut_seq(CMD_DDR, Octal, 0x12, CMD_DDR, Octal, 0xED),
    flexspi_lut_seq(RADDR_DDR, Octal, 0x20, WRITE_DDR, Octal, 0x04),
    0,
    0,
    // Unused
    0,
    0,
    0,
    0,
    // Erase chip
    flexspi_lut_seq(CMD_DDR, Octal, 0x60, CMD_DDR, Octal, 0x9F),
    0,
    0,
    0,
    // Remainder is unused
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
]);

#[link_section = ".keystore"]
#[used]
static KEYSTORE: [u8; 2048] = [0; 2048];
