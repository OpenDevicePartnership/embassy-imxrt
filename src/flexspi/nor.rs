//! FlexSPI NOR Storage Bus Driver module for the NXP RT6xx family of microcontrollers
//!
use embassy_hal_internal::{Peri, PeripheralType};
#[cfg(feature = "time")]
use embassy_time::Instant;
use mimxrt600_fcb::FlexSpiLutOpcode;
use mimxrt600_fcb::FlexSpiLutOpcode::*;
use paste::paste;
use storage_bus::nor::{
    BlockingNorStorageBusDriver, NorStorageBusError, NorStorageBusWidth, NorStorageCmd, NorStorageCmdMode,
    NorStorageCmdType, NorStorageDummyCycles,
};

use crate::clocks::enable_and_reset;
#[cfg(feature = "time")]
use crate::flexspi::is_expired;
use crate::iopctl::IopctlPin as Pin;
use crate::pac::flexspi::ahbcr::*;
use crate::pac::flexspi::flshcr1::*;
use crate::pac::flexspi::flshcr2::*;
use crate::pac::flexspi::flshcr4::*;
use crate::pac::flexspi::mcr0::*;
use crate::pac::flexspi::mcr2::*;
use crate::{interrupt, peripherals};

macro_rules! configure_ports_a {
    ($port:expr, $regs: ident, $device_config: ident, $flash_size: ident) => {
        paste! {
            $regs.[<flsha $port cr0>]().modify(|_, w| unsafe { w.flshsz().bits($flash_size) });
            $regs.[<flshcr1a $port>]().modify(|_, w| unsafe {
                w.csinterval()
                    .bits($device_config.cs_interval)
                    .tcsh()
                    .bits($device_config.cs_hold_time)
                    .tcss()
                    .bits($device_config.cs_setup_time)
                    .cas()
                    .bits($device_config.columnspace)
                    .wa()
                    .bit($device_config.enable_word_address)
                    .csintervalunit()
                    .variant($device_config.cs_interval_unit)
            });
            $regs.[<flshcr2a $port>]()
                .modify(|_, w| w.awrwaitunit().variant($device_config.ahb_write_wait_unit));

            if $device_config.ard_seq_number > 0 {
                $regs.[<flshcr2a $port>]().modify(|_, w| unsafe {
                    w.ardseqnum()
                        .bits($device_config.ard_seq_number - 1)
                        .ardseqid()
                        .bits($device_config.ard_seq_index)
                });
            }
        }
    };
}

macro_rules! configure_ports_b {
    ($port:expr, $regs: ident, $device_config: ident, $flash_size: ident) => {
        paste! {
            $regs.[<flshb $port cr0>]().modify(|_, w| unsafe { w.flshsz().bits($flash_size) });
            $regs.[<flshcr1b $port>]().modify(|_, w| unsafe {
                w.csinterval()
                    .bits($device_config.cs_interval)
                    .tcsh()
                    .bits($device_config.cs_hold_time)
                    .tcss()
                    .bits($device_config.cs_setup_time)
                    .cas()
                    .bits($device_config.columnspace)
                    .wa()
                    .bit($device_config.enable_word_address)
                    .csintervalunit()
                    .variant($device_config.cs_interval_unit)
            });
            $regs.[<flshcr2b $port>]()
                .modify(|_, w| w.awrwaitunit().variant($device_config.ahb_write_wait_unit));

            if $device_config.ard_seq_number > 0 {
                $regs.[<flshcr2b $port>]().modify(|_, w| unsafe {
                    w.ardseqnum()
                        .bits($device_config.ard_seq_number - 1)
                        .ardseqid()
                        .bits($device_config.ard_seq_index)
                });
            }
        }
    };
}

const FIFO_SLOT_SIZE: u32 = 4; // 4 bytes
const OPERATION_SEQ_NUMBER: u8 = 0;
const LUT_UNLOCK_CODE: u32 = 0x5AF05AF0;

const MAX_PACKET_SIZE: u32 = 65535; // 65,535 bytes
const MAX_TRANSMIT_SIZE: u32 = 1024; // 1024 bytes
const MAX_RECEIVE_SIZE: u32 = 512; // 512 bytes

#[cfg(feature = "time")]
const CMD_COMPLETION_TIMEOUT: u64 = 10; // 10 millisecond
#[cfg(feature = "time")]
const DATA_FILL_TIMEOUT: u64 = 10; // 10 millisecond
#[cfg(feature = "time")]
const TX_FIFO_FREE_WATERMARK_TIMEOUT: u64 = 10; // 10 millisecond
#[cfg(feature = "time")]
const RESET_TIMEOUT: u64 = 10; // 10 millisecond
#[cfg(feature = "time")]
const IDLE_TIMEOUT: u64 = 10; // 10 millisecond

const CLOCK_100MHZ: u32 = 100_000_000;
const DELAYCELLUNIT: u32 = 75; // 75ps

#[derive(Clone, Copy, Debug)]
/// FlexSPI Port Enum.
pub enum FlexSpiFlashPort {
    /// FlexSPI Port A
    PortA,
    /// FlexSPI Port B
    PortB,
}

#[derive(Clone, Copy, Debug)]
/// FlexSPI Flash Port Device Instance Enum.
pub enum FlexSpiFlashPortDeviceInstance {
    /// Device Instance 0
    DeviceInstance0,
    /// Device Instance 1
    DeviceInstance1,
}

/// FlexSPI Configuration Port data structure
pub struct FlexspiConfigPortData {
    /// FlexSPI Port - PortA or PortB
    pub port: FlexSpiFlashPort,
    /// FlexSPI Flash Port Device Instance - DeviceInstance0 or DeviceInstance1
    pub dev_instance: FlexSpiFlashPortDeviceInstance,
    /// RX watermark level
    pub rx_watermark: u8,
    /// TX watermark level
    pub tx_watermark: u8,
}

#[derive(Clone, Copy, Debug)]
/// FlexSPI Bus Width Enum.
pub enum FlexSpiBusWidth {
    /// Single bit bus width
    Single,
    /// Dual bit bus width
    Dual,
    /// Quad bit bus width
    Quad,
    /// Octal bit bus width
    Octal,
}

#[derive(Clone, Copy, Debug)]
/// FlexSPI Chip Select Interval unit Enum.
pub enum FlexspiCsIntervalCycleUnit {
    /// CS interval unit is 1 cycle
    Cycle1,
    /// CS interval unit is 256 cycle
    Cycle256,
}
#[derive(Clone, Copy, Debug)]
/// FlexSPI AHB Write Wait unit Enum.
pub enum FlexspiAhbWriteWaitUnit {
    /// AWRWAIT unit is 2 ahb clock cycle
    AhbCycle2,
    /// AWRWAIT unit is 8 ahb clock cycle.
    AhbCycle8,
    /// AWRWAIT unit is 32 ahb clock cycle.
    AhbCycle32,
    /// AWRWAIT unit is 128 ahb clock cycle.   
    AhbCycle128,
    /// AWRWAIT unit is 512 ahb clock cycle.   
    AhbCycle512,
    /// AWRWAIT unit is 2048 ahb clock cycle.  
    AhbCycle2048,
    /// AWRWAIT unit is 8192 ahb clock cycle.  
    AhbCycle8192,
    /// AWRWAIT unit is 32768 ahb clock cycle.
    AhbCycle32768,
}

#[derive(Clone, Copy, Debug)]
/// FlexSPI Read Sample Clock Enum.
pub enum FlexspiReadSampleClock {
    /// Dummy Read strobe generated by FlexSPI self.flexspi_ref and loopback internally
    LoopbackInternally,
    /// Dummy Read strobe generated by FlexSPI self.flexspi_ref and loopback from DQS pad
    LoopbackFromDqsPad,
    /// SCK output clock and loopback from SCK pad
    LoopbackFromSckPad,
    /// Flash provided Read strobe and input from DQS pad
    ExternalInputFromDqsPad,
}

#[derive(Clone, Copy, Debug)]
/// FlexSPI AHB Buffer Configuration structure
pub struct FlexspiAhbBufferConfig {
    /// This priority for AHB Master Read which this AHB RX Buffer is assigned.
    pub priority: u8,
    /// AHB Master ID the AHB RX Buffer is assigned.       
    pub master_index: u8,
    /// AHB buffer size in byte.   
    pub buffer_size: u16,
    /// AHB Read Prefetch Enable for current AHB RX Buffer corresponding Master, allows to prefetch
    /// data for AHB read access.
    pub enable_prefetch: bool,
}

#[derive(Clone, Copy, Debug)]
/// Flash Device configuration
pub struct FlexspiDeviceConfig {
    /// FLEXSPI serial root clock
    pub flexspi_root_clk: u32,
    /// FLEXSPI use SCK2
    pub is_sck2_enabled: bool,
    /// Flash size in KByte
    pub flash_size_kb: u32,
    /// CS interval unit, 1 or 256 cycle
    pub cs_interval_unit: Csintervalunit,
    /// CS line assert interval, multiply CS interval unit to get the CS line assert interval cycles
    pub cs_interval: u16,
    /// CS line hold time
    pub cs_hold_time: u8,
    /// CS line setup time
    pub cs_setup_time: u8,
    /// Data valid time for external device                          
    pub data_valid_time: u8,
    /// Column space size                       
    pub columnspace: u8,
    /// If enable word address                        
    pub enable_word_address: bool,
    /// Sequence ID for AHB write command                    
    pub awr_seq_index: u8,
    /// Sequence number for AHB write command
    pub awr_seq_number: u8,
    /// Sequence ID for AHB read command                       
    pub ard_seq_index: u8,
    /// Sequence number for AHB read command
    pub ard_seq_number: u8,
    /// AHB write wait unit
    pub ahb_write_wait_unit: Awrwaitunit,
    /// AHB write wait interval, multiply AHB write interval unit to get the AHB write wait cycles
    pub ahb_write_wait_interval: u16,
    /// Enable/Disable FLEXSPI drive DQS pin as write mask
    pub enable_write_mask_port_a: Wmena,
    /// Enable/Disable FLEXSPI drive DQS pin as write mask
    pub enable_write_mask_port_b: Wmenb,
}

#[derive(Clone, Copy, Debug)]
/// AHB configuration structure
pub struct AhbConfig {
    /// Enable AHB bus write access to IP TX FIFO.
    pub enable_ahb_write_ip_tx_fifo: bool,
    /// Enable AHB bus write access to IP RX FIFO.
    pub enable_ahb_write_ip_rx_fifo: bool,
    /// Timeout wait cycle for AHB command grant, timeout after ahbGrantTimeoutCyle*1024 AHB clock cycles.
    pub ahb_grant_timeout_cycle: u8,
    /// Timeout wait cycle for AHB read/write access, timeout after ahbBusTimeoutCycle*1024 AHB clock cycles.
    pub ahb_bus_timeout_cycle: u16,
    /// Wait cycle for idle state before suspended command sequence resume, timeout after ahbBusTimeoutCycle
    /// AHB clock cycles.
    pub resume_wait_cycle: u8,
    /// AHB buffer size.
    pub buffer: [FlexspiAhbBufferConfig; 8],
    /// Enable/disable automatically clean AHB RX Buffer and TX Buffer when FLEXSPI returns STOP mode ACK.
    pub enable_clear_ahb_buffer_opt: Clrahbbufopt,
    /// Enable/disable remove AHB read burst start address alignment limitation. when enable, there is no AHB
    /// read burst start address alignment limitation.
    pub enable_read_address_opt: Readaddropt,
    /// Enable/disable AHB read prefetch feature, when enabled, FLEXSPI will fetch more data than current AHB burst.
    pub enable_ahb_prefetch: bool,
    /// Enable/disable AHB bufferable write access support, when enabled, FLEXSPI return before waiting for command
    /// execution finished.
    pub enable_ahb_bufferable: Bufferableen,
    /// Enable AHB bus cachable read access support.
    pub enable_ahb_cachable: Cachableen,
}

#[derive(Clone, Copy, Debug)]
/// FlexSPI configuration structure
pub struct FlexspiConfig {
    /// Sample Clock source selection for Flash Reading.
    pub rx_sample_clock: Rxclksrc,
    /// Enable/disable SCK output free-running.
    pub enable_sck_free_running: Sckfreerunen,
    /// Enable/disable combining PORT A and B Data Pins (SIOA[3:0] and SIOB[3:0]) to support
    /// Flash Octal mode.
    pub enable_combination: bool,
    /// Enable/disable doze mode support.
    pub enable_doze: Dozeen,
    /// Enable/disable divide by 2 of the clock for half speed commands.
    pub enable_half_speed_access: Hsen,
    /// Enable/disable SCKB pad use as SCKA differential clock output, when enable, Port B flash access
    /// is not available.
    pub enable_sck_b_diff_opt: Sckbdiffopt,
    /// Enable/disable same configuration for all connected devices when enabled, same configuration in
    /// FLASHA1CRx is applied to all.
    pub enable_same_config_for_all: Samedeviceen,
    /// Timeout wait cycle for command sequence execution, timeout after ahbGrantTimeoutCyle*1024 serial
    /// root clock cycles.
    pub seq_timeout_cycle: u16,
    /// Timeout wait cycle for IP command grant, timeout after ipGrantTimeoutCycle*1024 AHB clock cycles.
    pub ip_grant_timeout_cycle: u8,
    /// AHB configuration
    pub ahb_config: AhbConfig,
}

mod sealed {
    /// simply seal a trait
    pub trait Sealed {}
}

impl<T> sealed::Sealed for T {}

struct Info {
    regs: &'static crate::pac::flexspi::RegisterBlock,
}

trait SealedInstance {
    fn info() -> Info;
}
/// Instance trait to be used for instanciating for FlexSPI HW instance
#[allow(private_bounds)]
pub trait Instance: SealedInstance + PeripheralType + 'static + Send {
    /// Interrupt for this SPI instance.
    type Interrupt: interrupt::typelevel::Interrupt;
}

impl SealedInstance for crate::peripherals::FLEXSPI {
    fn info() -> Info {
        Info {
            // SAFETY: We are just saving the reference of the FlexSPI peripheral address
            regs: unsafe { &*crate::pac::Flexspi::ptr() },
        }
    }
}

impl Instance for crate::peripherals::FLEXSPI {
    type Interrupt = crate::interrupt::typelevel::FLEXSPI;
}
/// Driver mode.
#[allow(private_bounds)]
pub trait Mode: sealed::Sealed {}

/// Blocking mode.
pub struct Blocking;
impl Mode for Blocking {}

/// Async mode.
pub struct Async;
impl Mode for Async {}

#[allow(private_interfaces)]
/// FlexSPI Configuration Manager Port
pub struct FlexSpiConfigurationPort {
    /// Flash Port
    flash_port: FlexSpiFlashPort,
    /// Device Instance
    device_instance: FlexSpiFlashPortDeviceInstance,
    /// FlexSPI HW Info Object
    info: Info,
}

/// FlexSPI instance
pub struct FlexspiNorStorageBus<'d, M: Mode> {
    /// FlexSPI HW Info Object
    info: Info,
    /// RX FIFO watermark level
    rx_watermark: u8,
    /// TX FIFO Watermark Level
    tx_watermark: u8,
    /// Mode Phantom object
    _mode: core::marker::PhantomData<M>,
    /// FlexSPI Configuration Port
    pub configport: FlexSpiConfigurationPort,
    phantom: core::marker::PhantomData<&'d ()>,
}

#[derive(PartialEq)]
enum LutInstrNum {
    /// First instruction in the LUT
    First,
    /// Second instruction in the LUT
    Second,
}

// LUT instruction pointer to be used during LUT programming
struct LutInstrCookie {
    seq_num: u8,
    instr_num: LutInstrNum,
}

impl LutInstrCookie {
    fn next_instruction(&mut self) {
        if self.instr_num == LutInstrNum::Second {
            self.seq_num += 1;
            self.instr_num = LutInstrNum::First;
        } else {
            self.instr_num = LutInstrNum::Second;
        }
    }
}

#[derive(Debug, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[allow(non_snake_case)]
/// FlexSPI command result
struct CmdResult {
    /// AHB read command error
    AhbReadCmdErr: bool,
    /// AHB write command error
    AhbWriteCmdErr: bool,
    /// IP command error
    IpCmdErr: bool,
}

#[derive(Debug, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[allow(non_snake_case)]
enum FlexSpiError {
    /// Flash command grant error
    CmdGrantErr { result: CmdResult }, // INTR[AHBCMDGE] = 1 / INTR[IPCMDGE] = 1
    /// Flash command check error
    CmdCheckErr { result: CmdResult }, // INTR[AHBCMDERR] = 1/ INTR[IPCMDERR] = 1
    /// Flash command execution error
    CmdExecErr { result: CmdResult }, // INTR[AHBCMDERR] = 1/ INTR[SEQTIMEOUT] = 1/ INTR[IPCMDERR] = 1
    /// AHB bus timeout error
    AhbBusTimeout { result: CmdResult },
    /// Data learning failed
    DataLearningFailed, // INTR[DATALEARNFAIL] = 1
}

impl From<FlexSpiError> for NorStorageBusError {
    fn from(err: FlexSpiError) -> Self {
        match err {
            FlexSpiError::CmdGrantErr { result: _ } => NorStorageBusError::StorageBusNotAvailable,
            FlexSpiError::CmdCheckErr { result: _ } => NorStorageBusError::StorageBusIoError,
            FlexSpiError::CmdExecErr { result: _ } => NorStorageBusError::StorageBusIoError,
            FlexSpiError::AhbBusTimeout { result: _ } => NorStorageBusError::StorageBusIoError,
            FlexSpiError::DataLearningFailed => NorStorageBusError::StorageBusInternalError,
        }
    }
}

impl FlexSpiError {
    /// Get the description of the error
    pub fn describe<'a, M: Mode>(&self, flexspi: &'a FlexspiNorStorageBus<M>) {
        match self {
            FlexSpiError::CmdGrantErr { result } => {
                if result.AhbReadCmdErr {
                    info!("AHB bus error response for Read Command. Command grant timeout");
                }
                if result.AhbWriteCmdErr {
                    info!("AHB bus error response for Write Command. Command grant timeout");
                }
                if result.IpCmdErr {
                    info!("IP command grant timeout. Command grant timeout");
                }
            }
            FlexSpiError::CmdCheckErr { result } => {
                if result.AhbWriteCmdErr {
                    info!(
                        "LUT sequence ID = {:08X}",
                        flexspi.info.regs.sts1().read().ahbcmderrid().bits()
                    );

                    info!(
                        "Sequnce Error Code = {:08X}",
                        flexspi.info.regs.sts1().read().ahbcmderrcode().bits()
                    );
                    info!(
                        "Command is not executed when error detected in command check.
                    Following are the possible reasons:
                    - AHB write command with JMP_ON_CS instruction used in the sequence
                    - There is unknown instruction opcode in the sequence.
                    - Instruction DUMMY_SDR/DUMMY_RWDS_SDR used in DDR sequence.
                    - Instruction DUMMY_DDR/DUMMY_RWDS_DDR used in SDR sequence."
                    );
                }
                if result.AhbReadCmdErr {
                    info!(
                        "LUT sequence ID = {:08X}",
                        flexspi.info.regs.sts1().read().ahbcmderrid().bits()
                    );

                    info!(
                        "Sequnce Error Code = {:08X}",
                        flexspi.info.regs.sts1().read().ahbcmderrcode().bits()
                    );
                    info!(
                        "Command is not executed when error detected in command check.
                    Following are the possible reasons:
                    - There is unknown instruction opcode in the sequence
                    - Instruction DUMMY_SDR/DUMMY_RWDS_SDR used in DDR sequence.
                    - Instruction DUMMY_DDR/DUMMY_RWDS_DDR used in SDR sequence."
                    );
                }
                if result.IpCmdErr {
                    info!(
                        "LUT sequence ID = {:08X}",
                        flexspi.info.regs.sts1().read().ipcmderrid().bits()
                    );

                    info!(
                        "Sequnce Error Code = {:08X}",
                        flexspi.info.regs.sts1().read().ipcmderrcode().bits()
                    );

                    info!(
                        "Command is not executed when error detected in command check.
                    Following are the possible reasons:
                    - IP command with JMP_ON_CS instruction used in the sequence
                    - There is unknown instruction opcode in the sequence.
                    - Instruction DUMMY_SDR/DUMMY_RWDS_SDR used in DDR sequence
                    - Instruction DUMMY_DDR/DUMMY_RWDS_DDR used in SDR sequence
                    - Flash boundary across"
                    );
                }
            }
            FlexSpiError::CmdExecErr { result } => {
                if result.AhbWriteCmdErr {
                    info!(
                        "LUT sequence ID = {:08X}",
                        flexspi.info.regs.sts1().read().ahbcmderrid().bits()
                    );

                    info!(
                        "Sequnce Error Code = {:08X}",
                        flexspi.info.regs.sts1().read().ahbcmderrcode().bits()
                    );
                    info!(
                        "There will be AHB bus error response except the following cases: 
                        - AHB write command is triggered by flush (INCR burst ended with AHB_TX_BUF not empty)
                        - AHB bufferable write access and bufferable enabled (AHBCR[BUFFERABLEEN]=0x1)
                    Following are possible reasons for this error - 
                        - Command timeout during execution"
                    );
                }
                if result.AhbReadCmdErr {
                    info!(
                        "LUT sequence ID = {:08X}",
                        flexspi.info.regs.sts1().read().ahbcmderrid().bits()
                    );

                    info!(
                        "Sequnce Error Code = {:08X}",
                        flexspi.info.regs.sts1().read().ahbcmderrcode().bits()
                    );
                    info!(
                        "There will be AHB bus error response. Following are possible reasons for this error - 
                        - Command timeout during execution"
                    );
                }
                if result.IpCmdErr {
                    info!(
                        "LUT sequence ID = {:08X}",
                        flexspi.info.regs.sts1().read().ipcmderrid().bits()
                    );

                    info!(
                        "Sequnce Error Code = {:08X}",
                        flexspi.info.regs.sts1().read().ipcmderrcode().bits()
                    );
                    info!(
                        "Following are possible reasons for this error - 
                        - Command timeout during execution"
                    );
                }
            }
            FlexSpiError::AhbBusTimeout { result } => {
                if result.AhbReadCmdErr || result.AhbWriteCmdErr {
                    info!(
                        "There will be AHB bus error response. Following are possible reasons for this error - 
                        - AHB bus timeout (no bus ready return)"
                    );
                } else {
                    info!("Unknown AHB bus timeout error");
                }
            }
            FlexSpiError::DataLearningFailed => info!("Data learning failed"),
        }
    }
}

impl<'d> BlockingNorStorageBusDriver for FlexspiNorStorageBus<'d, Blocking> {
    fn send_command(
        &mut self,
        cmd: NorStorageCmd,
        read_buf: Option<&mut [u8]>,
        write_buf: Option<&[u8]>,
    ) -> Result<(), NorStorageBusError> {
        let regs = self.info.regs;

        self.setup_ip_transfer(OPERATION_SEQ_NUMBER, cmd.addr, cmd.data_bytes);

        // Program the LUT instructions for the command
        self.program_lut(&cmd, OPERATION_SEQ_NUMBER as u8);

        // Start the transfer
        self.execute_ip_cmd();

        // Wait for command to complete
        // This wait is for FlexSPI to send the command to the Flash device
        // But the command completion in the flash needs to be checked separately
        // by reading the status register of the flash device
        let status = self.wait_for_cmd_completion();
        if status.is_err() {
            return status;
        }

        // Check for any errors during the transfer
        self.check_transfer_status().map_err(|e| {
            e.describe(self);
            <FlexSpiError as Into<FlexSpiError>>::into(e)
        })?;

        if let Some(data_cmd) = cmd.cmdtype {
            match data_cmd {
                NorStorageCmdType::Read => {
                    let buffer = read_buf.ok_or(NorStorageBusError::StorageBusInternalError)?;
                    if cmd.data_bytes.unwrap() > MAX_PACKET_SIZE {
                        return Err(NorStorageBusError::StorageBusInternalError);
                    }
                    self.read_data(cmd, buffer)?;
                }
                NorStorageCmdType::Write => {
                    let buffer = write_buf.ok_or(NorStorageBusError::StorageBusInternalError)?;
                    if cmd.data_bytes.unwrap() > MAX_PACKET_SIZE {
                        return Err(NorStorageBusError::StorageBusInternalError);
                    }
                    self.write_data(cmd, buffer)?;
                }
            }
        }

        // It is possible that IP command completes but the FlexSPI backend
        // is still processing the data from TX/RX FIFO. Unless we wait for the
        // Sequence engine to become idle, we could see Command grant error for
        // subsequent commands post data read/write command
        #[cfg(feature = "time")]
        {
            let start = Instant::now();

            while !(regs.sts0().read().arbidle().bit_is_set() && regs.sts0().read().seqidle().bit_is_set()) {
                let timedout = is_expired(start, IDLE_TIMEOUT);
                if timedout {
                    return Err(NorStorageBusError::StorageBusIoError);
                }
            }
        }
        #[cfg(not(feature = "time"))]
        {
            while !(regs.sts0().read().arbidle().bit_is_set() && regs.sts0().read().seqidle().bit_is_set()) {}
        }

        Ok(())
    }
}

impl<'d, M: Mode> FlexspiNorStorageBus<'d, M> {
    fn setup_ip_transfer(&mut self, seq_id: u8, addr: Option<u32>, size: Option<u32>) {
        self.info.regs.ipcr0().modify(|_, w| unsafe {
            //SAFETY - We are writing the address register. There is no issue from safety perspective
            w.sfar().bits(addr.unwrap_or(0))
        });

        // Set the Command sequence ID

        self.info.regs.ipcr1().modify(|_, w| unsafe {
            // SAFETY: Operation is safe as we are programming the sequence ID to be used for the transfer
            w.iseqid().bits(seq_id as u8)
        });

        // Reset the sequence pointer
        self.info.regs.flshcr2(0).modify(|_, w| w.clrinstrptr().set_bit());
        self.info.regs.flshcr2(1).modify(|_, w| w.clrinstrptr().set_bit());
        self.info.regs.flshcr2(2).modify(|_, w| w.clrinstrptr().set_bit());
        self.info.regs.flshcr2(3).modify(|_, w| w.clrinstrptr().set_bit());

        // Disable DMA for TX and RX and Reset RX and TX FIFO
        self.info
            .regs
            .iptxfcr()
            .modify(|_, w| w.txdmaen().clear_bit().clriptxf().set_bit());
        self.info
            .regs
            .iprxfcr()
            .modify(|_, w| w.rxdmaen().clear_bit().clriprxf().set_bit());

        // TODO: Set Tx and Rx watermark
        self.info.regs.iprxfcr().modify(|_, w| unsafe {
            // SAFETY: Operation is safe as we are programming the watermark value to be used for the transfer
            w.rxwmrk().bits((self.rx_watermark / 8) - 1 as u8)
        });

        // Set the data length
        // Max RX FIFO size is MAX_FLEXSPI_TRANSFER_SIZE bytes
        // TODO - We want to avoid RX FIFO overflow for now. We will revisit this later and increase the size
        // once we add overflow handling
        if let Some(size) = size {
            self.info.regs.ipcr1().modify(|_, w| unsafe {
                // SAFETY: Operation is safe as we are programming the size of the transfer
                w.idatsz().bits(size as u16)
            });
        }
    }

    fn execute_ip_cmd(&mut self) {
        self.info.regs.ipcmd().write(|w| w.trg().set_bit());
    }

    fn check_transfer_status(&self) -> Result<(), FlexSpiError> {
        let intr = self.info.regs.intr().read();

        if intr.ipcmderr().bit_is_set() {
            self.info.regs.intr().modify(|_, w| w.ipcmderr().clear_bit_by_one());
            if intr.seqtimeout().bit_is_set() {
                self.info.regs.intr().modify(|_, w| w.seqtimeout().clear_bit_by_one());
                return Err(FlexSpiError::CmdExecErr {
                    result: CmdResult {
                        AhbReadCmdErr: false,
                        AhbWriteCmdErr: false,
                        IpCmdErr: true,
                    },
                });
            } else {
                return Err(FlexSpiError::CmdCheckErr {
                    result: CmdResult {
                        AhbReadCmdErr: false,
                        AhbWriteCmdErr: false,
                        IpCmdErr: true,
                    },
                });
            }
        } else if intr.ahbcmderr().bit_is_set() {
            self.info.regs.intr().modify(|_, w| w.ahbcmderr().clear_bit_by_one());
            if intr.seqtimeout().bit_is_set() {
                return Err(FlexSpiError::CmdExecErr {
                    result: CmdResult {
                        AhbReadCmdErr: true,
                        AhbWriteCmdErr: true,
                        IpCmdErr: false,
                    },
                });
            } else {
                return Err(FlexSpiError::CmdCheckErr {
                    result: CmdResult {
                        AhbReadCmdErr: true,
                        AhbWriteCmdErr: true,
                        IpCmdErr: false,
                    },
                });
            }
        } else if intr.ahbbustimeout().bit_is_set() {
            self.info
                .regs
                .intr()
                .modify(|_, w| w.ahbbustimeout().clear_bit_by_one());
            return Err(FlexSpiError::AhbBusTimeout {
                result: CmdResult {
                    AhbReadCmdErr: true,
                    AhbWriteCmdErr: true,
                    IpCmdErr: false,
                },
            });
        } else if intr.datalearnfail().bit_is_set() {
            self.info
                .regs
                .intr()
                .modify(|_, w| w.datalearnfail().clear_bit_by_one());
            return Err(FlexSpiError::DataLearningFailed);
        } else if intr.ipcmdge().bit_is_set() {
            self.info.regs.intr().modify(|_, w| w.ipcmdge().clear_bit_by_one());
            return Err(FlexSpiError::CmdGrantErr {
                result: CmdResult {
                    AhbReadCmdErr: false,
                    AhbWriteCmdErr: false,
                    IpCmdErr: true,
                },
            });
        } else if intr.ahbcmdge().bit_is_set() {
            self.info.regs.intr().modify(|_, w| w.ahbcmdge().clear_bit_by_one());
            return Err(FlexSpiError::CmdGrantErr {
                result: CmdResult {
                    AhbReadCmdErr: true,
                    AhbWriteCmdErr: true,
                    IpCmdErr: false,
                },
            });
        } else {
            return Ok(());
        }
    }

    fn write_instr(&self, cookie: &mut LutInstrCookie, opcode: FlexSpiLutOpcode, operand: u8, bus_width: u8) {
        let seq_id = cookie.seq_num as usize;

        if cookie.instr_num == LutInstrNum::First {
            self.write_even_instr(seq_id, opcode, operand, bus_width);
        } else {
            self.write_odd_instr(seq_id, opcode, operand, bus_width);
        }
    }

    fn write_even_instr(&self, seq_id: usize, opcode: FlexSpiLutOpcode, operand: u8, bus_width: u8) {
        self.info.regs.lut(seq_id).modify(|_, w| unsafe {
            w.opcode0()
                .bits(opcode as u8)
                .num_pads0()
                .bits(bus_width)
                .operand0()
                .bits(operand)
        });
    }

    fn write_odd_instr(&self, seq_id: usize, opcode: FlexSpiLutOpcode, operand: u8, bus_width: u8) {
        self.info.regs.lut(seq_id).modify(|_, w| unsafe {
            w.opcode1()
                .bits(opcode as u8)
                .num_pads1()
                .bits(bus_width)
                .operand1()
                .bits(operand)
        });
    }

    fn program_cmd_instruction(&self, cmd: &NorStorageCmd, cookie: &mut LutInstrCookie) {
        let mut cmd_mode: FlexSpiLutOpcode = CMD_DDR;

        if cmd.mode == NorStorageCmdMode::SDR {
            cmd_mode = CMD_SDR;
        }
        let bus_width = match cmd.bus_width {
            NorStorageBusWidth::Single => 0,
            NorStorageBusWidth::Dual => 1,
            NorStorageBusWidth::Quad => 2,
            NorStorageBusWidth::Octal => 3,
        };

        self.write_instr(cookie, cmd_mode, cmd.cmd_lb, bus_width);

        cookie.next_instruction();

        if cmd.cmd_ub.is_some() {
            self.write_instr(cookie, cmd_mode, cmd.cmd_ub.unwrap(), bus_width);
            cookie.next_instruction();
        }
    }

    fn program_addr_instruction(&self, cmd: &NorStorageCmd, cookie: &mut LutInstrCookie) {
        let mut cmd_mode: FlexSpiLutOpcode = RADDR_DDR;

        if cmd.mode == NorStorageCmdMode::SDR {
            cmd_mode = RADDR_SDR;
        }
        let bus_width = match cmd.bus_width {
            NorStorageBusWidth::Single => 0,
            NorStorageBusWidth::Dual => 1,
            NorStorageBusWidth::Quad => 2,
            NorStorageBusWidth::Octal => 3,
        };
        self.write_instr(cookie, cmd_mode, cmd.addr_width.unwrap(), bus_width);

        cookie.next_instruction();
    }

    fn program_dummy_instruction(&self, cmd: &NorStorageCmd, cookie: &mut LutInstrCookie) {
        let mut cmd_mode: FlexSpiLutOpcode = DUMMY_DDR;

        if cmd.mode == NorStorageCmdMode::SDR {
            cmd_mode = DUMMY_SDR;
        }
        let bus_width = match cmd.bus_width {
            NorStorageBusWidth::Single => 0,
            NorStorageBusWidth::Dual => 1,
            NorStorageBusWidth::Quad => 2,
            NorStorageBusWidth::Octal => 3,
        };
        let dummy_val: u8;

        match cmd.dummy {
            NorStorageDummyCycles::Bytes(dummy_bytes) => {
                dummy_val = dummy_bytes;
            }
            NorStorageDummyCycles::Clocks(dummy_cycles) => {
                dummy_val = dummy_cycles;
            }
        }
        self.write_instr(cookie, cmd_mode, dummy_val, bus_width);
        cookie.next_instruction();
    }

    fn program_read_data_instruction(&self, cmd: &NorStorageCmd, cookie: &mut LutInstrCookie, data_length: u8) {
        let mut cmd_mode: FlexSpiLutOpcode = READ_DDR;

        if cmd.mode == NorStorageCmdMode::SDR {
            cmd_mode = READ_SDR;
        }
        let bus_width = match cmd.bus_width {
            NorStorageBusWidth::Single => 0,
            NorStorageBusWidth::Dual => 1,
            NorStorageBusWidth::Quad => 2,
            NorStorageBusWidth::Octal => 3,
        };

        self.write_instr(cookie, cmd_mode, data_length, bus_width);

        cookie.next_instruction();
    }

    fn program_write_data_instruction(&self, cmd: &NorStorageCmd, cookie: &mut LutInstrCookie, data_length: u8) {
        let mut cmd_mode: FlexSpiLutOpcode = WRITE_DDR;

        if cmd.mode == NorStorageCmdMode::SDR {
            cmd_mode = WRITE_SDR;
        }
        let bus_width = match cmd.bus_width {
            NorStorageBusWidth::Single => 0,
            NorStorageBusWidth::Dual => 1,
            NorStorageBusWidth::Quad => 2,
            NorStorageBusWidth::Octal => 3,
        };

        self.write_instr(cookie, cmd_mode, data_length, bus_width);

        cookie.next_instruction();
    }

    fn program_stop_instruction(&self, cookie: &mut LutInstrCookie) {
        let cmd_mode: FlexSpiLutOpcode = STOP;

        self.write_instr(cookie, cmd_mode, 0, 0);
        cookie.next_instruction();
    }

    fn program_lut(&self, cmd: &NorStorageCmd, seq_id: u8) {
        let mut cookie = LutInstrCookie {
            seq_num: seq_id * 4,
            instr_num: LutInstrNum::First,
        };

        // Unlock LUT
        self.info
            .regs
            .lutkey()
            .modify(|_, w| unsafe { w.key().bits(LUT_UNLOCK_CODE) });

        self.info.regs.lutcr().write(|w| w.unlock().set_bit());

        // Clear out the LUT
        self.info
            .regs
            .lut((seq_id * 4) as usize)
            .modify(|_, w| unsafe { w.bits(0) });
        self.info
            .regs
            .lut((seq_id * 4 + 1) as usize)
            .modify(|_, w| unsafe { w.bits(0) });
        self.info
            .regs
            .lut((seq_id * 4 + 2) as usize)
            .modify(|_, w| unsafe { w.bits(0) });
        self.info
            .regs
            .lut((seq_id * 4 + 3) as usize)
            .modify(|_, w| unsafe { w.bits(0) });

        self.program_cmd_instruction(cmd, &mut cookie);

        if cmd.addr_width.is_some() {
            self.program_addr_instruction(cmd, &mut cookie);
        }

        match cmd.dummy {
            NorStorageDummyCycles::Clocks(clk) => {
                if clk > 0 {
                    self.program_dummy_instruction(cmd, &mut cookie);
                }
            }
            _ => {}
        }

        if let Some(transfertype) = cmd.cmdtype {
            match transfertype {
                NorStorageCmdType::Read => {
                    self.program_read_data_instruction(cmd, &mut cookie, cmd.data_bytes.unwrap() as u8);
                }
                NorStorageCmdType::Write => {
                    self.program_write_data_instruction(cmd, &mut cookie, cmd.data_bytes.unwrap() as u8);
                }
            }
        }

        self.program_stop_instruction(&mut cookie);

        // Lock LUT
        self.info
            .regs
            .lutkey()
            .modify(|_, w| unsafe { w.key().bits(LUT_UNLOCK_CODE) });
        self.info.regs.lutcr().modify(|_, w| w.lock().set_bit());
    }
}

impl<'d> FlexspiNorStorageBus<'d, Blocking> {
    fn read_data(&mut self, cmd: NorStorageCmd, read_buf: &mut [u8]) -> Result<(), NorStorageBusError> {
        let size = cmd.data_bytes.ok_or(NorStorageBusError::StorageBusInternalError)?;

        if read_buf.len() != size as usize {
            return Err(NorStorageBusError::StorageBusInternalError);
        }

        for chunk in read_buf.chunks_mut(MAX_RECEIVE_SIZE as usize) {
            self.read_cmd_data(chunk)?;
        }

        Ok(())
    }

    fn write_data(&mut self, cmd: NorStorageCmd, write_buf: &[u8]) -> Result<(), NorStorageBusError> {
        let size = cmd.data_bytes.ok_or(NorStorageBusError::StorageBusInternalError)?;

        if write_buf.len() != size as usize {
            return Err(NorStorageBusError::StorageBusInternalError);
        }

        for chunk in write_buf.chunks(MAX_TRANSMIT_SIZE as usize) {
            self.write_cmd_data(chunk)?;
        }
        Ok(())
    }

    fn wait_for_cmd_completion(&mut self) -> Result<(), NorStorageBusError> {
        #[cfg(feature = "time")]
        {
            let start = Instant::now();
            while self.info.regs.intr().read().ipcmddone().bit_is_clear() {
                let timedout = is_expired(start, CMD_COMPLETION_TIMEOUT);
                if timedout {
                    return Err(NorStorageBusError::StorageBusIoError);
                }
            }
        }
        #[cfg(not(feature = "time"))]
        {
            while self.info.regs.intr().read().ipcmddone().bit_is_clear() {}
        }

        Ok(())
    }

    fn read_cmd_data(&mut self, read_data: &mut [u8]) -> Result<(), NorStorageBusError> {
        let num_rx_watermark_slot;
        let mut size = read_data.len() as u32;

        let error = self.check_transfer_status();

        if let Err(e) = error {
            e.describe(self);
            return Err(NorStorageBusError::StorageBusIoError);
        }

        num_rx_watermark_slot = self.rx_watermark / FIFO_SLOT_SIZE as u8;

        for watermark_sized_chunk in read_data.chunks_mut(self.rx_watermark as usize) {
            if watermark_sized_chunk.len() < self.rx_watermark as usize {
                #[cfg(feature = "time")]
                {
                    let start = Instant::now();
                    while ((self.info.regs.iprxfsts().read().fill().bits() * 8) as u32) < size {
                        let timedout = is_expired(start, DATA_FILL_TIMEOUT);
                        if timedout {
                            return Err(NorStorageBusError::StorageBusInternalError);
                        }
                    }
                }
                #[cfg(not(feature = "time"))]
                {
                    while ((self.info.regs.iprxfsts().read().fill().bits() * 8) as u32) < size {}
                }
            } else {
                #[cfg(feature = "time")]
                {
                    let start = Instant::now();
                    while self.info.regs.intr().read().iprxwa().bit_is_clear() {
                        let timedout = is_expired(start, TX_FIFO_FREE_WATERMARK_TIMEOUT);
                        if timedout {
                            return Err(NorStorageBusError::StorageBusInternalError);
                        }
                    }
                }
                #[cfg(not(feature = "time"))]
                {
                    while self.info.regs.intr().read().iprxwa().bit_is_clear() {}
                }
            }
            for (chunk, slot) in watermark_sized_chunk
                .chunks_mut(FIFO_SLOT_SIZE as usize)
                .zip(0..num_rx_watermark_slot)
            {
                let data = self.info.regs.rfdr(slot as usize).read().bits();
                if chunk.len() < FIFO_SLOT_SIZE as usize {
                    // We cannot do copy from slice as it will cause a panic
                    for i in 0..chunk.len() {
                        chunk[i] = (data >> (i * 8)) as u8;
                    }
                } else {
                    chunk.copy_from_slice(&data.to_le_bytes());
                }
                size -= chunk.len() as u32;
            }
            self.info.regs.intr().modify(|_, w| w.iprxwa().clear_bit_by_one());
        }

        Ok(())
    }

    fn write_cmd_data(&mut self, write_data: &[u8]) -> Result<(), NorStorageBusError> {
        // Check for any errors during the transfer
        let error = self.check_transfer_status();
        if let Err(e) = error {
            e.describe(self);
            return Err(NorStorageBusError::StorageBusIoError);
        }

        let num_tx_watermark_slot = self.tx_watermark / FIFO_SLOT_SIZE as u8;

        for watermark_sized_chunk in write_data.chunks(self.tx_watermark as usize) {
            // Wait for space in TX FIFO
            #[cfg(feature = "time")]
            {
                let start = Instant::now();
                while self.info.regs.intr().read().iptxwe().bit_is_clear() {
                    let timedout = is_expired(start, TX_FIFO_FREE_WATERMARK_TIMEOUT);
                    if timedout {
                        return Err(NorStorageBusError::StorageBusInternalError);
                    }
                }
            }
            #[cfg(not(feature = "time"))]
            {
                while self.info.regs.intr().read().iptxwe().bit_is_clear() {}
            }

            for (chunk, slot) in watermark_sized_chunk
                .chunks(FIFO_SLOT_SIZE as usize)
                .zip(0..num_tx_watermark_slot)
            {
                let mut temp = 0_u32;
                if chunk.len() < FIFO_SLOT_SIZE as usize {
                    // We cannot do copy from slice as it will cause a panic
                    for i in 0..chunk.len() as u32 {
                        temp |= (chunk[i as usize] as u32) << (i * 8);
                    }
                } else {
                    temp = u32::from_ne_bytes(
                        chunk
                            .try_into()
                            .map_err(|_| NorStorageBusError::StorageBusInternalError)?,
                    );
                }
                self.info.regs.tfdr(slot as usize).write(|w| unsafe {
                    //SAFETY: Operation is safe as we are programming the data to be sent to the flash
                    w.bits(temp)
                });
            }
            // Clear out the water mark level data
            self.info.regs.intr().modify(|_, w| w.iptxwe().clear_bit_by_one());
        }

        Ok(())
    }
}

impl FlexSpiConfigurationPort {
    /// Initialize FlexSPI
    pub fn configure_flexspi(&mut self, config: &FlexspiConfig) -> Result<(), ()> {
        let regs = self.info.regs;

        // Enable Clock and deassert Reset
        enable_and_reset::<peripherals::FLEXSPI>();

        let sysctl_reg = unsafe { &*crate::pac::Sysctl0::ptr() };
        sysctl_reg
            .pdruncfg1_clr()
            .write(|w| w.flexspi_sram_apd().clr_pdruncfg1().flexspi_sram_ppd().clr_pdruncfg1());

        // These register sequence needs to be updated sequentially. Hence we dont merge the calls
        regs.mcr0().modify(|_, w| w.swreset().set_bit());
        #[cfg(feature = "time")]
        {
            let start = Instant::now();
            while regs.mcr0().read().swreset().bit_is_set() {
                let timedout = is_expired(start, RESET_TIMEOUT);
                if timedout {
                    return Err(());
                }
            }
        }
        #[cfg(not(feature = "time"))]
        {
            while regs.mcr0().read().swreset().bit_is_set() {}
        }

        //• Set MCR0[MDIS] to 0x1 (Make sure self.flexspi_ref is configured in module stop mode)
        regs.mcr0().modify(|_, w| w.mdis().set_bit());

        //• Configure module control registers: MCR0, MCR1, MCR2. (Don't change MCR0[MDIS])
        regs.mcr0().modify(|_, w| {
            w.rxclksrc()
                .variant(config.rx_sample_clock)
                .dozeen()
                .variant(config.enable_doze)
                .sckfreerunen()
                .variant(config.enable_sck_free_running)
                .hsen()
                .variant(config.enable_half_speed_access)
        });

        regs.mcr1().modify(|_, w| unsafe {
            w.ahbbuswait()
                .bits(config.ahb_config.ahb_bus_timeout_cycle)
                .seqwait()
                .bits(config.seq_timeout_cycle)
        });

        regs.mcr2().modify(|_, w| unsafe {
            w.samedeviceen()
                .variant(config.enable_same_config_for_all)
                .resumewait()
                .bits(config.ahb_config.resume_wait_cycle)
                .sckbdiffopt()
                .variant(config.enable_sck_b_diff_opt)
                .clrahbbufopt()
                .variant(config.ahb_config.enable_clear_ahb_buffer_opt)
        });

        regs.ahbcr().modify(|_, w| {
            w.readaddropt()
                .variant(config.ahb_config.enable_read_address_opt)
                .bufferableen()
                .variant(config.ahb_config.enable_ahb_bufferable)
                .cachableen()
                .variant(config.ahb_config.enable_ahb_cachable)
        });

        regs.ahbcr()
            .modify(|_, w| w.prefetchen().variant(config.ahb_config.enable_ahb_prefetch));

        regs.ahbrxbuf0cr0().modify(|_, w| unsafe {
            w.mstrid()
                .bits(0)
                .prefetchen()
                .set_bit()
                .bufsz()
                .bits(256)
                .priority()
                .bits(0)
        });

        regs.ahbrxbuf1cr0().modify(|_, w| unsafe {
            w.mstrid()
                .bits(0)
                .prefetchen()
                .set_bit()
                .bufsz()
                .bits(256)
                .priority()
                .bits(0)
        });

        regs.ahbrxbuf2cr0().modify(|_, w| unsafe {
            w.mstrid()
                .bits(0)
                .prefetchen()
                .set_bit()
                .bufsz()
                .bits(256)
                .priority()
                .bits(0)
        });

        regs.ahbrxbuf3cr0().modify(|_, w| unsafe {
            w.mstrid()
                .bits(0)
                .prefetchen()
                .set_bit()
                .bufsz()
                .bits(256)
                .priority()
                .bits(0)
        });

        regs.ahbrxbuf4cr0().modify(|_, w| unsafe {
            w.mstrid()
                .bits(0)
                .prefetchen()
                .set_bit()
                .bufsz()
                .bits(256)
                .priority()
                .bits(0)
        });

        regs.ahbrxbuf5cr0().modify(|_, w| unsafe {
            w.mstrid()
                .bits(0)
                .prefetchen()
                .set_bit()
                .bufsz()
                .bits(256)
                .priority()
                .bits(0)
        });

        regs.ahbrxbuf6cr0().modify(|_, w| unsafe {
            w.mstrid()
                .bits(0)
                .prefetchen()
                .set_bit()
                .bufsz()
                .bits(256)
                .priority()
                .bits(0)
        });

        regs.ahbrxbuf7cr0().modify(|_, w| unsafe {
            w.mstrid()
                .bits(0)
                .prefetchen()
                .set_bit()
                .bufsz()
                .bits(256)
                .priority()
                .bits(0)
        });

        // • Initialize Flash control registers (FLSHxCR0,FLSHxCR1,FLSHxCR2)
        match (self.flash_port, self.device_instance) {
            (FlexSpiFlashPort::PortA, FlexSpiFlashPortDeviceInstance::DeviceInstance0) => {
                regs.flsha1cr0().modify(|_, w| unsafe { w.flshsz().bits(0) });
            }
            (FlexSpiFlashPort::PortA, FlexSpiFlashPortDeviceInstance::DeviceInstance1) => {
                regs.flsha2cr0().modify(|_, w| unsafe { w.flshsz().bits(0) });
            }
            (FlexSpiFlashPort::PortB, FlexSpiFlashPortDeviceInstance::DeviceInstance0) => {
                regs.flshb1cr0().modify(|_, w| unsafe { w.flshsz().bits(0) });
            }
            (FlexSpiFlashPort::PortB, FlexSpiFlashPortDeviceInstance::DeviceInstance1) => {
                regs.flshb2cr0().modify(|_, w| unsafe { w.flshsz().bits(0) });
            }
        }

        regs.iprxfcr().modify(|_, w| unsafe { w.rxwmrk().bits(0) });
        regs.iptxfcr().modify(|_, w| unsafe { w.txwmrk().bits(0) });

        Ok(())
    }

    /// Configure the flash self.flexspi_ref based on the external flash device
    pub fn configure_device_port(
        &self,
        device_config: &FlexspiDeviceConfig,
        flexspi_config: &FlexspiConfig,
    ) -> Result<(), ()> {
        let regs = self.info.regs;
        let inst = match self.device_instance {
            FlexSpiFlashPortDeviceInstance::DeviceInstance0 => 0,
            FlexSpiFlashPortDeviceInstance::DeviceInstance1 => 1,
        };

        #[cfg(feature = "time")]
        {
            let start = Instant::now();

            while !(regs.sts0().read().arbidle().bit_is_set() && regs.sts0().read().seqidle().bit_is_set()) {
                let timedout = is_expired(start, IDLE_TIMEOUT);
                if timedout {
                    return Err(());
                }
            }
        }
        #[cfg(not(feature = "time"))]
        {
            while !(regs.sts0().read().arbidle().bit_is_set() && regs.sts0().read().seqidle().bit_is_set()) {}
        }

        regs.dllcr(inst).modify(|_, w| {
            let is_unified_config;
            let mut dll_value;
            let temp;

            let rx_sample_clock = flexspi_config.rx_sample_clock;
            match rx_sample_clock {
                Rxclksrc::Rxclksrc0 => {
                    is_unified_config = true;
                }
                Rxclksrc::Rxclksrc1 => {
                    is_unified_config = true;
                }
                Rxclksrc::Rxclksrc3 => {
                    is_unified_config = device_config.is_sck2_enabled;
                }
            }
            w.ovrden().variant(is_unified_config);
            if device_config.flexspi_root_clk >= CLOCK_100MHZ {
                /* DLLEN = 1, SLVDLYTARGET = 0xF, */
                unsafe {
                    w.slvdlytarget().bits(0xF).dllen().set_bit();
                }
            } else {
                temp = (device_config.data_valid_time) as u32 * 1000; /* Convert data valid time in ns to ps. */
                dll_value = temp / DELAYCELLUNIT as u32;
                if dll_value * (DELAYCELLUNIT as u32) < temp {
                    dll_value += 1;
                }
                unsafe {
                    w.ovrdval().bits((dll_value) as u8);
                }
            }
            w
        });

        regs.flshcr4().modify(|_, w| match self.flash_port {
            FlexSpiFlashPort::PortA => w.wmena().variant(device_config.enable_write_mask_port_a),
            FlexSpiFlashPort::PortB => w.wmenb().variant(device_config.enable_write_mask_port_b),
        });

        match self.flash_port {
            FlexSpiFlashPort::PortA => self.configure_flexspi_device_port_a(device_config)?,
            FlexSpiFlashPort::PortB => self.configure_flexspi_device_port_b(device_config)?,
        }

        // Enable the module
        regs.mcr0().modify(|_, w| w.mdis().clear_bit());

        Ok(())
    }

    fn configure_flexspi_device_port_a(&self, device_config: &FlexspiDeviceConfig) -> Result<(), ()> {
        let regs = self.info.regs;
        let flash_size = device_config.flash_size_kb;

        match self.device_instance {
            FlexSpiFlashPortDeviceInstance::DeviceInstance0 => {
                configure_ports_a!(1, regs, device_config, flash_size);
            }

            FlexSpiFlashPortDeviceInstance::DeviceInstance1 => {
                configure_ports_a!(2, regs, device_config, flash_size);
            }
        }
        Ok(())
    }

    fn configure_flexspi_device_port_b(&self, device_config: &FlexspiDeviceConfig) -> Result<(), ()> {
        let regs = self.info.regs;
        let flash_size = device_config.flash_size_kb;

        match self.device_instance {
            FlexSpiFlashPortDeviceInstance::DeviceInstance0 => {
                configure_ports_b!(1, regs, device_config, flash_size);
            }
            FlexSpiFlashPortDeviceInstance::DeviceInstance1 => {
                configure_ports_b!(2, regs, device_config, flash_size);
            }
        }
        Ok(())
    }
}

impl<'d> FlexspiNorStorageBus<'d, Blocking> {
    /// Create a new FlexSPI instance in blocking mode with single configuration
    pub fn new_blocking_single_config<T: Instance>(
        _inst: Peri<'d, T>,
        data0: Peri<'d, impl FlexSpiPin>,
        data1: Peri<'d, impl FlexSpiPin>,
        clk: Peri<'d, impl FlexSpiPin>,
        cs: Peri<'d, impl FlexSpiPin>,
        config: FlexspiConfigPortData,
    ) -> Self {
        // Configure the pins
        data0.config_pin();
        data1.config_pin();
        clk.config_pin();
        cs.config_pin();

        Self {
            info: T::info(),
            _mode: core::marker::PhantomData,
            configport: FlexSpiConfigurationPort {
                info: T::info(),
                device_instance: config.dev_instance,
                flash_port: config.port,
            },
            rx_watermark: config.rx_watermark,
            tx_watermark: config.tx_watermark,
            phantom: core::marker::PhantomData,
        }
    }

    /// Create a new FlexSPI instance in blocking mode with Dual configuration
    pub fn new_blocking_dual_config<T: Instance>(
        _inst: Peri<'d, T>,
        data0: Peri<'d, impl FlexSpiPin>,
        data1: Peri<'d, impl FlexSpiPin>,
        clk: Peri<'d, impl FlexSpiPin>,
        cs: Peri<'d, impl FlexSpiPin>,
        config: FlexspiConfigPortData,
    ) -> Self {
        // Configure the pins
        data0.config_pin();
        data1.config_pin();
        clk.config_pin();
        cs.config_pin();
        Self {
            info: T::info(),
            _mode: core::marker::PhantomData,
            configport: FlexSpiConfigurationPort {
                info: T::info(),
                device_instance: config.dev_instance,
                flash_port: config.port,
            },
            rx_watermark: config.rx_watermark,
            tx_watermark: config.tx_watermark,
            phantom: core::marker::PhantomData,
        }
    }

    /// Create a new FlexSPI instance in blocking mode with Quad configuration
    pub fn new_blocking_quad_config<T: Instance>(
        _inst: Peri<'d, T>,
        data0: Peri<'d, impl FlexSpiPin>,
        data1: Peri<'d, impl FlexSpiPin>,
        data2: Peri<'d, impl FlexSpiPin>,
        data3: Peri<'d, impl FlexSpiPin>,
        clk: Peri<'d, impl FlexSpiPin>,
        cs: Peri<'d, impl FlexSpiPin>,
        config: FlexspiConfigPortData,
    ) -> Self {
        // Configure the pins
        data0.config_pin();
        data1.config_pin();
        data2.config_pin();
        data3.config_pin();
        clk.config_pin();
        cs.config_pin();
        Self {
            info: T::info(),
            _mode: core::marker::PhantomData,
            configport: FlexSpiConfigurationPort {
                info: T::info(),
                device_instance: config.dev_instance,
                flash_port: config.port,
            },
            rx_watermark: config.rx_watermark,
            tx_watermark: config.tx_watermark,
            phantom: core::marker::PhantomData,
        }
    }

    /// Create a new FlexSPI instance in blocking mode with octal configuration
    pub fn new_blocking_octal_config<T: Instance>(
        _inst: Peri<'d, T>,
        data0: Peri<'d, impl FlexSpiPin>,
        data1: Peri<'d, impl FlexSpiPin>,
        data2: Peri<'d, impl FlexSpiPin>,
        data3: Peri<'d, impl FlexSpiPin>,
        data4: Peri<'d, impl FlexSpiPin>,
        data5: Peri<'d, impl FlexSpiPin>,
        data6: Peri<'d, impl FlexSpiPin>,
        data7: Peri<'d, impl FlexSpiPin>,
        clk: Peri<'d, impl FlexSpiPin>,
        cs: Peri<'d, impl FlexSpiPin>,
        config: FlexspiConfigPortData,
    ) -> Self {
        // Configure the pins
        data0.config_pin();
        data1.config_pin();
        data2.config_pin();
        data3.config_pin();
        data4.config_pin();
        data5.config_pin();
        data6.config_pin();
        data7.config_pin();
        clk.config_pin();
        cs.config_pin();
        Self {
            info: T::info(),
            _mode: core::marker::PhantomData,
            configport: FlexSpiConfigurationPort {
                info: T::info(),
                device_instance: config.dev_instance,
                flash_port: config.port,
            },
            rx_watermark: config.rx_watermark,
            tx_watermark: config.tx_watermark,
            phantom: core::marker::PhantomData,
        }
    }

    /// Create a new FlexSPI instance in blocking mode without pin configuration
    pub fn new_blocking_no_pin_config<T: Instance>(_inst: Peri<'d, T>, config: FlexspiConfigPortData) -> Self {
        Self {
            info: T::info(),
            _mode: core::marker::PhantomData,
            configport: FlexSpiConfigurationPort {
                info: T::info(),
                device_instance: config.dev_instance,
                flash_port: config.port,
            },
            rx_watermark: config.rx_watermark,
            tx_watermark: config.tx_watermark,
            phantom: core::marker::PhantomData,
        }
    }
}

macro_rules! impl_pin {
    ($peri:ident, $fn: ident) => {
        impl FlexSpiPin for crate::peripherals::$peri {
            fn config_pin(&self) {
                self.set_function(crate::iopctl::Function::$fn)
                    .set_pull(crate::iopctl::Pull::None)
                    .set_slew_rate(crate::gpio::SlewRate::Slow)
                    .set_drive_strength(crate::gpio::DriveStrength::Normal)
                    .disable_analog_multiplex()
                    .set_drive_mode(crate::gpio::DriveMode::PushPull)
                    .set_input_inverter(crate::gpio::Inverter::Disabled);
            }
        }
    };
}

/// FlexSPI Data Pins
pub trait FlexSpiPin: Pin + sealed::Sealed + PeripheralType {
    /// Configure FlexSPI Data Pin
    fn config_pin(&self);
}

impl_pin!(PIO1_11, F6); // PortB-DATA0
impl_pin!(PIO1_12, F6); // PortB-DATA1
impl_pin!(PIO1_13, F6); // PortB-DATA2
impl_pin!(PIO1_14, F6); // PortB-DATA3
impl_pin!(PIO2_17, F6); // PortB-DATA4
impl_pin!(PIO2_18, F6); // PortB-DATA5
impl_pin!(PIO2_22, F6); // PortB-DATA6
impl_pin!(PIO2_23, F6); // PortB-DATA7
impl_pin!(PIO2_19, F6); // PortB-CS0
impl_pin!(PIO2_21, F6); // PortB-CS1
impl_pin!(PIO1_29, F5); // PortB-SCLK

impl_pin!(PIO1_19, F1); // PortA-CS0
impl_pin!(PIO1_18, F1); // PortA-SCLK
impl_pin!(PIO1_20, F1); // PortA-DATA0
impl_pin!(PIO1_21, F1); // PortA-DATA1
impl_pin!(PIO1_22, F1); // PortA-DATA2
impl_pin!(PIO1_23, F1); // PortA-DATA3
impl_pin!(PIO1_24, F1); // PortA-DATA4
impl_pin!(PIO1_25, F1); // PortA-DATA5
impl_pin!(PIO1_26, F1); // PortA-DATA6
impl_pin!(PIO1_27, F1); // PortA-DATA7
