use cortex_m::asm;
use embassy_hal_internal::Peripheral;
use embedded_storage::nor_flash::{
    ErrorType, NorFlash as BlockingNorFlash, NorFlashError, NorFlashErrorKind, ReadNorFlash as BlockingReadNorFlash,
};
use mimxrt600_fcb::flexspi_lut_seq;
use mimxrt600_fcb::FlexSpiLutOpcode::*;
use mimxrt600_fcb::FlexSpiNumPads::*;

use crate::clocks::enable_and_reset;
// use crate::flexspi::errors::FlashError;
use crate::interrupt;
use crate::iopctl::IopctlPin as Pin;
use crate::peripherals;
use crate::storage::{StorageCmdPort, StorageDataPort};

#[repr(C)]
#[allow(non_snake_case)]
struct FlexSpi {
    MCR0: u32,
    /**< Module Control Register 0, offset: 0x0 */
    MCR1: u32,
    /**< Module Control Register 1, offset: 0x4 */
    MCR2: u32,
    /**< Module Control Register 2, offset: 0x8 */
    AHBCR: u32,
    /**< AHB Bus Control Register, offset: 0xC */
    INTEN: u32,
    /**< Interrupt Enable Register, offset: 0x10 */
    INTR: u32,
    /**< Interrupt Register, offset: 0x14 */
    LUTKEY: u32,
    /**< LUT Key Register, offset: 0x18 */
    LUTCR: u32,
    /**< LUT Control Register, offset: 0x1C */
    AHBRXBUFCR0: [u32; 8],
    /**< AHB RX Buffer 0 Control Register 0..AHB RX Buffer 7 Control Register 0, array offset: 0x20, array step: 0x4 */
    RESERVED_0: [u8; 32],
    FLSHCR0: [u32; 4],
    /**< Flash Control Register 0, array offset: 0x60, array step: 0x4 */
    FLSHCR1: [u32; 4],
    /**< Flash Control Register 1, array offset: 0x70, array step: 0x4 */
    FLSHCR2: [u32; 4],
    /**< Flash Control Register 2, array offset: 0x80, array step: 0x4 */
    RESERVED_1: [u8; 4],
    FLSHCR4: u32,
    /**< Flash Control Register 4, offset: 0x94 */
    RESERVED_2: [u8; 8],
    pub IPCR0: u32,
    /**< IP Control Register 0, offset: 0xA0 */
    IPCR1: u32,
    /**< IP Control Register 1, offset: 0xA4 */
    RESERVED_3: [u8; 8],
    IPCMD: u32,
    /**< IP Command Register, offset: 0xB0 */
    DLPR: u32,
    /**< Data Learn Pattern Register, offset: 0xB4 */
    IPRXFCR: u32,
    /**< IP RX FIFO Control Register, offset: 0xB8 */
    IPTXFCR: u32,
    /**< IP TX FIFO Control Register, offset: 0xBC */
    DLLCR: [u32; 2],
    /**< DLL Control Register 0, array offset: 0xC0, array step: 0x4 */
    RESERVED_4: [u8; 24],
    STS0: u32,
    /**< Status Register 0, offset: 0xE0 */
    STS1: u32,
    /**< Status Register 1, offset: 0xE4 */
    STS2: u32,
    /**< Status Register 2, offset: 0xE8 */
    AHBSPNDSTS: u32,
    /**< AHB Suspend Status Register, offset: 0xEC */
    IPRXFSTS: u32,
    /**< IP RX FIFO Status Register, offset: 0xF0 */
    IPTXFSTS: u32,
    /**< IP TX FIFO Status Register, offset: 0xF4 */
    RESERVED_5: [u8; 8],
    RFDR: [u32; 32],
    /**< IP RX FIFO Data Register 0..IP RX FIFO Data Register 31, array offset: 0x100, array step: 0x4 */
    TFDR: [u32; 32],
    /**< IP TX FIFO Data Register 0..IP TX FIFO Data Register 31, array offset: 0x180, array step: 0x4 */
    LUT: [u32; 120],
}

const LUT_NUM_REG_PER_SEQ: usize = 4;

impl From<FlexSpiCmd> for usize {
    fn from(cmd: FlexSpiCmd) -> usize {
        match cmd {
            FlexSpiCmd::ReadId => 1,
            FlexSpiCmd::WriteEnable => 3,
            FlexSpiCmd::ReadStatusRegister => 4,
            FlexSpiCmd::EraseSector => 6,
            FlexSpiCmd::PageProgram => 12,
        }
    }
}

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
    CsIntervalUnit1Cycle,
    /// CS interval unit is 256 cycle
    CsIntervalUnit256Cycle,
}
#[derive(Clone, Copy, Debug)]
/// FlexSPI AHB Write Wait unit Enum.
pub enum FlexspiAhbWriteWaitUnit {
    /// AWRWAIT unit is 2 ahb clock cycle
    FlexspiAhbWriteWaitUnit2ahbCycle,
    /// AWRWAIT unit is 8 ahb clock cycle.
    FlexspiAhbWriteWaitUnit8ahbCycle,
    /// AWRWAIT unit is 32 ahb clock cycle.
    FlexspiAhbWriteWaitUnit32ahbCycle,
    /// AWRWAIT unit is 128 ahb clock cycle.   
    FlexspiAhbWriteWaitUnit128ahbCycle,
    /// AWRWAIT unit is 512 ahb clock cycle.   
    FlexspiAhbWriteWaitUnit512ahbCycle,
    /// AWRWAIT unit is 2048 ahb clock cycle.  
    FlexspiAhbWriteWaitUnit2048ahbCycle,
    /// AWRWAIT unit is 8192 ahb clock cycle.  
    FlexspiAhbWriteWaitUnit8192ahbCycle,
    /// AWRWAIT unit is 32768 ahb clock cycle.
    FlexspiAhbWriteWaitUnit32768ahbCycle,
}

#[derive(Clone, Copy, Debug)]
/// FlexSPI Read Sample Clock Enum.
pub enum FlexspiReadSampleClock {
    /// Dummy Read strobe generated by FlexSPI self.flexspi_ref and loopback internally
    FlexspiReadSampleClkLoopbackInternally,
    /// Dummy Read strobe generated by FlexSPI self.flexspi_ref and loopback from DQS pad
    FlexspiReadSampleClkLoopbackFromDqsPad,
    /// SCK output clock and loopback from SCK pad
    FlexspiReadSampleClkLoopbackFromSckPad,
    /// Flash provided Read strobe and input from DQS pad
    FlexspiReadSampleClkExternalInputFromDqsPad,
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
    /// AHB Read Prefetch Enable for current AHB RX Buffer corresponding Master, allows to prefetch data for AHB read access.
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
    pub cs_interval_unit: FlexspiCsIntervalCycleUnit,
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
    pub ahb_write_wait_unit: FlexspiAhbWriteWaitUnit,
    /// AHB write wait interval, multiply AHB write interval unit to get the AHB write wait cycles
    pub ahb_write_wait_interval: u16,
    /// Enable/Disable FLEXSPI drive DQS pin as write mask
    pub enable_write_mask: bool,
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
    /// Wait cycle for idle state before suspended command sequence resume, timeout after ahbBusTimeoutCycle AHB clock cycles.
    pub resume_wait_cycle: u8,
    /// AHB buffer size.
    pub buffer: [FlexspiAhbBufferConfig; 8],
    /// Enable/disable automatically clean AHB RX Buffer and TX Buffer when FLEXSPI returns STOP mode ACK.
    pub enable_clear_ahb_buffer_opt: bool,
    /// Enable/disable remove AHB read burst start address alignment limitation. when enable, there is no AHB read burst start address alignment limitation.
    pub enable_read_address_opt: bool,
    /// Enable/disable AHB read prefetch feature, when enabled, FLEXSPI will fetch more data than current AHB burst.
    pub enable_ahb_prefetch: bool,
    /// Enable/disable AHB bufferable write access support, when enabled, FLEXSPI return before waiting for command execution finished.
    pub enable_ahb_bufferable: bool,
    /// Enable AHB bus cachable read access support.
    pub enable_ahb_cachable: bool,
}

#[derive(Clone, Copy, Debug)]
/// FlexSPI configuration structure
pub struct FlexspiConfig {
    /// Sample Clock source selection for Flash Reading.
    pub rx_sample_clock: FlexspiReadSampleClock,
    /// Enable/disable SCK output free-running.
    pub enable_sck_free_running: bool,
    /// Enable/disable combining PORT A and B Data Pins (SIOA[3:0] and SIOB[3:0]) to support Flash Octal mode.
    pub enable_combination: bool,
    /// Enable/disable doze mode support.
    pub enable_doze: bool,
    /// Enable/disable divide by 2 of the clock for half speed commands.
    pub enable_half_speed_access: bool,
    /// Enable/disable SCKB pad use as SCKA differential clock output, when enable, Port B flash access is not available.
    pub enable_sck_b_diff_opt: bool,
    /// Enable/disable same configuration for all connected devices when enabled, same configuration in FLASHA1CRx is applied to all.
    pub enable_same_config_for_all: bool,
    /// Timeout wait cycle for command sequence execution, timeout after ahbGrantTimeoutCyle*1024 serial root clock cycles.
    pub seq_timeout_cycle: u16,
    /// Timeout wait cycle for IP command grant, timeout after ipGrantTimeoutCycle*1024 AHB clock cycles.
    pub ip_grant_timeout_cycle: u8,
    /// FLEXSPI IP transmit watermark value.
    pub tx_watermark: u8,
    /// FLEXSPI receive watermark value.
    pub rx_watermark: u8,
    /// AHB configuration
    pub ahb_config: AhbConfig,
}

/// FlexSPI LUT Sequence Enum.
/// This enum is used by FlexSPI HAL consumers to define the LUT sequence for FlexSPI.
pub struct FlexSpiLutSeq {
    /// Fast Read Sequence
    pub fast_read: [u32; 4],
    /// Page Program Sequence
    pub page_program: [u32; 4],
    /// Sector Erase Sequence
    pub sector_erase: [u32; 4],
    /// Write Enable Sequence
    pub write_enable: [u32; 4],
    /// Write Disable Sequence
    pub write_disable: [u32; 4],
    /// Deep Power Down Sequence
    pub read_id: [u32; 4],
    /// Power Up Sequence from deep power down
    pub fast_read_custom: [u32; 4],
    /// Reset Enable Sequence
    pub reset_enable: [u32; 4],
    /// Reset Memory Sequence
    pub reset_memory: [u32; 4],
    /// Read JEDEC ID Sequence
    pub read_jedec_id: [u32; 4],
    /// Read Status/Config Register Sequence
    pub read_status_cfg_reg1: [u32; 4],
    /// Write Status/Config Register Sequence
    pub write_status_cfg_reg1: [u32; 4],
    /// Read Status/Config Register Sequence
    pub read_status_cfg_reg2: [u32; 4],
    /// Write Status/Config Register Sequence
    pub write_status_cfg_reg2: [u32; 4],
    /// Read Status/Config Register Sequence
    pub read_status_cfg_reg3: [u32; 4],
    /// Write Status/Config Register Sequence
    pub write_status_cfg_reg3: [u32; 4],
}

enum FlexSpiCmd {
    WriteEnable,
    ReadStatusRegister,
    EraseSector,
    ReadId,
    PageProgram,
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
pub trait Instance: SealedInstance + Peripheral<P = Self> + 'static + Send {
    /// Interrupt for this SPI instance.
    type Interrupt: interrupt::typelevel::Interrupt;
}

impl SealedInstance for crate::peripherals::FLEXSPI {
    fn info() -> Info {
        Info {
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

/// Driver execution location mode
pub trait Execution: sealed::Sealed {}

/// Blocking mode.
pub struct Blocking;
impl Mode for Blocking {}

/// Async mode.
pub struct Async;
impl Mode for Async {}

/// XIP execution mode.
pub struct Xip;
impl Execution for Xip {}

/// Ram execution mode.
pub struct Ram;
impl Execution for Ram {}

/// FlexSPI write policy
pub struct WritePolicy;

impl WritePolicy {
    /// Apply write policy
    pub fn action() {
        // Set write policy
    }
}

/// FlexSPI Read Policy
pub struct ReadPolicy;

impl ReadPolicy {
    /// Apply read policy
    pub fn action() {
        // Set read policy
    }
}

/// Nor flash error object
#[derive(Debug)]
pub struct FlashStorageErrorOther;
impl<M: Mode, E: Execution> ErrorType for FlexspiStorage<M, E> {
    type Error = FlashStorageErrorOther;
}

impl NorFlashError for FlashStorageErrorOther {
    fn kind(&self) -> embedded_storage::nor_flash::NorFlashErrorKind {
        NorFlashErrorKind::Other
    }
}

#[allow(private_interfaces)]
/// FlexSPI Configuration Manager Port
pub struct FlexSpiConfigurationPort<E: Execution> {
    /// Bus Width
    bus_width: FlexSpiBusWidth,
    /// Flash Port
    flash_port: FlexSpiFlashPort,
    /// Device Instance
    device_instance: FlexSpiFlashPortDeviceInstance,
    /// FlexSPI HW Info Object
    info: Info,
    /// Mode Phantom object
    _execution: core::marker::PhantomData<E>,
}

/// FlexSPI instance
pub struct FlexspiStorage<M: Mode, E: Execution> {
    /// FlexSPI HW Info Object
    info: Info,
    /// Write policy object
    write_policy: WritePolicy,
    /// Read policy object
    read_policy: ReadPolicy,
    /// RX FIFO watermark level
    rx_watermark: u8,
    /// TX FIFO Watermark Level
    tx_watermark: u8,
    /// Mode Phantom object
    _mode: core::marker::PhantomData<(M, E)>,
    /// FlexSPI peripheral instance
    flexspi_ref: &'static mut FlexSpi,
    /// Flash Port
    flash_port: FlexSpiFlashPort,
    /// Device Instance
    device_instance: FlexSpiFlashPortDeviceInstance,
    /// FlexSPI Configuration Port
    pub configport: Option<FlexSpiConfigurationPort<E>>,
}

impl crate::storage::StorageDriver<Blocking> for FlexspiStorage<Blocking, Xip> {}

#[derive(Debug, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[allow(non_snake_case)]
/// FlexSPI self.flexspi_ref specific errors
/// This enum provides verbose error messages for FlexSPI self.flexspi_ref specific errors
pub enum FlexSpiError {
    /// Flash command grant error
    CmdGrantErr {
        /// AHB read command error
        AhbReadCmdErr: bool,
        /// AHB write command error
        AhbWriteCmdErr: bool,
        /// IP command error
        IpCmdErr: bool,
    }, // INTR[AHBCMDGE] = 1 / INTR[IPCMDGE] = 1
    /// Flash command check error
    CmdCheckErr {
        /// AHB read command error
        AhbReadCmdErr: bool,
        /// AHB write command error
        AhbWriteCmdErr: bool,
        /// IP command error
        IpCmdErr: bool,
    }, // INTR[AHBCMDERR] = 1/ INTR[IPCMDERR] = 1
    /// Flash command execution error
    CmdExecErr {
        /// AHB read command error
        AhbReadCmdErr: bool,
        /// AHB write command error
        AhbWriteCmdErr: bool,
        /// IP command error
        IpCmdErr: bool,
    }, // INTR[AHBCMDERR] = 1/ INTR[SEQTIMEOUT] = 1/ INTR[IPCMDERR] = 1
    /// AHB bus timeout error
    AhbBusTimeout {
        /// AHB read command error
        AhbReadCmdErr: bool, // INTR[AHBBUSTIMEO UT] = 1
        /// AHB write command error
        AhbWriteCmdErr: bool, // INTR[AHBBUSTIMEO UT] = 1
    },
    /// Data learning failed
    DataLearningFailed, // INTR[DATALEARNFAIL] = 1
}

impl FlexSpiError {
    /// Get the description of the error
    pub fn describe(&self) -> &str {
        match self {
            FlexSpiError::CmdGrantErr {
                AhbReadCmdErr,
                AhbWriteCmdErr,
                IpCmdErr,
            } => {
                if *AhbReadCmdErr {
                    "AHB bus error response for Read Command. Command grant timeout"
                } else if *AhbWriteCmdErr {
                    "AHB bus error response for Write Command. Command grant timeout"
                } else if *IpCmdErr {
                    "IP command grant timeout. Command grant timeout"
                } else {
                    "Unknown Flash command grant error"
                }
            }
            FlexSpiError::CmdCheckErr {
                AhbReadCmdErr,
                AhbWriteCmdErr,
                IpCmdErr,
            } => {
                if *AhbWriteCmdErr {
                    "Command is not executed when error detected in command check. Following are the possible reasons:
                    - AHB write command with JMP_ON_CS instruction used in the sequence
                    - There is unknown instruction opcode in the sequence.
                    - Instruction DUMMY_SDR/DUMMY_RWDS_SDR used in DDR sequence.
                    - Instruction DUMMY_DDR/DUMMY_RWDS_DDR used in SDR sequence."
                } else if *AhbReadCmdErr {
                    "Command is not executed when error detected in command check. Following are the possible reasons:
                    - There is unknown instruction opcode in the sequence
                    - Instruction DUMMY_SDR/DUMMY_RWDS_SDR used in DDR sequence.
                    - Instruction DUMMY_DDR/DUMMY_RWDS_DDR used in SDR sequence."
                } else if *IpCmdErr {
                    "Command is not executed when error detected in command check. Following are the possible reasons:
                    - IP command with JMP_ON_CS instruction used in the sequence
                    - There is unknown instruction opcode in the sequence.
                    - Instruction DUMMY_SDR/DUMMY_RWDS_SDRused in DDR sequence
                    - Instruction DUMMY_DDR/DUMMY_RWDS_DDR used in SDR sequence
                    - Flash boundary across"
                } else {
                    "Unknown Flash command check error"
                }
            }
            FlexSpiError::CmdExecErr {
                AhbReadCmdErr,
                AhbWriteCmdErr,
                IpCmdErr,
            } => {
                if *AhbWriteCmdErr {
                    "There will be AHB bus error response except the following cases: 
                        - AHB write command is triggered by flush (INCR burst ended with AHB_TX_BUF not empty)
                        - AHB bufferable write access and bufferable enabled (AHBCR[BUFFERABLEEN]=0x1)
                    Following are possible reasons for this error - 
                        - Command timeout during execution"
                } else if *AhbReadCmdErr {
                    "There will be AHB bus error response. Following are possible reasons for this error - 
                        - Command timeout during execution"
                } else if *IpCmdErr {
                    "Following are possible reasons for this error - 
                        - Command timeout during execution"
                } else {
                    "Unknown Flash command execution error"
                }
            }
            FlexSpiError::AhbBusTimeout {
                AhbReadCmdErr,
                AhbWriteCmdErr,
            } => {
                if *AhbReadCmdErr || *AhbWriteCmdErr {
                    "There will be AHB bus error response. Following are possible reasons for this error - 
                        - AHB bus timeout (no bus ready return)"
                } else {
                    "Unknown AHB bus timeout error"
                }
            }
            FlexSpiError::DataLearningFailed => "Data learning failed",
        }
    }
}

impl BlockingReadNorFlash for FlexspiStorage<Blocking, Xip> {
    const READ_SIZE: usize = 1;
    #[no_mangle]
    #[link_section = ".flexspi_code"]
    fn read(&mut self, offset: u32, bytes: &mut [u8]) -> Result<(), Self::Error> {
        let offset = 0x08000000 + offset;
        let ptr = offset as *const u8;
        unsafe {
            let data = *ptr;
            bytes[0] = data;
        }
        Ok(())
    }
    fn capacity(&self) -> usize {
        match self.flash_port {
            FlexSpiFlashPort::PortA => match self.device_instance {
                FlexSpiFlashPortDeviceInstance::DeviceInstance0 => {
                    self.info.regs.flsha1cr0().read().flshsz().bits() as usize
                }
                FlexSpiFlashPortDeviceInstance::DeviceInstance1 => {
                    self.info.regs.flsha2cr0().read().flshsz().bits() as usize
                }
            },
            FlexSpiFlashPort::PortB => match self.device_instance {
                FlexSpiFlashPortDeviceInstance::DeviceInstance0 => {
                    self.info.regs.flshb1cr0().read().flshsz().bits() as usize
                }
                FlexSpiFlashPortDeviceInstance::DeviceInstance1 => {
                    self.info.regs.flshb2cr0().read().flshsz().bits() as usize
                }
            },
        }
    }
}

impl FlexspiStorage<Blocking, Xip> {
    #[no_mangle]
    #[link_section = ".flexspi_code"]
    fn setup_write_transfer(&mut self) {
        self.flexspi_ref.LUTKEY = 0x5AF05AF0;
        self.flexspi_ref.LUTCR = 0x00000001;

        let cmd_idx: usize = FlexSpiCmd::PageProgram.into();
        self.flexspi_ref.FLSHCR2[2] &= !(0x1f << 8);
        self.flexspi_ref.FLSHCR2[2] |= (cmd_idx as u32) << 8;

        self.flexspi_ref.LUT[cmd_idx * LUT_NUM_REG_PER_SEQ] =
            flexspi_lut_seq(CMD_DDR, Octal, 0x12, CMD_DDR, Octal, 0xED);
        self.flexspi_ref.LUT[cmd_idx * LUT_NUM_REG_PER_SEQ + 1] =
            flexspi_lut_seq(RADDR_DDR, Octal, 0x20, WRITE_DDR, Octal, 0x04);
        self.flexspi_ref.LUT[cmd_idx * LUT_NUM_REG_PER_SEQ + 2] = 0;
        self.flexspi_ref.LUT[cmd_idx * LUT_NUM_REG_PER_SEQ + 3] = 0;
    }
}

impl BlockingNorFlash for FlexspiStorage<Blocking, Xip> {
    const WRITE_SIZE: usize = 1;
    const ERASE_SIZE: usize = 4096;

    fn erase(&mut self, from: u32, to: u32) -> Result<(), Self::Error> {
        panic!("Erase operation is not implemented for Data Port. Please use Command Port for erase operation");
    }

    #[no_mangle]
    #[link_section = ".flexspi_code"]
    fn write(&mut self, offset: u32, bytes: &[u8]) -> Result<(), Self::Error> {
        let addr = 0x08000000 + offset;
        let ptr = addr as *mut u8;
        self.setup_write_transfer();
        unsafe {
            *ptr = bytes[0];
        }

        Ok(())
    }
}

impl FlexspiStorage<Blocking, Xip> {
    #[no_mangle]
    #[link_section = ".flexspi_code"]
    fn setup_ip_transfer(&mut self, cmd: FlexSpiCmd, addr: Option<u32>, data: Option<u32>, size: Option<u32>) {
        match addr {
            Some(addr) => {
                self.flexspi_ref.IPCR0 = addr;
            }

            None => {
                self.flexspi_ref.IPCR0 = 0;
            }
        }
        // Clear the sequence ID
        self.flexspi_ref.IPCR1 &= !(0x1F << 16);

        // Unlock the LUT
        self.flexspi_ref.LUTKEY = 0x5AF05AF0;
        self.flexspi_ref.LUTCR = 0x2;

        // Reset the sequence pointer
        self.flexspi_ref.FLSHCR2[0] |= 0x1 << 31;
        self.flexspi_ref.FLSHCR2[1] |= 0x1 << 31;
        self.flexspi_ref.FLSHCR2[2] |= 0x1 << 31;
        self.flexspi_ref.FLSHCR2[3] |= 0x1 << 31;

        match cmd {
            FlexSpiCmd::ReadId => {
                let cmd_idx: usize = cmd.into();
                self.flexspi_ref.IPCR1 |= (cmd_idx as u32) << 16;
                self.flexspi_ref.LUT[LUT_NUM_REG_PER_SEQ * cmd_idx] =
                    flexspi_lut_seq(CMD_SDR, Single, 0x9F, READ_SDR, Single, 0x4);
                self.flexspi_ref.LUT[LUT_NUM_REG_PER_SEQ * cmd_idx + 1] = 0;
                self.flexspi_ref.LUT[LUT_NUM_REG_PER_SEQ * cmd_idx + 2] = 0;
                self.flexspi_ref.LUT[LUT_NUM_REG_PER_SEQ * cmd_idx + 3] = 0;
            }
            FlexSpiCmd::WriteEnable => {
                let cmd_idx: usize = cmd.into();
                self.flexspi_ref.IPCR1 |= (cmd_idx as u32) << 16;
                self.flexspi_ref.LUT[LUT_NUM_REG_PER_SEQ * cmd_idx] =
                    flexspi_lut_seq(CMD_DDR, Octal, 0x06, CMD_DDR, Octal, 0xF9);
                self.flexspi_ref.LUT[LUT_NUM_REG_PER_SEQ * cmd_idx + 1] = 0;
                self.flexspi_ref.LUT[LUT_NUM_REG_PER_SEQ * cmd_idx + 2] = 0;
                self.flexspi_ref.LUT[LUT_NUM_REG_PER_SEQ * cmd_idx + 3] = 0;
            }
            FlexSpiCmd::ReadStatusRegister => {
                let cmd_idx: usize = cmd.into();
                self.flexspi_ref.IPCR1 |= (cmd_idx as u32) << 16;
                self.flexspi_ref.LUT[LUT_NUM_REG_PER_SEQ * cmd_idx] =
                    flexspi_lut_seq(CMD_DDR, Octal, 0x05, CMD_DDR, Octal, 0xFA);
                self.flexspi_ref.LUT[LUT_NUM_REG_PER_SEQ * cmd_idx + 1] =
                    flexspi_lut_seq(RADDR_DDR, Octal, 0x20, DUMMY_DDR, Octal, 0x18);
                self.flexspi_ref.LUT[LUT_NUM_REG_PER_SEQ * cmd_idx + 2] =
                    flexspi_lut_seq(READ_DDR, Octal, 0x1, STOP, Single, 0x0);
                self.flexspi_ref.LUT[LUT_NUM_REG_PER_SEQ * cmd_idx + 3] = 0;
            }
            FlexSpiCmd::EraseSector => {
                let cmd_idx: usize = cmd.into();
                self.flexspi_ref.IPCR1 |= (cmd_idx as u32) << 16;
                self.flexspi_ref.LUT[LUT_NUM_REG_PER_SEQ * cmd_idx] =
                    flexspi_lut_seq(CMD_DDR, Octal, 0x21, CMD_DDR, Octal, 0xDE);
                self.flexspi_ref.LUT[LUT_NUM_REG_PER_SEQ * cmd_idx + 1] =
                    flexspi_lut_seq(RADDR_DDR, Octal, 0x20, STOP, Single, 0x0);
                self.flexspi_ref.LUT[LUT_NUM_REG_PER_SEQ * cmd_idx + 2] = 0;
                self.flexspi_ref.LUT[LUT_NUM_REG_PER_SEQ * cmd_idx + 3] = 0;
            }
            _ => {}
        }

        // Disable DMA for TX and RX
        self.flexspi_ref.IPRXFCR &= !0x2;
        self.flexspi_ref.IPTXFCR &= !0x2;

        // set watermark
        //self.flexspi_ref.IPRXFCR &= !(0x3F << 2);
        //self.flexspi_ref.IPRXFCR != (((0x8 / 8) - 1) << 2); // 8 bytes watermark

        // Reset RX and TX FIFO
        self.flexspi_ref.IPRXFCR |= 0x1;
        self.flexspi_ref.IPTXFCR |= 0x1;
    }

    #[no_mangle]
    #[link_section = ".flexspi_code"]
    fn execute_cmd(&mut self) {
        self.flexspi_ref.IPCMD |= 0x1;
    }

    #[no_mangle]
    #[link_section = ".flexspi_code"]
    fn wait_for_cmd_completion(&mut self) {
        #[allow(clippy::while_immutable_condition)]
        while (self.flexspi_ref.INTR & 0x1 == 0) {}
    }

    #[no_mangle]
    #[link_section = ".flexspi_code"]
    fn read_cmd_data(&mut self, size: u32, read_data: Option<&mut [u8]>) {
        loop {
            //info!("Waiting for filled data = {:02X}", controller.IPRXFSTS & 0xFF);
            if ((self.flexspi_ref.IPRXFSTS & 0xFF) * 8) < size {
                continue;
            }
            break;
        }

        read_data.unwrap()[0] = self.flexspi_ref.RFDR[0] as u8;
    }
    #[no_mangle]
    #[link_section = ".flexspi_code"]
    /// Wait for Flash operation completion
    pub fn wait_for_operation_completion(&mut self) {
        loop {
            // Read Status Register
            let status = self.read_status_register();
            // check if WIP is set or cleared
            if status[0] & 0x1 == 0x0 {
                break;
            }
        }
    }

    #[no_mangle]
    #[link_section = ".flexspi_code"]
    /// Erase flash sector
    pub fn erase_sector(&mut self, addr: u32) {
        // Erase sector
        self.setup_ip_transfer(FlexSpiCmd::EraseSector, Some(addr), None, None);
        self.execute_cmd();
        self.wait_for_cmd_completion();
        self.wait_for_operation_completion();
    }
    #[no_mangle]
    #[link_section = ".flexspi_code"]
    /// Write enable for flash
    pub fn write_enable(&mut self) {
        // Write enable
        self.setup_ip_transfer(FlexSpiCmd::WriteEnable, None, None, None);
        self.execute_cmd();
        self.wait_for_cmd_completion();
    }
    #[no_mangle]
    #[link_section = ".flexspi_code"]
    /// Read flash status register
    pub fn read_status_register(&mut self) -> [u8; 1] {
        // Read status register;
        let mut data = [0x55; 1];

        self.setup_ip_transfer(FlexSpiCmd::ReadStatusRegister, None, None, None);
        self.execute_cmd();
        self.wait_for_cmd_completion();
        self.read_cmd_data(1, Some(&mut data));
        data
    }
}

// ================================================================================//

/// FlexSPI self.flexspi_ref init API for clocking and Reset
pub fn init() {
    let sysctl_reg = unsafe { &*crate::pac::Sysctl0::ptr() };
    sysctl_reg
        .pdruncfg1_clr()
        .write(|w| w.flexspi_sram_apd().set_bit().flexspi_sram_ppd().set_bit());
}

impl FlexSpiConfigurationPort<Xip> {
    // Nothing to do as BootROM would have initialized everything
}
impl FlexSpiConfigurationPort<Ram> {
    /// Initialize FlexSPI
    pub fn configure_flexspi(&mut self, config: FlexspiConfig) {
        let regs = self.info.regs;

        // Enable Clock and deassert Reset
        enable_and_reset::<peripherals::FLEXSPI>();

        let sysctl_reg = unsafe { &*crate::pac::Sysctl0::ptr() };
        sysctl_reg
            .pdruncfg1_clr()
            .write(|w| w.flexspi_sram_apd().set_bit().flexspi_sram_ppd().set_bit());

        regs.mcr0().modify(|_, w| w.mdis().clear_bit());
        regs.mcr0().modify(|_, w| w.swreset().set_bit());
        while regs.mcr0().read().swreset().bit_is_set() {}

        //• Set MCR0[MDIS] to 0x1 (Make sure self.flexspi_ref is configured in module stop mode)
        regs.mcr0().modify(|_, w| w.mdis().set_bit());

        //• Configure module control registers: MCR0, MCR1, MCR2. (Don't change MCR0[MDIS])
        match config.rx_sample_clock {
            FlexspiReadSampleClock::FlexspiReadSampleClkLoopbackInternally => {
                regs.mcr0().modify(|_, w| w.rxclksrc().rxclksrc_0());
            }
            FlexspiReadSampleClock::FlexspiReadSampleClkLoopbackFromDqsPad => {
                regs.mcr0().modify(|_, w| w.rxclksrc().rxclksrc_1());
            }
            FlexspiReadSampleClock::FlexspiReadSampleClkLoopbackFromSckPad => {
                regs.mcr0().modify(|_, w| w.rxclksrc().rxclksrc_3());
            }
            FlexspiReadSampleClock::FlexspiReadSampleClkExternalInputFromDqsPad => {
                regs.mcr0().modify(|_, w| w.rxclksrc().rxclksrc_3());
            }
        }
        if config.enable_doze {
            regs.mcr0().modify(|_, w| w.dozeen().set_bit());
        } else {
            regs.mcr0().modify(|_, w| w.dozeen().clear_bit());
        }
        //==============================================================================================
        // These are only for debug purpose. So commenting out for now
        // regs.mcr0()
        //     .modify(|_, w| unsafe { w.ipgrantwait().bits(config.ip_grant_timeout_cycle) });

        // regs.mcr0()
        //     .write(|w| unsafe { w.ahbgrantwait().bits(config.ahb_config.ahb_grant_timeout_cycle) });
        //==============================================================================================

        if config.enable_sck_free_running {
            regs.mcr0().modify(|_, w| w.sckfreerunen().set_bit());
        } else {
            regs.mcr0().modify(|_, w| w.sckfreerunen().clear_bit());
        }

        if config.enable_half_speed_access {
            regs.mcr0().modify(|_, w| w.hsen().set_bit());
        } else {
            regs.mcr0().modify(|_, w| w.hsen().clear_bit());
        }

        regs.mcr1().modify(|_, w| unsafe {
            w.ahbbuswait()
                .bits(config.ahb_config.ahb_bus_timeout_cycle)
                .seqwait()
                .bits(config.seq_timeout_cycle)
        });

        if config.enable_same_config_for_all {
            regs.mcr2().modify(|_, w| w.samedeviceen().set_bit());
        } else {
            regs.mcr2().modify(|_, w| w.samedeviceen().clear_bit());
        }

        regs.mcr2()
            .modify(|_, w| unsafe { w.resumewait().bits(config.ahb_config.resume_wait_cycle) });

        if config.enable_sck_b_diff_opt {
            regs.mcr2().write(|w| w.sckbdiffopt().set_bit());
        } else {
            regs.mcr2().write(|w| w.sckbdiffopt().clear_bit());
        }

        if config.ahb_config.enable_clear_ahb_buffer_opt {
            regs.mcr2().modify(|_, w| w.clrahbbufopt().set_bit());
        } else {
            regs.mcr2().modify(|_, w| w.clrahbbufopt().clear_bit());
        }

        if config.ahb_config.enable_read_address_opt {
            regs.ahbcr().modify(|_, w| w.readaddropt().set_bit());
        } else {
            regs.ahbcr().modify(|_, w| w.readaddropt().clear_bit());
        }

        if config.ahb_config.enable_ahb_prefetch {
            regs.ahbcr().modify(|_, w| w.prefetchen().set_bit());
        } else {
            regs.ahbcr().modify(|_, w| w.prefetchen().clear_bit());
        }

        if config.ahb_config.enable_ahb_bufferable {
            regs.ahbcr().modify(|_, w| w.bufferableen().set_bit());
        } else {
            regs.ahbcr().modify(|_, w| w.bufferableen().clear_bit());
        }

        if config.ahb_config.enable_ahb_cachable {
            regs.ahbcr().modify(|_, w| w.cachableen().set_bit());
        } else {
            regs.ahbcr().modify(|_, w| w.cachableen().clear_bit());
        }

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
        match self.flash_port {
            FlexSpiFlashPort::PortA => match self.device_instance {
                FlexSpiFlashPortDeviceInstance::DeviceInstance0 => {
                    regs.flsha1cr0().modify(|_, w| unsafe { w.flshsz().bits(0) });
                }
                FlexSpiFlashPortDeviceInstance::DeviceInstance1 => {
                    regs.flsha2cr0().modify(|_, w| unsafe { w.flshsz().bits(0) });
                }
            },
            FlexSpiFlashPort::PortB => match self.device_instance {
                FlexSpiFlashPortDeviceInstance::DeviceInstance0 => {
                    regs.flshb1cr0().modify(|_, w| unsafe { w.flshsz().bits(0) });
                }
                FlexSpiFlashPortDeviceInstance::DeviceInstance1 => {
                    regs.flshb2cr0().modify(|_, w| unsafe { w.flshsz().bits(0) });
                }
            },
        }

        regs.iprxfcr().modify(|_, w| unsafe { w.rxwmrk().bits(0) });
        regs.iptxfcr().modify(|_, w| unsafe { w.txwmrk().bits(0) });
    }

    /// Configure the flash self.flexspi_ref based on the external flash device
    pub fn configure_flexspi_device(&self, device_config: FlexspiDeviceConfig, flexspi_config: FlexspiConfig) {
        let regs = self.info.regs;
        let flash_size = device_config.flash_size_kb;

        while regs.sts0().read().arbidle().bit_is_clear() || regs.sts0().read().seqidle().bit_is_clear() {}

        let dll_val = Self::calc_dll_value(&device_config, &flexspi_config);

        if device_config.enable_write_mask {
            regs.flshcr4().write(|w| w.wmopt1().wmopt1_1());
        } else {
            regs.flshcr4().write(|w| w.wmopt1().wmopt1_0());
        }

        match self.flash_port {
            FlexSpiFlashPort::PortA => {
                regs.dllcr(0).modify(|_, w| unsafe { w.bits(dll_val) });
                if device_config.enable_write_mask {
                    regs.flshcr4().write(|w| w.wmena().wmena_1());
                } else {
                    regs.flshcr4().write(|w| w.wmena().wmena_0());
                }
                match self.device_instance {
                    FlexSpiFlashPortDeviceInstance::DeviceInstance0 => {
                        regs.flsha1cr0().modify(|_, w| unsafe { w.flshsz().bits(flash_size) });
                        regs.flshcr1a1().modify(|_, w| unsafe {
                            w.csinterval()
                                .bits(device_config.cs_interval)
                                .tcsh()
                                .bits(device_config.cs_hold_time)
                                .tcss()
                                .bits(device_config.cs_setup_time)
                                .cas()
                                .bits(device_config.columnspace)
                                .wa()
                                .bit(device_config.enable_word_address)
                        });
                        match device_config.cs_interval_unit {
                            FlexspiCsIntervalCycleUnit::CsIntervalUnit256Cycle => {
                                regs.flshcr1a1().modify(|_, w| w.csintervalunit().csintervalunit_1());
                            }
                            FlexspiCsIntervalCycleUnit::CsIntervalUnit1Cycle => {
                                regs.flshcr1a1().modify(|_, w| w.csintervalunit().csintervalunit_0());
                            }
                        }
                        match device_config.ahb_write_wait_unit {
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit2ahbCycle => {
                                regs.flshcr2a1().modify(|_, w| w.awrwaitunit().awrwaitunit_0());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit8ahbCycle => {
                                regs.flshcr2a1().modify(|_, w| w.awrwaitunit().awrwaitunit_1());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit32ahbCycle => {
                                regs.flshcr2a1().modify(|_, w| w.awrwaitunit().awrwaitunit_2());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit128ahbCycle => {
                                regs.flshcr2a1().modify(|_, w| w.awrwaitunit().awrwaitunit_3());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit512ahbCycle => {
                                regs.flshcr2a1().modify(|_, w| w.awrwaitunit().awrwaitunit_4());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit2048ahbCycle => {
                                regs.flshcr2a1().modify(|_, w| w.awrwaitunit().awrwaitunit_5());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit8192ahbCycle => {
                                regs.flshcr2a1().modify(|_, w| w.awrwaitunit().awrwaitunit_6());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit32768ahbCycle => {
                                regs.flshcr2a1().modify(|_, w| w.awrwaitunit().awrwaitunit_7());
                            }
                        }

                        if device_config.ard_seq_number > 0 {
                            regs.flshcr2a1().modify(|_, w| unsafe {
                                w.ardseqnum()
                                    .bits(device_config.ard_seq_number - 1)
                                    .ardseqid()
                                    .bits(device_config.ard_seq_index)
                            });
                        }
                    }

                    FlexSpiFlashPortDeviceInstance::DeviceInstance1 => {
                        regs.flsha2cr0().modify(|_, w| unsafe { w.flshsz().bits(flash_size) });
                        regs.flshcr1a2().modify(|_, w| unsafe {
                            w.csinterval()
                                .bits(device_config.cs_interval)
                                .tcsh()
                                .bits(device_config.cs_hold_time)
                                .tcss()
                                .bits(device_config.cs_setup_time)
                                .cas()
                                .bits(device_config.columnspace)
                                .wa()
                                .bit(device_config.enable_word_address)
                        });
                        match device_config.cs_interval_unit {
                            FlexspiCsIntervalCycleUnit::CsIntervalUnit256Cycle => {
                                regs.flshcr1a2().modify(|_, w| w.csintervalunit().csintervalunit_1());
                            }
                            FlexspiCsIntervalCycleUnit::CsIntervalUnit1Cycle => {
                                regs.flshcr1a2().modify(|_, w| w.csintervalunit().csintervalunit_0());
                            }
                        }
                        match device_config.ahb_write_wait_unit {
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit2ahbCycle => {
                                regs.flshcr2a2().modify(|_, w| w.awrwaitunit().awrwaitunit_0());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit8ahbCycle => {
                                regs.flshcr2a2().modify(|_, w| w.awrwaitunit().awrwaitunit_1());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit32ahbCycle => {
                                regs.flshcr2a2().modify(|_, w| w.awrwaitunit().awrwaitunit_2());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit128ahbCycle => {
                                regs.flshcr2a2().modify(|_, w| w.awrwaitunit().awrwaitunit_3());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit512ahbCycle => {
                                regs.flshcr2a2().modify(|_, w| w.awrwaitunit().awrwaitunit_4());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit2048ahbCycle => {
                                regs.flshcr2a2().modify(|_, w| w.awrwaitunit().awrwaitunit_5());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit8192ahbCycle => {
                                regs.flshcr2a2().modify(|_, w| w.awrwaitunit().awrwaitunit_6());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit32768ahbCycle => {
                                regs.flshcr2a2().modify(|_, w| w.awrwaitunit().awrwaitunit_7());
                            }
                        }
                        if device_config.ard_seq_number > 0 {
                            regs.flshcr2a2().modify(|_, w| unsafe {
                                w.ardseqnum()
                                    .bits(device_config.ard_seq_number - 1)
                                    .ardseqid()
                                    .bits(device_config.ard_seq_index)
                            });
                        }
                    }
                }
            }
            FlexSpiFlashPort::PortB => {
                regs.dllcr(1).modify(|_, w| unsafe { w.bits(dll_val) });
                if device_config.enable_write_mask {
                    regs.flshcr4().write(|w| w.wmenb().wmenb_1());
                } else {
                    regs.flshcr4().write(|w| w.wmenb().wmenb_0());
                }
                match self.device_instance {
                    FlexSpiFlashPortDeviceInstance::DeviceInstance0 => {
                        regs.flshb1cr0().modify(|_, w| unsafe { w.flshsz().bits(flash_size) });
                        regs.flshcr1b1().modify(|_, w| unsafe {
                            w.csinterval()
                                .bits(device_config.cs_interval)
                                .tcsh()
                                .bits(device_config.cs_hold_time)
                                .tcss()
                                .bits(device_config.cs_setup_time)
                                .cas()
                                .bits(device_config.columnspace)
                                .wa()
                                .bit(device_config.enable_word_address)
                        });
                        match device_config.cs_interval_unit {
                            FlexspiCsIntervalCycleUnit::CsIntervalUnit256Cycle => {
                                regs.flshcr1b1().modify(|_, w| w.csintervalunit().csintervalunit_1());
                            }
                            FlexspiCsIntervalCycleUnit::CsIntervalUnit1Cycle => {
                                regs.flshcr1b1().modify(|_, w| w.csintervalunit().csintervalunit_0());
                            }
                        }
                        match device_config.ahb_write_wait_unit {
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit2ahbCycle => {
                                regs.flshcr2b1().modify(|_, w| w.awrwaitunit().awrwaitunit_0());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit8ahbCycle => {
                                regs.flshcr2b1().modify(|_, w| w.awrwaitunit().awrwaitunit_1());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit32ahbCycle => {
                                regs.flshcr2b1().modify(|_, w| w.awrwaitunit().awrwaitunit_2());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit128ahbCycle => {
                                regs.flshcr2b1().modify(|_, w| w.awrwaitunit().awrwaitunit_3());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit512ahbCycle => {
                                regs.flshcr2b1().modify(|_, w| w.awrwaitunit().awrwaitunit_4());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit2048ahbCycle => {
                                regs.flshcr2b1().modify(|_, w| w.awrwaitunit().awrwaitunit_5());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit8192ahbCycle => {
                                regs.flshcr2b1().modify(|_, w| w.awrwaitunit().awrwaitunit_6());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit32768ahbCycle => {
                                regs.flshcr2b1().modify(|_, w| w.awrwaitunit().awrwaitunit_7());
                            }
                        }
                        if device_config.ard_seq_number > 0 {
                            regs.flshcr2b1().modify(|_, w| unsafe {
                                w.ardseqnum()
                                    .bits(device_config.ard_seq_number - 1)
                                    .ardseqid()
                                    .bits(device_config.ard_seq_index)
                            });
                        }
                    }
                    FlexSpiFlashPortDeviceInstance::DeviceInstance1 => {
                        regs.flshb2cr0().modify(|_, w| unsafe { w.flshsz().bits(flash_size) });
                        regs.flshcr1b2().modify(|_, w| unsafe {
                            w.csinterval()
                                .bits(device_config.cs_interval)
                                .tcsh()
                                .bits(device_config.cs_hold_time)
                                .tcss()
                                .bits(device_config.cs_setup_time)
                                .cas()
                                .bits(device_config.columnspace)
                                .wa()
                                .bit(device_config.enable_word_address)
                        });
                        match device_config.cs_interval_unit {
                            FlexspiCsIntervalCycleUnit::CsIntervalUnit256Cycle => {
                                regs.flshcr1b2().modify(|_, w| w.csintervalunit().csintervalunit_1());
                            }
                            FlexspiCsIntervalCycleUnit::CsIntervalUnit1Cycle => {
                                regs.flshcr1b2().modify(|_, w| w.csintervalunit().csintervalunit_0());
                            }
                        }
                        match device_config.ahb_write_wait_unit {
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit2ahbCycle => {
                                regs.flshcr2b2().modify(|_, w| w.awrwaitunit().awrwaitunit_0());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit8ahbCycle => {
                                regs.flshcr2b2().modify(|_, w| w.awrwaitunit().awrwaitunit_1());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit32ahbCycle => {
                                regs.flshcr2b2().modify(|_, w| w.awrwaitunit().awrwaitunit_2());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit128ahbCycle => {
                                regs.flshcr2b2().modify(|_, w| w.awrwaitunit().awrwaitunit_3());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit512ahbCycle => {
                                regs.flshcr2b2().modify(|_, w| w.awrwaitunit().awrwaitunit_4());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit2048ahbCycle => {
                                regs.flshcr2b2().modify(|_, w| w.awrwaitunit().awrwaitunit_5());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit8192ahbCycle => {
                                regs.flshcr2b2().modify(|_, w| w.awrwaitunit().awrwaitunit_6());
                            }
                            FlexspiAhbWriteWaitUnit::FlexspiAhbWriteWaitUnit32768ahbCycle => {
                                regs.flshcr2b2().modify(|_, w| w.awrwaitunit().awrwaitunit_7());
                            }
                        }
                        if device_config.ard_seq_number > 0 {
                            regs.flshcr2b2().modify(|_, w| unsafe {
                                w.ardseqnum()
                                    .bits(device_config.ard_seq_number - 1)
                                    .ardseqid()
                                    .bits(device_config.ard_seq_index)
                            });
                        }
                    }
                }
            }
        }

        // Enable the module
        regs.mcr0().write(|w| w.mdis().clear_bit());

        //Errata ERR011377 - need to delay at least 100 NOPs to ensure the DLL is locked.
        match self.flash_port {
            FlexSpiFlashPort::PortA => {
                while regs.sts2().read().aslvlock().bit_is_clear() && regs.sts2().read().areflock().bit_is_clear() {
                    // Wait for DLL lock
                }

                for i in 0..100 {
                    asm::nop();
                }
            }
            FlexSpiFlashPort::PortB => {
                while regs.sts2().read().bslvlock().bit_is_clear() && regs.sts2().read().breflock().bit_is_clear() {
                    // Wait for DLL lock
                }

                for i in 0..100 {
                    asm::nop();
                }
            }
        }
    }

    fn calc_dll_value(device_config: &FlexspiDeviceConfig, flexspi_config: &FlexspiConfig) -> u32 {
        let mut is_unified_config = true;
        let mut flexspi_dll_value = 0u32;
        let mut dll_value = 0u32;
        let mut temp = 0u32;

        let rx_sample_clock = flexspi_config.rx_sample_clock;
        match rx_sample_clock {
            FlexspiReadSampleClock::FlexspiReadSampleClkLoopbackInternally => {
                is_unified_config = true;
            }
            FlexspiReadSampleClock::FlexspiReadSampleClkLoopbackFromDqsPad => {
                is_unified_config = true;
            }
            FlexspiReadSampleClock::FlexspiReadSampleClkLoopbackFromSckPad => {
                is_unified_config = true;
            }
            FlexspiReadSampleClock::FlexspiReadSampleClkExternalInputFromDqsPad => {
                is_unified_config = device_config.is_sck2_enabled;
            }
        }

        if is_unified_config {
            flexspi_dll_value = 0x100; /* 1 fixed delay cells in DLL delay chain) */
        } else if (device_config.flexspi_root_clk >= 100000000) {
            /* DLLEN = 1, SLVDLYTARGET = 0xF, */
            flexspi_dll_value = 0x1 | (0xF << 3);
        } else {
            temp = (device_config.data_valid_time) as u32 * 1000; /* Convert data valid time in ns to ps. */
            dll_value = temp / 75;
            if (dll_value * 75 < temp) {
                dll_value += 1;
            }
            flexspi_dll_value = 0x1 << 8 | (dll_value & 0x78) << 9; // TODO: remove hardcoding
        }
        flexspi_dll_value
    }

    /// Enable or disable clock
    pub fn enable_disable_clock(&self, op: bool) {
        // Enable or disable clock
    }
    /// Enable or disable SRAM
    pub fn enable_disable_sram(&self, op: bool) {
        // Enable or disable SRAM
    }
    /// Reset FlexSPI
    pub fn apply_clear_reset(&self, op: bool) {
        // Reset FlexSPI
    }
    /// Enable Disable FlexSPI module
    pub fn enable_disable_flexspi_module(&self, op: bool) {}
}

/// FlexSPI Data Pins
pub trait FlexSpiDataPin: Pin + sealed::Sealed + crate::Peripheral {
    /// Configure FlexSPI Data Pin
    fn config_pin(&self);
}
/// FlexSPI CS Pin
pub trait FlexSpiCsPin: Pin + sealed::Sealed + crate::Peripheral {
    /// Configure FlexSPI CS Pin
    fn config_pin(&self);
}
/// FlexSPI Clock Pin
pub trait FlexSpiClkPin: Pin + sealed::Sealed + crate::Peripheral {
    /// Configure FlexSPI Clock Pin
    fn config_pin(&self);
}

impl<M: Mode, E: Execution> FlexspiStorage<M, E> {}

impl FlexspiStorage<Blocking, Xip> {
    /// Create a new FlexSPI instance in blocking mode
    pub fn new_blocking_xip<T: Instance>(
        _instance: T,
        port: FlexSpiFlashPort,
        dev_instance: FlexSpiFlashPortDeviceInstance,
    ) -> Self {
        Self {
            info: T::info(),
            write_policy: WritePolicy,
            read_policy: ReadPolicy,
            rx_watermark: 8,
            tx_watermark: 8,
            _mode: core::marker::PhantomData,
            flexspi_ref: unsafe { (crate::pac::Flexspi::ptr() as *mut FlexSpi).as_mut().unwrap() },
            configport: None,
            device_instance: dev_instance,
            flash_port: port,
        }
    }
}
impl StorageDataPort<Blocking> for FlexspiStorage<Blocking, Xip> {}
impl StorageCmdPort<Blocking> for FlexspiStorage<Blocking, Xip> {}

// impl FlexspiStorage<Blocking, Ram> {
//     #[allow(clippy::too_many_arguments)]
//     /// Create a new FlexSPI instance in blocking mode with RAM execution
//     pub fn new_blocking_ram<T: Instance>(
//         _inst: T,
//         data0: Option<impl FlexSpiDataPin>,
//         data1: Option<impl FlexSpiDataPin>,
//         data2: Option<impl FlexSpiDataPin>,
//         data3: Option<impl FlexSpiDataPin>,
//         data4: Option<impl FlexSpiDataPin>,
//         data5: Option<impl FlexSpiDataPin>,
//         data6: Option<impl FlexSpiDataPin>,
//         data7: Option<impl FlexSpiDataPin>,
//         clk: impl FlexSpiClkPin,
//         cs: impl FlexSpiCsPin,
//         port: FlexSpiFlashPort,
//         bus_width: FlexSpiBusWidth,
//         dev_instance: FlexSpiFlashPortDeviceInstance,
//     ) -> Self {
//         if let Some(data0) = data0 {
//             data0.config_pin();
//         }
//         if let Some(data1) = data1 {
//             data1.config_pin();
//         }
//         if let Some(data2) = data2 {
//             data2.config_pin();
//         }
//         if let Some(data3) = data3 {
//             data3.config_pin();
//         }
//         if let Some(data4) = data4 {
//             data4.config_pin();
//         }
//         if let Some(data5) = data5 {
//             data5.config_pin();
//         }
//         if let Some(data6) = data6 {
//             data6.config_pin();
//         }
//         if let Some(data7) = data7 {
//             data7.config_pin();
//         }

//         cs.config_pin();
//         clk.config_pin();

//         Self {
//             cmdport: StorageCmdPort {
//                 info: T::info(),
//                 write_policy: WritePolicy,
//                 read_policy: ReadPolicy,
//                 rx_watermark: 8,
//                 tx_watermark: 8,
//                 _mode: core::marker::PhantomData,
//                 flexspi_ref: unsafe { (crate::pac::Flexspi::ptr() as *mut FlexSpi).as_mut().unwrap() },
//             },
//             dataport: StorageDataPort {
//                 info: T::info(),
//                 write_policy: WritePolicy,
//                 read_policy: ReadPolicy,
//                 _mode: core::marker::PhantomData,
//                 flexspi_ref: unsafe { (crate::pac::Flexspi::ptr() as *mut FlexSpi).as_mut().unwrap() },
//                 device_instance: dev_instance,
//                 flash_port: port,
//             },
//             configport: Some(FlexSpiConfigurationPort {
//                 info: T::info(),
//                 bus_width,
//                 device_instance: dev_instance,
//                 flash_port: port,
//                 _execution: core::marker::PhantomData,
//             }),
//         }
//     }
// }

macro_rules! impl_data_pin {
    ($peri:ident, $fn: ident, $invert: ident, $pull: ident) => {
        impl FlexSpiDataPin for crate::peripherals::$peri {
            fn config_pin(&self) {
                self.set_function(crate::iopctl::Function::$fn)
                    .set_pull(crate::iopctl::Pull::None)
                    .set_slew_rate(crate::gpio::SlewRate::Slow)
                    .set_drive_strength(crate::gpio::DriveStrength::Normal)
                    .disable_analog_multiplex()
                    .set_drive_mode(crate::gpio::DriveMode::$pull)
                    .set_input_inverter(crate::gpio::Inverter::$invert);
            }
        }
    };
}

macro_rules! impl_cs_pin {
    ($peri:ident, $fn: ident) => {
        impl FlexSpiCsPin for crate::peripherals::$peri {
            fn config_pin(&self) {
                self.set_function(crate::iopctl::Function::$fn)
                    .set_pull(crate::iopctl::Pull::None)
                    .set_slew_rate(crate::gpio::SlewRate::Standard)
                    .set_drive_strength(crate::gpio::DriveStrength::Normal)
                    .set_drive_mode(crate::gpio::DriveMode::PushPull)
                    .set_input_inverter(crate::gpio::Inverter::Disabled);
            }
        }
    };
}
macro_rules! impl_clk_pin {
    ($peri:ident, $fn: ident) => {
        impl FlexSpiClkPin for crate::peripherals::$peri {
            fn config_pin(&self) {
                self.set_function(crate::iopctl::Function::$fn)
                    .set_pull(crate::iopctl::Pull::None)
                    .enable_input_buffer()
                    .set_slew_rate(crate::gpio::SlewRate::Standard)
                    .set_drive_strength(crate::gpio::DriveStrength::Full)
                    .disable_analog_multiplex()
                    .set_drive_mode(crate::gpio::DriveMode::PushPull)
                    .set_input_inverter(crate::gpio::Inverter::Disabled);
            }
        }
    };
}

impl_data_pin!(PIO1_11, F6, Disabled, PushPull); // PortB-DATA0
impl_data_pin!(PIO1_12, F6, Disabled, PushPull); // PortB-DATA1
impl_data_pin!(PIO1_13, F6, Disabled, PushPull); // PortB-DATA2
impl_data_pin!(PIO1_14, F6, Disabled, PushPull); // PortB-DATA3
impl_data_pin!(PIO2_17, F6, Disabled, PushPull); // PortB-DATA4
impl_data_pin!(PIO2_18, F6, Disabled, PushPull); // PortB-DATA5
impl_data_pin!(PIO2_22, F6, Disabled, PushPull); // PortB-DATA6
impl_data_pin!(PIO2_23, F6, Disabled, PushPull); // PortB-DATA7
impl_cs_pin!(PIO2_19, F6); // PortB-CS0
impl_cs_pin!(PIO2_21, F6); // PortB-CS1
impl_clk_pin!(PIO1_29, F5); // PortB-SCLK

// impl_cs_pin!(PIO1_19, F1); // PortA-CS0
// impl_clk_pin!(PIO1_18, F1); // PortA-SCLK
// impl_data_pin!(PIO1_20, F1); // PortA-DATA0
// impl_data_pin!(PIO1_21, F1); // PortA-DATA1
// impl_data_pin!(PIO1_22, F1); // PortA-DATA2
// impl_data_pin!(PIO1_23, F1); // PortA-DATA3
// impl_data_pin!(PIO1_24, F1); // PortA-DATA4
// impl_data_pin!(PIO1_25, F1); // PortA-DATA5
// impl_data_pin!(PIO1_26, F1); // PortA-DATA6
// impl_data_pin!(PIO1_27, F1); // PortA-DATA7
