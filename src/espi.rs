//! Enhanced Serial Peripheral Interface (eSPI) driver.

use core::future::poll_fn;
use core::marker::PhantomData;
use core::slice;
use core::task::Poll;

use embassy_sync::waitqueue::AtomicWaker;
use paste::paste;

use crate::clocks::{SysconPeripheral, enable_and_reset};
use crate::gpio::{DriveMode, DriveStrength, Function, GpioPin as Pin, Inverter, Pull, SlewRate};
use crate::interrupt::typelevel::Interrupt;
pub use crate::pac::espi::espicap::{Flashmx, Maxspd, Safera, Spicap};
pub use crate::pac::espi::port::addr::BaseOrAsz;
pub use crate::pac::espi::port::cfg::Direction;
use crate::pac::espi::port::cfg::Type;
pub use crate::pac::espi::port::ramuse::Len;
pub use crate::pac::espi::stataddr::Base;
use crate::{Peri, PeripheralType, interrupt, peripherals};

// This controller has 5 different eSPI ports
const ESPI_PORTS: usize = 5;

static ESPI_WAKER: AtomicWaker = AtomicWaker::new();

/// Result type alias
pub type Result<T> = core::result::Result<T, Error>;

/// eSPI error
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum Error {
    /// CRC Error
    Crc,

    /// HStall Error
    HStall,

    /// Invalid Port Error
    InvalidPort,

    /// Invalid Parameter Error
    InvalidParameter,
}

/// eSPI Command Length
#[derive(Debug, PartialEq, Clone, Copy)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum Length {
    /// 1 byte
    OneByte,

    /// 2 bytes
    TwoBytes,

    /// 4 bytes
    FourBytes,
}

impl From<Length> for u8 {
    fn from(length: Length) -> u8 {
        match length {
            Length::OneByte => 0,
            Length::TwoBytes => 1,
            Length::FourBytes => 3,
        }
    }
}

/// eSPI interrupt handler.
pub struct InterruptHandler<T: Instance> {
    _phantom: PhantomData<T>,
}

impl<T: Instance> interrupt::typelevel::Handler<T::Interrupt> for InterruptHandler<T> {
    unsafe fn on_interrupt() {
        let stat = T::info().regs.intstat().read();
        T::info().regs.intenclr().write(|w| unsafe { w.bits(stat.bits()) });

        if stat.bus_rst().bit_is_set()
            || stat.port_int0().bit_is_set()
            || stat.port_int1().bit_is_set()
            || stat.port_int2().bit_is_set()
            || stat.port_int3().bit_is_set()
            || stat.port_int4().bit_is_set()
            || stat.p80int().bit_is_set()
            || stat.bus_rst().bit_is_set()
            || stat.irq_upd().bit_is_set()
            || stat.wire_chg().bit_is_set()
            || stat.hstall().bit_is_set()
            || stat.crcerr().bit_is_set()
            || stat.gpio().bit_is_set()
        {
            ESPI_WAKER.wake();
        }
    }
}

/// eSPI Port configuration.
#[derive(Default, Debug, PartialEq, Eq, Clone, Copy)]
pub enum PortConfig {
    /// Unconfigured
    #[default]
    Unconfigured,

    /// ACPI-style Endpoint
    AcpiEndpoint {
        /// Port Direction
        direction: Direction,

        /// Base memory to select for port base
        base_sel: BaseOrAsz,

        /// 12-bit Word-aligned offset from selected base
        offset: u16,
    },

    /// ACPI-style Index/Data
    AcpiIndex,

    /// Mailbox Shared
    MailboxShared {
        /// Port Direction
        direction: Direction,

        /// Base memory to select for port base
        base_sel: BaseOrAsz,

        /// 12-bit Word-aligned offset from selected base
        offset: u16,

        /// Length of the mailbox or mastering area per direction.
        length: Len,
    },

    /// Mailbox Single
    MailboxSingle {
        /// Port Direction
        direction: Direction,

        /// Base memory to select for port base
        base_sel: BaseOrAsz,

        /// 12-bit Word-aligned offset from selected base
        offset: u16,

        /// This is the length of the mailbox or mastering area per
        /// direction.
        length: Len,
    },

    /// Mailbox Split
    MailboxSplit {
        /// Port Direction
        direction: Direction,

        /// Base memory to select for port base
        base_sel: BaseOrAsz,

        /// 12-bit Word-aligned offset from selected base
        offset: u16,

        /// This is the length of the mailbox or mastering area per
        /// direction.
        length: Len,
    },

    /// Put Posted/Completion Mem32
    PutPcMem32,

    /// Mailbox Split OOB
    MailboxSplitOOB {
        /// 12-bit Word-aligned offset from selected base
        offset: u16,

        /// Length of the mailbox or mastering area per direction.
        length: Len,
    },

    /// Slave Flash
    SlaveFlash,

    /// Mem Single
    MemSingle,

    /// Master Flash
    MasterFlash,
}

impl From<PortConfig> for Type {
    fn from(val: PortConfig) -> Self {
        match val {
            PortConfig::Unconfigured => Type::Unconfigured,
            PortConfig::AcpiEndpoint { .. } => Type::AcpiEnd,
            PortConfig::AcpiIndex => Type::AcpiIndex,
            PortConfig::MailboxShared { .. } => Type::MailboxShared,
            PortConfig::MailboxSingle { .. } => Type::MailboxSingle,
            PortConfig::MailboxSplit { .. } => Type::MailboxSplit,
            PortConfig::PutPcMem32 => Type::MailboxShared,
            PortConfig::MailboxSplitOOB { .. } => Type::MailboxOobSplit,
            PortConfig::SlaveFlash => Type::BusMFlashS,
            PortConfig::MemSingle => Type::BusMMemS,
            PortConfig::MasterFlash => Type::BusMFlashS,
        }
    }
}

/// eSPI capabilities.
#[derive(Clone, Copy)]
pub struct Capabilities {
    /// Mode of operation
    pub mode: Spicap,

    /// Max speed
    pub max_speed: Maxspd,

    /// Allow use of alert pin
    pub alert_as_a_pin: bool,

    /// Allow out-of-band
    pub allow_oob: bool,

    /// Allow 128b payload
    pub allow_128b_payload: bool,

    /// Flash payload size
    pub flash_payload_size: Flashmx,

    /// Slave-attached-flash erase size
    pub saf_erase_size: Option<Safera>,
}

impl Default for Capabilities {
    fn default() -> Self {
        Self {
            mode: Spicap::Any,
            max_speed: Maxspd::SmallThan20m,
            alert_as_a_pin: false,
            allow_oob: false,
            allow_128b_payload: false,
            flash_payload_size: Flashmx::Byte64,
            saf_erase_size: None,
        }
    }
}

/// eSPI configuration.
#[derive(Clone, Copy)]
pub struct Config {
    /// Instance capabilities
    pub caps: Capabilities,

    /// Use 60MHz clock?
    pub use_60mhz: bool,

    /// RAM Base address
    pub ram_base: u32,

    /// Base 0 Address
    pub base0_addr: u32,

    /// Base 1 Address
    pub base1_addr: u32,

    /// Status Block address
    pub status_addr: Option<u16>,

    /// Status Block Base
    pub status_base: Base,

    /// Per-port configuration
    pub ports_config: [PortConfig; ESPI_PORTS],
}

impl Default for Config {
    fn default() -> Self {
        Self {
            caps: Default::default(),
            use_60mhz: false,
            ram_base: 0,
            base0_addr: 0,
            base1_addr: 0,
            status_addr: None,
            status_base: Base::OffsetFrom0,
            ports_config: Default::default(),
        }
    }
}

/// Port event data
pub struct PortEvent {
    /// Port that event occurred on
    pub port: usize,

    /// Base address of buffer
    pub base_addr: u32,

    /// Offset into buffer
    pub offset: usize,

    /// Size of access
    pub length: usize,

    /// Direction of access
    pub direction: bool,
}

/// Wire Change Event
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct WireChangeEvent {
    slp_s3n: bool,
    slp_s4n: bool,
    slp_s5n: bool,
    sus_stat: bool,
    pltrstn: bool,
    oob_rst_warn: bool,
    host_rst_warn: bool,
    sus_warnn: bool,
    sus_pwrdn_ackn: bool,
    slp_an: bool,
    slp_lann: bool,
    slp_wlann: bool,
    p2e: u8,
    host_c10n: bool,
}

impl WireChangeEvent {
    /// Set when power to non-critical systems should be shut off in
    /// S3 (Suspend to RAM).
    pub fn is_s3_sleep_control(&self) -> bool {
        self.slp_s3n
    }

    /// Set when power to non-critical systems should be shut off in
    /// S4 (Suspend to Disk).
    pub fn is_s4_sleep_control(&self) -> bool {
        self.slp_s4n
    }

    /// Set when power to non-critical systems should be shut off in
    /// S5 (Soft Off).
    pub fn is_s5_sleep_control(&self) -> bool {
        self.slp_s5n
    }

    /// Set when the system will be entering a low power state soon.
    pub fn is_suspend_status(&self) -> bool {
        self.sus_stat
    }

    /// Command to indicate Platform Reset assertion and de-assertion.
    pub fn is_platform_reset(&self) -> bool {
        self.pltrstn
    }

    /// Sent by controller just begore the OOB processor is about to
    /// enter reset.
    pub fn is_oob_reset_warn(&self) -> bool {
        self.oob_rst_warn
    }

    /// Sent by controller just before the Host is about to enter
    /// reset.
    pub fn is_host_reset_warn(&self) -> bool {
        self.host_rst_warn
    }

    /// Suspend about to happen.
    pub fn is_suspend_warn(&self) -> bool {
        self.sus_warnn
    }

    /// Host indicates that suspend power well can be shut down
    /// safely.
    pub fn is_suspend_power_down_ack(&self) -> bool {
        self.sus_pwrdn_ackn
    }

    /// Used when in Sx sleep but Management Engine is on.
    pub fn is_sleep_a(&self) -> bool {
        self.slp_an
    }

    /// Wired LAN can be powered down.
    pub fn is_sleep_lan(&self) -> bool {
        self.slp_lann
    }

    /// Wireless LAN can be powered down.
    pub fn is_sleep_wlan(&self) -> bool {
        self.slp_wlann
    }

    /// PCH to EC byte
    pub fn p2e(&self) -> u8 {
        self.p2e
    }

    /// Asserted when Host has entered deep power down state C10 or
    /// deeper.
    pub fn is_host_c10(&self) -> bool {
        self.host_c10n
    }
}

/// eSPI events.
pub enum Event {
    ///  OOB event on port 0-4
    OOBEvent(PortEvent),

    /// Peripheral event on port 0-4
    PeripheralEvent(PortEvent),

    /// Port 80 has pending events
    Port80,

    /// Change in virtual wires
    WireChange(WireChangeEvent),
}

/// eSPI Boot Status.
pub enum BootStatus {
    /// Success
    Success,

    /// Failure
    Failure,
}

impl From<BootStatus> for bool {
    fn from(status: BootStatus) -> bool {
        matches!(status, BootStatus::Success)
    }
}

/// eSPI driver.
pub struct Espi<'d> {
    info: Info,
    config: Config,
    _phantom: PhantomData<&'d ()>,
}

impl<'d> Espi<'d> {
    /// Instantiates new eSPI peripheral and initializes to default values.
    #[allow(clippy::too_many_arguments)]
    pub fn new<T: Instance>(
        _peripheral: Peri<'d, T>,
        _clk: Peri<'d, impl ClkPin<T>>,
        _cs: Peri<'d, impl CsPin<T>>,
        _io0: Peri<'d, impl Io0Pin<T>>,
        _io1: Peri<'d, impl Io1Pin<T>>,
        _io2: Peri<'d, impl Io2Pin<T>>,
        _io3: Peri<'d, impl Io3Pin<T>>,
        _rst: Peri<'d, impl RstPin<T>>,
        _alert: Peri<'d, impl AlertPin<T>>,
        _irq: impl interrupt::typelevel::Binding<T::Interrupt, InterruptHandler<T>> + 'd,
        config: Config,
    ) -> Espi<'d> {
        _alert.as_alert();
        _rst.as_rst();
        _cs.as_cs();
        _io0.as_io0();
        _io1.as_io1();
        _clk.as_clk();
        _io2.as_io2();
        _io3.as_io3();

        // enable ESPI clock
        enable_and_reset::<T>();

        let mut instance = Espi::<'d> {
            info: T::info(),
            config,
            _phantom: PhantomData,
        };

        // Set ESPI mode
        instance.info.regs.mctrl().modify(|_, w| w.enable().espi());

        // Save configuration for future reference
        instance.config = config;

        // Configure ports
        for port in 0..ESPI_PORTS {
            instance.configure(port, config.ports_config[port]);
        }

        // Set eSPI status block address
        if let Some(status_addr) = config.status_addr {
            // SAFETY: Unsafe only due to the use of `bits()`. All 16-bits are
            // valid, any 16-bit offset can be used.
            instance
                .info
                .regs
                .stataddr()
                .write(|w| unsafe { w.off().bits(status_addr) }.base().variant(config.status_base));

            instance.info.regs.mctrl().modify(|_, w| w.sblkena().set_bit());
        }

        // Set eSPI capabilities
        instance.info.regs.espicap().write(|w| {
            w.spicap()
                .variant(config.caps.mode)
                .maxspd()
                .variant(config.caps.max_speed)
                .alpin()
                .variant(config.caps.alert_as_a_pin)
                .oobok()
                .variant(config.caps.allow_oob)
                .memmx()
                .variant(config.caps.allow_128b_payload)
                .flashmx()
                .variant(config.caps.flash_payload_size)
                .saf()
                .variant(config.caps.saf_erase_size.is_some())
                .safera()
                .variant(config.caps.saf_erase_size.unwrap_or(Safera::Min2kb))
        });

        // Enable power save
        instance.info.regs.espimisc().write(|w| w.pwrsav().set_bit());

        // Clear Bus Reset status
        instance.info.regs.mstat().write(|w| w.bus_rst().clear_bit_by_one());

        // Set RAMBASE
        instance
            .info
            .regs
            .rambase()
            .write(|w| unsafe { w.bits(config.ram_base) });

        // Set MapBase addr
        instance.info.regs.mapbase().write(|w| unsafe {
            w.base1()
                .bits((config.base1_addr >> 16) as u16)
                .base0()
                .bits((config.base0_addr >> 16) as u16)
        });

        instance
            .info
            .regs
            .mctrl()
            .modify(|_, w| w.use60mhz().variant(config.use_60mhz));

        T::Interrupt::unpend();
        unsafe { T::Interrupt::enable() };

        instance
    }

    /// Configure the port to a given mode
    pub fn configure(&mut self, port: usize, config: PortConfig) {
        match config {
            PortConfig::AcpiEndpoint {
                direction,
                base_sel,
                offset,
            } => {
                self.mailbox(port, config.into(), direction, base_sel, offset, Len::Len4);
            }

            PortConfig::MailboxShared {
                direction,
                base_sel,
                offset,
                length,
            } => {
                self.mailbox(port, config.into(), direction, base_sel, offset, length);
            }

            PortConfig::MailboxSingle {
                direction,
                base_sel,
                offset,
                length,
            } => {
                self.mailbox(port, config.into(), direction, base_sel, offset, length);
            }

            PortConfig::MailboxSplit {
                direction,
                base_sel,
                offset,
                length,
            } => {
                self.mailbox(port, config.into(), direction, base_sel, offset, length);
            }

            PortConfig::MailboxSplitOOB { offset, length } => {
                self.mailbox(
                    port,
                    config.into(),
                    Direction::BidirectionalUnenforced,
                    BaseOrAsz::OffsetFrom0,
                    offset,
                    length,
                );
            }

            _ => {
                self.info.regs.mctrl().modify(|_, w| w.pena(port as u8).disabled());
            }
        }
    }

    /// Complete port status
    pub fn complete_port(&mut self, port: usize) {
        self.info.regs.port(port).stat().write(|w| {
            w.interr()
                .clear_bit_by_one()
                .intrd()
                .clear_bit_by_one()
                .intwr()
                .clear_bit_by_one()
                .intspc0()
                .clear_bit_by_one()
                .intspc1()
                .clear_bit_by_one()
                .intspc2()
                .clear_bit_by_one()
                .intspc3()
                .clear_bit_by_one()
        });
    }

    fn get_port_event(&mut self, port: usize) -> Poll<Result<Event>> {
        // If port is not configured ignore and return Poll::Pending
        if self.config.ports_config[port] == PortConfig::Unconfigured {
            return Poll::Pending;
        }

        // Common registers for all ports
        let datain = self.info.regs.port(port).datain().read();
        let idxoff = datain.idx().bits() as usize;
        let length = datain.data_len().bits() as usize + 1;
        let direction = datain.dir().bit_is_set();

        match self.config.ports_config[port] {
            PortConfig::AcpiEndpoint { base_sel, offset, .. }
            | PortConfig::MailboxSingle { base_sel, offset, .. }
            | PortConfig::MailboxShared { base_sel, offset, .. }
            | PortConfig::MailboxSplit { base_sel, offset, .. } => {
                let address = match base_sel {
                    BaseOrAsz::UseBase0 => self.config.base0_addr + offset as u32,
                    BaseOrAsz::UseBase1 => self.config.base1_addr + offset as u32,
                    _ => self.config.ram_base + offset as u32,
                };

                Poll::Ready(Ok(Event::PeripheralEvent(PortEvent {
                    port,
                    base_addr: address,
                    offset: idxoff,
                    length,
                    direction,
                })))
            }
            PortConfig::MailboxSplitOOB { offset, .. } => {
                let address = self.config.ram_base + offset as u32;
                Poll::Ready(Ok(Event::OOBEvent(PortEvent {
                    port,
                    base_addr: address,
                    offset: 0,
                    length,
                    direction,
                })))
            }
            _ => Poll::Pending,
        }
    }

    /// Wait for controller event
    pub async fn wait_for_event(&mut self) -> Result<Event> {
        self.wait_for(
            |me| {
                if me.info.regs.mstat().read().port_int0().bit_is_set() {
                    me.get_port_event(0)
                } else if me.info.regs.mstat().read().port_int1().bit_is_set() {
                    me.get_port_event(1)
                } else if me.info.regs.mstat().read().port_int2().bit_is_set() {
                    me.get_port_event(2)
                } else if me.info.regs.mstat().read().port_int3().bit_is_set() {
                    me.get_port_event(3)
                } else if me.info.regs.mstat().read().port_int4().bit_is_set() {
                    me.get_port_event(4)
                } else if me.info.regs.mstat().read().p80int().bit_is_set() {
                    Poll::Ready(Ok(Event::Port80))
                } else if me.info.regs.mstat().read().wire_chg().bit_is_set() {
                    me.info.regs.mstat().write(|w| w.wire_chg().clear_bit_by_one());

                    let wirero = me.info.regs.wirero().read();

                    let event = WireChangeEvent {
                        slp_s3n: wirero.slp_s3n().bit_is_set(),
                        slp_s4n: wirero.slp_s4n().bit_is_set(),
                        slp_s5n: wirero.slp_s5n().bit_is_set(),
                        sus_stat: wirero.sus_stat().bit_is_set(),
                        pltrstn: wirero.pltrstn().bit_is_set(),
                        oob_rst_warn: wirero.oob_rst_warn().bit_is_set(),
                        host_rst_warn: wirero.host_rst_warn().bit_is_set(),
                        sus_warnn: wirero.sus_warnn().bit_is_set(),
                        sus_pwrdn_ackn: wirero.sus_pwrdn_ackn().bit_is_set(),
                        slp_an: wirero.slp_an().bit_is_set(),
                        slp_lann: wirero.slp_lann().bit_is_set(),
                        slp_wlann: wirero.slp_wlann().bit_is_set(),
                        p2e: wirero.p2e().bits(),
                        host_c10n: wirero.host_c10n().bit_is_set(),
                    };

                    Poll::Ready(Ok(Event::WireChange(event)))
                } else if me.info.regs.mstat().read().crcerr().bit_is_set() {
                    me.info.regs.mstat().write(|w| w.crcerr().clear_bit_by_one());
                    Poll::Ready(Err(Error::Crc))
                } else if me.info.regs.mstat().read().hstall().bit_is_set() {
                    me.info.regs.mstat().write(|w| w.hstall().clear_bit_by_one());
                    Poll::Ready(Err(Error::HStall))
                } else {
                    Poll::Pending
                }
            },
            |me| {
                me.info.regs.intenset().write(|w| {
                    w.port_int0()
                        .set_bit()
                        .port_int1()
                        .set_bit()
                        .port_int2()
                        .set_bit()
                        .port_int3()
                        .set_bit()
                        .port_int4()
                        .set_bit()
                        .p80int()
                        .set_bit()
                        .wire_chg()
                        .set_bit()
                        .hstall()
                        .set_bit()
                        .crcerr()
                        .set_bit()
                });
            },
        )
        .await
    }

    /// Wait for platform reset
    pub async fn wait_for_plat_reset(&mut self) {
        self.wait_for(
            |me| {
                if me.info.regs.mstat().read().wire_chg().bit_is_set() {
                    me.info.regs.mstat().write(|w| w.wire_chg().clear_bit_by_one());
                    let wirero = me.info.regs.wirero().read();
                    if wirero.pltrstn().bit_is_set() {
                        Poll::Ready(())
                    } else {
                        Poll::Pending
                    }
                } else {
                    Poll::Pending
                }
            },
            |me| {
                me.info.regs.intenset().write(|w| w.wire_chg().set_bit());
            },
        )
        .await
    }

    /// Wait for bus reset
    pub async fn wait_for_reset(&mut self) {
        self.wait_for(
            |me| {
                if me.info.regs.mstat().read().in_rst().bit_is_set() {
                    me.info.regs.mstat().write(|w| w.bus_rst().clear_bit_by_one());
                    Poll::Ready(())
                } else {
                    Poll::Pending
                }
            },
            |me| {
                me.info.regs.intenset().write(|w| w.bus_rst().set_bit());
            },
        )
        .await
    }

    /// Push IRQ to Host
    pub async fn irq_push(&mut self, irq: u8) {
        self.info.regs.irqpush().write(|w| unsafe { w.irq().bits(irq) });

        self.wait_for(
            |me| {
                if me.info.regs.mstat().read().irq_upd().bit_is_set() {
                    me.info.regs.mstat().write(|w| w.irq_upd().clear_bit_by_one());
                    Poll::Ready(())
                } else {
                    Poll::Pending
                }
            },
            |me| {
                me.info.regs.intenset().write(|w| w.irq_upd().set_bit());
            },
        )
        .await
    }

    /// Acknowledge OOB Reset.
    ///
    /// Active High.
    ///
    /// Warning: Blocks until DONE bit clears
    pub fn oob_reset_ack(&mut self) {
        self.info.regs.wirewo().write(|w| w.oob_rst_ack().set_bit());
        self.block_for_vwire_done();
    }

    /// Return pointer to OOB write buffer
    ///
    /// Warning: This directly returns memory buffer based on port config, memory.x
    /// must have memory properly carved out to prevent back access
    ///
    /// # Safety
    /// OOB port config must point to valid memory region that has been carved
    /// out in memory.x to prevent access to code region. After calling oob_write_data
    /// must wait for Event::OOBEvent with direction: true to indicate previous write
    /// has completed. Not waiting for previous transaction can lead to corruption of
    /// OOB packets
    pub unsafe fn oob_get_write_buffer(&mut self, port: usize) -> Result<&mut [u8]> {
        match self.config.ports_config[port] {
            PortConfig::MailboxSplitOOB { offset, length, .. } => {
                // All OOB is split so add offset from read buffer
                let buf_len = (1 << (<Len as Into<u8>>::into(length) + 2)) as u32;
                let buf_addr = (self.config.ram_base + offset as u32 + buf_len) as *mut u8;
                Ok(unsafe { slice::from_raw_parts_mut(buf_addr, buf_len as usize) })
            }
            _ => Err(Error::InvalidPort),
        }
    }

    /// Write OOB data from device to host in OOB write buffer
    /// This starts a transfer, upon completion INTWR event on OOB port is triggered
    ///
    /// Length must be between 1 and 73
    pub fn oob_write_data(&mut self, port: usize, length: u8) -> Result<()> {
        // Maximum length of raw OOB = 3 + 5 + 64 + 1
        if (1..73).contains(&length) {
            // SAFETY: Valid length range 1-73 checked previous
            self.info
                .regs
                .port(port)
                .omflen()
                .write(|w| unsafe { w.len().bits(length - 1) });
            self.info.regs.port(port).irulestat().modify(|_, w| w.sstcl().mcudone());
        } else {
            return Err(Error::InvalidParameter);
        }

        Ok(())
    }

    /// Generate WAKE# event to wake Host up from Sx on any
    /// event. Also a general purpose event to wake on Lid switch or
    /// AC insertion.
    ///
    /// If the event occurs while Host is in S0, an SCI is generated
    /// instead.
    ///
    /// wake(true) sets WAKE# signal low to generate WAKE event
    /// wake(false) must be sent to clear WAKE signal does not auto clear
    ///
    /// Active Low.
    ///
    /// Warning: Blocks until DONE bit clears
    pub fn wake(&mut self, set: bool) {
        self.info.regs.wirewo().write(|w| w.waken_scin().variant(!set));
        self.block_for_vwire_done();
    }

    /// Generate PME# event to wake the Host from Sx through PCI PME#.
    ///
    /// pme(true) sets PME# signal low to generate PME event
    /// pme(false) must be sent to clear WAKE signal does not auto clear
    ///
    /// Active Low.
    ///
    /// Warning: Blocks until DONE bit clears
    pub fn pme(&mut self, set: bool) {
        self.info.regs.wirewo().write(|w| w.pmen().variant(!set));
        self.block_for_vwire_done();
    }

    /// Generate SCI# event resulting in ACPI method being invoked by
    /// the OS.
    ///
    /// sci(true) generates SCI# event to host
    /// sci(false) must be called after SCI has been handled
    ///
    /// Active Low.
    ///
    /// Warning: Blocks until DONE bit clears
    pub fn sci(&mut self, set: bool) {
        self.info.regs.wirewo().write(|w| w.scin().variant(!set));
        self.block_for_vwire_done();
    }

    /// Generate SMI# event resulting in SMI code being invoked by the
    /// BIOS.
    ///
    /// smi(true) sets SMI# signal to indicate system management interrupt
    /// smi(false) must be called after SMI event has been handled
    ///
    /// Active Low.
    ///
    /// Warning: Blocks until DONE bit clears
    pub fn smi(&mut self, set: bool) {
        self.info.regs.wirewo().write(|w| w.smin().variant(!set));
        self.block_for_vwire_done();
    }

    /// Generate RCIN# event.
    ///
    /// rcin(true) sets RCIN# on host to request CPU reset
    /// rcin(false) removes the request for CPU reset. Normally CPU and
    /// EC will reset and it is not necessary to set false.
    ///
    /// Active Low.
    ///
    /// Warning: Blocks until DONE bit clears
    pub fn rcin(&mut self, set: bool) {
        self.info.regs.wirewo().write(|w| w.rcinn().variant(!set));
        self.block_for_vwire_done();
    }

    /// Acknowledge Host Reset. Used in response to HOST_RST_WARN.
    ///
    /// Active High
    ///
    /// Warning: Blocks until DONE bit clears
    pub fn host_reset_ack(&mut self) {
        self.info.regs.wirewo().write(|w| w.host_rst_ack().set_bit());
        self.block_for_vwire_done();
    }

    /// Acknowledge Suspend Warn.
    ///
    /// Active Low.
    ///
    /// Warning: Blocks until DONE bit clears
    pub fn suspend_ack(&mut self) {
        self.info.regs.wirewo().write(|w| w.susackn().clear_bit());
        self.block_for_vwire_done();
    }

    /// EC to PCH byte.
    ///
    /// Warning: Blocks until DONE bit clears
    pub fn e2p(&mut self, data: u8) {
        self.info.regs.wirewo().write(|w| unsafe { w.e2p().bits(data) });
        self.block_for_vwire_done();
    }

    /// Sent when EC or BMC has completed its boot process as an
    /// indication to eSPI controller to continue with G3 to S0 exit.
    ///
    /// Active High.
    ///
    /// Warning: Blocks until DONE bit clears
    pub fn boot_done(&mut self) {
        self.info.regs.wirewo().write(|w| w.boot_done().set_bit());
        self.block_for_vwire_done();
    }

    /// If boot ended in success, set to `true`.
    ///
    /// Active High.
    ///
    /// Warning: Blocks until DONE bit clears
    pub fn boot_status(&mut self, status: BootStatus) {
        self.info.regs.wirewo().write(|w| w.boot_errn().variant(status.into()));
        self.block_for_vwire_done();
    }

    /// To be called when Host goes into G3.
    ///
    /// Active High.
    ///
    /// Warning: Blocks until DONE bit clears
    pub fn dsw_pwrok_reset(&mut self) {
        self.info.regs.wirewo().write(|w| w.dsw_pwrok_rst().set_bit());
        self.block_for_vwire_done();
    }

    fn block_for_vwire_done(&self) {
        // No interrupt event available, must busy loop
        while self.info.regs.wirewo().read().done().bit_is_clear() {}
    }

    /// Calls `f` to check if we are ready or not.
    /// If not, `g` is called once the waker is set (to eg enable the required interrupts).
    async fn wait_for<F, U, G>(&mut self, mut f: F, mut g: G) -> U
    where
        F: FnMut(&mut Self) -> Poll<U>,
        G: FnMut(&mut Self),
    {
        poll_fn(|cx| {
            // Register waker before checking condition, to ensure that wakes/interrupts
            // aren't lost between f() and g()
            ESPI_WAKER.register(cx.waker());
            let r = f(self);

            if r.is_pending() {
                g(self);
            }

            r
        })
        .await
    }
}

impl Espi<'_> {
    fn mailbox(
        &mut self,
        port: usize,
        port_type: Type,
        direction: Direction,
        base_sel: BaseOrAsz,
        offset: u16,
        length: Len,
    ) {
        // Set port type,direction and interrupt configuration
        self.info.regs.port(port).cfg().write(|w| {
            w.type_()
                .variant(port_type)
                .direction()
                .variant(direction)
                .mbint_all()
                .set_bit()
        });

        // Set port interrupt rules
        self.info.regs.port(port).irulestat().write(|w| {
            unsafe { w.ustat().bits(0) }
                .interr()
                .set_bit()
                .intrd()
                .set_bit()
                .intwr()
                .set_bit()
                .intspc0()
                .set_bit()
                .intspc1()
                .set_bit()
                .intspc2()
                .set_bit()
                .intspc3()
                .set_bit()
        });

        // Set port mapped address
        self.info
            .regs
            .port(port)
            .addr()
            .write(|w| w.base_or_asz().variant(base_sel));

        // Set port RAM use
        self.info
            .regs
            .port(port)
            .ramuse()
            .write(|w| unsafe { w.off().bits(offset) }.len().variant(length));

        // Enable the port
        self.info.regs.mctrl().modify(|_, w| w.pena(port as u8).enabled());
    }
}

#[derive(Clone, Copy)]
struct Info {
    regs: &'static crate::pac::espi::RegisterBlock,
}

// SAFETY: safety for Send here is the same as the other accessors to unsafe blocks: it must be done from a single executor context.
//         This is a temporary workaround -- a better solution might be to refactor Info to no longer maintain a reference to regs,
//         but instead look up the correct register set and then perform operations within an unsafe block as we do for other peripherals
unsafe impl Send for Info {}

trait SealedInstance {
    fn info() -> Info;
}

/// eSPI instance trait.
#[allow(private_bounds)]
pub trait Instance: SealedInstance + PeripheralType + SysconPeripheral + 'static + Send {
    /// Interrupt for this eSPI instance.
    type Interrupt: interrupt::typelevel::Interrupt;
}

impl Instance for peripherals::ESPI {
    type Interrupt = crate::interrupt::typelevel::ESPI;
}

impl SealedInstance for peripherals::ESPI {
    fn info() -> Info {
        Info {
            // SAFETY: safe from single executor
            regs: unsafe { &*crate::pac::Espi::ptr() },
        }
    }
}

trait SealedPin: Pin {
    fn as_espi(&self, function: Function) {
        self.set_function(function)
            .set_pull(Pull::Up)
            .enable_input_buffer()
            .set_slew_rate(SlewRate::Standard)
            .set_drive_strength(DriveStrength::Normal)
            .disable_analog_multiplex()
            .set_drive_mode(DriveMode::PushPull)
            .set_input_inverter(Inverter::Disabled);
    }
}

macro_rules! pin_traits {
    ($mode:ident, $($pin:ident, $function:ident),*) => {
        paste! {
            /// Select pin mode of operation
            #[allow(private_bounds)]
            pub trait [<$mode:camel Pin>]<T: Instance>: SealedPin + PeripheralType {
                /// Set pin mode of operation
                fn [<as_ $mode>](&self);
            }
        }

	$(
	    paste!{
		impl SealedPin for crate::peripherals::$pin {}

		impl [<$mode:camel Pin>]<crate::peripherals::ESPI> for crate::peripherals::$pin {
		    fn [<as_ $mode>](&self) {
			self.as_espi(Function::$function);
		    }
		}
	    }
	)*
    };
}

pin_traits!(alert, PIO7_24, F6);
pin_traits!(rst, PIO7_25, F6);
pin_traits!(cs, PIO7_26, F6);
pin_traits!(io0, PIO7_27, F6);
pin_traits!(io1, PIO7_28, F6);
pin_traits!(clk, PIO7_29, F6);
pin_traits!(io2, PIO7_30, F6);
pin_traits!(io3, PIO7_31, F6);
