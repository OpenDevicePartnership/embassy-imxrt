//! System Clock Configuration

use embassy_hal_internal::Peri;

use crate::peripherals::{PIO0_24, PIO0_25, PIO1_10, PIO2_15, PIO2_29, PIO2_30};

//
// structs
//

/// The main user-provided configuration
#[derive(Clone, Copy, Debug)]
pub struct ClockConfig {
    /// Clock coming from RTC crystal oscillator
    pub enable_32k_clk: Option<PoweredClock>,
    /// 16MHz clock, generated on-chip, accurate +/- 1%
    pub enable_16m_irc: Option<PoweredClock>,
    /// 1MHz clock, generated on-chip, accurate +/- 10%
    pub enable_1m_lposc: Option<PoweredClock>,
    /// 48MHz/60MHz clock, generated on-chip, accurate +/- 1%
    pub m4860_irc_select: M4860IrcSelect,
    /// 32khz Wake Clock Select
    pub k32_wake_clk_select: K32WakeClkSelect,
    /// Main PLL Configuration
    pub main_pll: Option<MainPll>,
    /// Main Clock Selection
    pub main_clock_select: MainClockSelect,
    /// Main clock divided by (1 + sys_cpu_ahb_div)
    pub sys_cpu_ahb_div: Div8,
    /// Division of FRGPLLCLKDIV, main_pll_clk divided by (1 + frg_clk_pll_div)
    pub frg_clk_pll_div: Option<FrgClockConfig>,
    /// Clock output
    pub clk_out_select: ClockOutSink,
    /// Clock Out Divisor
    pub clk_out_div: Option<Div8>,
}

/// Fractional Rate Generator Clock Configuration
#[derive(Clone, Copy, Debug)]
pub struct FrgClockConfig {
    /// Clock divisor
    pub div: Div8,
    /// Clock power state
    pub powered: PoweredClock,
}

/// This type represents a divider in the range 1..=256.
///
/// At a hardware level, this is an 8-bit register from 0..=255,
/// which adds one.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Div8(pub(super) u8);

/// Main System PLL
///
/// ```text
/// ┌────────────────────────────────────────────────────────────────────────────────────────┐
/// │                                                                                        │
/// │                                                          ┌─────────────┐               │
/// │                                                          │Main PLL     │  main_pll_clk │
/// │                                                   ┌─────▶│Clock Divider│ ────────────▶ │
/// │                                                   │      └─────────────┘               │
/// │                                                   │             ▲                      │
/// │                                                   │             │                      │
/// │                                                   │       MAINPLLCLKDIV                │
/// │                                                   │      ┌─────────────┐               │
/// │                                                   │      │DSP PLL      │   dsp_pll_clk │
/// │                                                   │ ┌───▶│Clock Divider│ ────────────▶ │
/// │                                                   │ │    └─────────────┘               │
/// │                     ┌─────┐       ┌────────────┐  │ │           ▲                      │
/// │         16m_irc ───▶│000  │       │       PFD0 │──┘ │           │                      │
/// │          clk_in ───▶│001  │       │ Main  PFD1 │────┘     DSPPLLCLKDIV                 │
/// │ 48/60m_irc_div2 ───▶│010  │──────▶│ PLL   PFD2 │────┐    ┌─────────────┐               │
/// │          "none" ───▶│111  │       │       PFD3 │───┐│    │AUX0 PLL     │  aux0_pll_clk │
/// │                     └─────┘       └────────────┘   │└───▶│Clock Divider│ ────────────▶ │
/// │                        ▲                 ▲         │     └─────────────┘               │
/// │                        │                 │         │            ▲                      │
/// │            Sys PLL clock select  Main PLL settings │            │                      │
/// │             SYSPLL0CLKSEL[2:0]       SYSPLL0xx     │      AUX0PLLCLKDIV                │
/// │                                                    │     ┌─────────────┐               │
/// │                                                    │     │AUX1 PLL     │  aux1_pll_clk │
/// │                                                    └────▶│Clock Divider│ ────────────▶ │
/// │                                                          └─────────────┘               │
/// │                                                                 ▲                      │
/// │                                                                 │                      │
/// │                                                           AUX1PLLCLKDIV                │
/// │                                                                                        │
/// └────────────────────────────────────────────────────────────────────────────────────────┘
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MainPll {
    /// Clock power state
    pub powered: PoweredClock,
    /// Select the used clock input
    pub clock_select: MainPllClockSelect,
    /// Allowed range: 16..=22
    pub multiplier: u8,
    /// PFD that feeds the `main_pll_clk`.
    /// If None, the pfd is gated and the clock will not be active.
    ///
    /// Allowed range: `12..=35`.
    /// Applied multiplier = `18/div`.
    pub pfd0_div: Option<u8>,
    /// PFD that feeds the `dsp_pll_clk`.
    /// If None, the pfd is gated and the clock will not be active.
    ///
    /// Allowed range: `12..=35`.
    /// Applied multiplier = `18/div`.
    pub pfd1_div: Option<u8>,
    /// PFD that feeds the `aux0_pll_clk`.
    /// If None, the pfd is gated and the clock will not be active.
    ///
    /// Allowed range: `12..=35`.
    /// Applied multiplier = `18/div`.
    pub pfd2_div: Option<u8>,
    /// PFD that feeds the `aux1_pll_clk`.
    /// If None, the pfd is gated and the clock will not be active.
    ///
    /// Allowed range: `12..=35`.
    /// Applied multiplier = `18/div`.
    pub pfd3_div: Option<u8>,
}

//
// enums
//

/// Powered Clock Configuration
///
/// Is this clock high-power only, or high and low power enabled?
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoweredClock {
    /// Clock is powered in normal operation mode, but is disabled
    /// when entering Deep Sleep Mode. It will be re-enabled when
    /// exiting deep sleep mode.
    NormalEnabledDeepSleepDisabled,
    /// Clock is powered in normal operation mode, AND is left
    /// enabled in Deep Sleep Mode.
    AlwaysEnabled,
}

/// ```text
///      16m_irc ┌─────┐                          ┌─────┐
/// ────────────▶│000  │      ┌──────────────────▶│000  │
///       clk_in │     │      │      main_pll_clk │     │
/// ────────────▶│001  │      │      ────────────▶│001  │
///     1m_lposc │     │      │      aux0_pll_clk │     │
/// ────────────▶│010  │      │      ────────────▶│010  │
///   48/60m_irc │     │──────┘       dsp_pll_clk │     │    ┌───────┐
/// ────────────▶│011  │             ────────────▶│011  │    │CLKOUT │    CLKOUT
///     main_clk │     │             aux1_pll_clk │     │───▶│Divider│────────────▶
/// ────────────▶│100  │             ────────────▶│100  │    └───────┘
/// dsp_main_clk │     │            audio_pll_clk │     │        ▲
/// ────────────▶│110  │             ────────────▶│101  │        │
///              └─────┘                  32k_clk │     │    CLKOUTDIV
///                 ▲                ────────────▶│110  │
///                 │                      "none" │     │
///         CLKOUT 0 select          ────────────▶│111  │
///         CLKOUTSEL0[2:0]                       └─────┘
///                                                  ▲
///                                                  │
///                                          CLKOUT 1 select
///                                          CLKOUTSEL1[2:0]
/// ```
#[derive(Copy, Clone, Default, Debug)]
pub enum ClockOutSink {
    /// Sourced from `16m_irc`, internal 16MHz Oscillator "SFRO"
    M16Irc,
    /// Sourced from `clk_in`, external crystal or oscillator
    ClkIn,
    /// Sourced from `1m_lposc`, internal 1MHz Low Power Oscillator
    M1Lposc,
    /// Sourced from `48/60m_irc`, internal 48/60MHz Oscillator "FFRO"
    M4860Irc,
    /// Sourced from `main_clk`, input to the (pre-divided) AHB/HCLK stage
    MainClk,
    /// Sourced from `dsp_main_clk`, input to the (pre-divided) DSP stage
    DspMainClk,
    /// Sourced from `main_pll_clk`, driven by the main system PLL output stage
    /// PFD0 and fed through the Main PLL Clock Divider
    MainPllClk,
    /// Sourced from `aux0_pll_clk`, driven by the main system PLL output stage
    /// PFD2 and fed through the AUX0 PLL Clock Divider
    Aux0PllClk,
    /// Sourced from `dsp_pll_clk`, driven by the main system PLL output stage
    /// PFD1 and fed through the DSP PLL Clock Divider
    DspPllClk,
    /// Sourced from `aux1_pll_clk`, driven by the main system PLL output stage
    /// PFD3 and fed through the AUX1 PLL Clock Divider
    Aux1PllClk,
    /// Sourced from `audio_pll_clk`, driven by the Audio PLL output stage
    /// PDF0 and fed through the Audio PLL Divider
    AudioPllClk,
    /// Sourced from `32k_clk`, the external RTC crystal oscillator
    K32Clk,
    /// Not fed
    #[default]
    None,
}

/// ```text
///                     ┌─────┐
///         16m_irc ───▶│000  │
///          clk_in ───▶│001  │
/// 48/60m_irc_div2 ───▶│010  │──────▶
///          "none" ───▶│111  │
///                     └─────┘
///                        ▲
///                        │
///            Sys PLL clock select
///             SYSPLL0CLKSEL[2:0]
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MainPllClockSelect {
    /// 16MHz internal oscillator
    M16Irc = 0b000,
    /// External clock input
    ClkIn = 0b001,
    /// 48/60MHz internal oscillator
    M4860IrcDiv2 = 0b010,
}

/// ```text
/// clkin (selected by IOCON)          ┌───┐ clk_in
///       ────────────────────────────▶│1  │───────▶
///                ┌────────────┐  ┌──▶│0  │
///  xtalin ──────▶│Main crystal│  │   └───┘
/// xtalout ──────▶│oscillator  │──┘     ▲
///                └────────────┘        │
///                       ▲       SYSOSCBYPASS[2:0]
///                       │
///                Enable & bypass
///                SYSOSCCTL0[1:0]
/// ```
#[derive(Debug, Default)]
pub enum ClkInSelect {
    /// External Crystal
    Xtal {
        /// External Crystal Frequency
        freq: u32,
        /// Enable "bypass"
        bypass: bool,
        /// If true: "Low Power". If false: "High Gain"
        low_power: bool,
        /// Power state
        powered: PoweredClock,
    },
    /// Clock connected to Pin0.25
    ClkIn0_25 {
        /// External clock frequency
        freq: u32,
        /// Clock Pin
        pin: Peri<'static, PIO0_25>,
    },
    /// Clock connected to Pin1.15
    ClkIn2_15 {
        /// External clock frequency
        freq: u32,
        /// Clock Pin
        pin: Peri<'static, PIO2_15>,
    },
    /// Clock connected to Pin2.30
    ClkIn2_30 {
        /// External clock frequency
        freq: u32,
        /// Clock Pin
        pin: Peri<'static, PIO2_30>,
    },
    /// No clock
    #[default]
    None,
}

/// Output pin selection for ClockOut
#[derive(Debug, Default)]
pub enum ClkOutSelect {
    /// Pin0.24 Selected
    ClkOut0_24(Peri<'static, PIO0_24>),
    /// Pin1.10 Selected
    ClkOut1_10(Peri<'static, PIO1_10>),
    /// Pin2.29 Selected
    ClkOut2_29(Peri<'static, PIO2_29>),
    /// None selected
    #[default]
    None,
}

/// ```text
///                      ┌────┐
///  48/60m_irc_div2 ───▶│00  │
///           clk_in ───▶│01  │                      ┌────┐
///         1m_lposc ───▶│10  │─────────────────────▶│00  │
///       48/60m_irc ───▶│11  │         16m_irc ┌───▶│01  │
///                      └────┘    ─────────────┘┌──▶│10  │─────▶
///                         ▲      main_pll_clk  │┌─▶│11  │
///                         │      ──────────────┘│  └────┘
///           Main clock select A       32k_clk   │     ▲
///            MAINCLKSELA[1:0]    ───────────────┘     │
///                                       Main clock select B
///                                        MAINCLKSELB[1:0]
/// ```
// Top 2 bits = MAINCLKSELA
// Bottom 2 bits = MAINCLKSELB
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MainClockSelect {
    /// 48/60MHz Oscillator Divided by 4
    M4860IrcDiv4 = 0b00_00,
    /// Clock In
    ClkIn = 0b01_00,
    /// 1MHz Oscillator
    M1Lposc = 0b10_00,
    /// 48/60MHz Oscillator
    M4860Irc = 0b11_00,
    /// 16MHz Oscillator
    M16Irc = 0b00_01,
    /// Main PLL Clock
    MainPllClk = 0b0010,
    /// 32KHz clock
    K32Clk = 0b0011,
}

/// ```text
///  ┌──────────┐                              48/60m_irc
///  │48/60 MHz │─┬──────────────────────────────────────▶
///  │Oscillator│ │ ┌───────────┐         48/60m_irc_div2
///  └──────────┘ └▶│Divide by 2│────────────────────────▶
///        ▲        └───────────┘         48/60m_irc_div4
///        │              │ ┌───────────┐ ┌──────────────▶
/// PDRUNCFG0[15],        └▶│Divide by 2│─┘
/// PDSLEEPCFG0[15]         └───────────┘
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum M4860IrcSelect {
    /// Clock disabled
    #[default]
    Off,
    /// 48MHz oscillator selected
    Mhz48(PoweredClock),
    /// 60MHz oscillator selected
    Mhz60(PoweredClock),
}

/// ```text
///                                                    1m_lposc
///                   ┌─────────────────────────────────────────▶
///                   │           32k_clk
///                   │           ───────┐
///  ┌──────────┐     │   ┌─────────┐    │  ┌─────┐
///  │1 MHz low │     │   │divide by│    └─▶│000  │ 32k_wake_clk
///  │power osc.│─────┴──▶│   32    │ ─────▶│001  │─────────────▶
///  └──────────┘         └─────────┘    ┌─▶│111  │
///        ▲                      "none" │  └─────┘
///        │                      ───────┘     ▲
/// PDRUNCFG0[14],                             │
/// PDSLEEPCFG0[14]                  WAKECLK32KHZSEL[2:0]
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum K32WakeClkSelect {
    /// No clock selected
    Off = 0b111,
    /// 32KHz Oscillator (external)
    K32Clk = 0b000,
    /// 32KHz Oscillator (1MHz Oscillator / 32)
    K32Lp = 0b001,
}

//
// impls
//

impl PoweredClock {
    /// Does THIS clock meet the power requirements of the OTHER clock?
    pub fn meets_requirement_of(&self, other: &Self) -> bool {
        match (self, other) {
            (PoweredClock::NormalEnabledDeepSleepDisabled, PoweredClock::AlwaysEnabled) => false,
            (PoweredClock::NormalEnabledDeepSleepDisabled, PoweredClock::NormalEnabledDeepSleepDisabled) => true,
            (PoweredClock::AlwaysEnabled, PoweredClock::NormalEnabledDeepSleepDisabled) => true,
            (PoweredClock::AlwaysEnabled, PoweredClock::AlwaysEnabled) => true,
        }
    }
}

impl Div8 {
    /// Store a "raw" divisor value that will divide the source by
    /// `(n + 1)`, e.g. `Div8::from_raw(0)` will divide the source
    /// by 1, and `Div8::from_raw(255)` will divide the source by
    /// 256.
    pub const fn from_raw(n: u8) -> Self {
        Self(n)
    }

    /// Store a specific divisor value that will divide the source
    /// by `n`. e.g. `Div8::from_divisor(1)` will divide the source
    /// by 1, and `Div8::from_divisor(256)` will divide the source
    /// by 256.
    ///
    /// Will return `None` if `n` is not in the range `1..=256`.
    /// Consider [`Self::from_raw`] for an infallible version.
    pub const fn from_divisor(n: u16) -> Option<Self> {
        let Some(n) = n.checked_sub(1) else {
            return None;
        };
        if n > (u8::MAX as u16) {
            return None;
        }
        Some(Self(n as u8))
    }

    /// Convert into "raw" bits form
    #[inline(always)]
    pub const fn into_bits(self) -> u8 {
        self.0
    }

    /// Convert into "divisor" form, as a u32 for convenient frequency math
    #[inline(always)]
    pub const fn into_divisor(self) -> u32 {
        self.0 as u32 + 1
    }
}

impl Default for ClockConfig {
    fn default() -> Self {
        // For the default strategy, we should probably assume as little
        // as possible about the outside world (e.g. what clocks are
        // connected externally), and enable the maximum number of source
        // clocks.
        ClockConfig {
            // Don't assume we have an external 32k clock
            enable_32k_clk: None,
            // Enable 16m osc
            enable_16m_irc: Some(PoweredClock::NormalEnabledDeepSleepDisabled),
            // Enable 1m osc
            enable_1m_lposc: Some(PoweredClock::AlwaysEnabled),
            // Select high speed option
            m4860_irc_select: M4860IrcSelect::Mhz60(PoweredClock::NormalEnabledDeepSleepDisabled),
            // Use the internal osc as the wake clk source
            k32_wake_clk_select: K32WakeClkSelect::K32Lp,
            main_pll: Some(MainPll {
                // Clock power state
                powered: PoweredClock::AlwaysEnabled,
                // Select 48/60 div2, e.g. 30MHz
                clock_select: MainPllClockSelect::M16Irc,
                // 30 x 20: 600MHz
                multiplier: 20,
                // 600 / (18 / 18) = 600MHz
                pfd0_div: Some(18),
                // 600 / (18 / 18) = 600MHz
                pfd1_div: Some(18),
                // 600 / (18 / 18) = 600MHz
                pfd2_div: Some(18),
                // 600 / (18 / 18) = 600MHz
                pfd3_div: Some(18),
            }),
            // Select Main PLL Clock, which is at 300MHz
            main_clock_select: MainClockSelect::MainPllClk,
            // HCLK: (300 / (0 + 1)) = 300MHz
            sys_cpu_ahb_div: const { Div8::from_divisor(1).unwrap() },
            // FRG CLK: (300 / (9 + 1)) = 30MHz
            frg_clk_pll_div: const {
                Some(FrgClockConfig {
                    div: Div8::from_divisor(10).unwrap(),
                    powered: PoweredClock::NormalEnabledDeepSleepDisabled,
                })
            },
            clk_out_select: ClockOutSink::None,
            clk_out_div: None,
        }
    }
}

impl M4860IrcSelect {
    /// Selected frequency
    pub fn freq(&self) -> Option<u32> {
        match self {
            M4860IrcSelect::Off => None,
            M4860IrcSelect::Mhz48(_) => Some(48_000_000),
            M4860IrcSelect::Mhz60(_) => Some(60_000_000),
        }
    }

    /// Returns `true` if the  48 60m irc select is [`Off`].
    ///
    /// [`Off`]: _48_60mIrcSelect::Off
    #[must_use]
    pub fn is_off(&self) -> bool {
        matches!(self, Self::Off)
    }
}

impl K32WakeClkSelect {
    /// Returns `true` if the  32k wake clk select is [`Off`].
    ///
    /// [`Off`]: _32kWakeClkSelect::Off
    #[must_use]
    pub fn is_off(&self) -> bool {
        matches!(self, Self::Off)
    }
}
