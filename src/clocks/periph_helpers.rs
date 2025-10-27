//! Peripheral Clock Helpers
//!
//! This module contains the configuration types and the methods used for applying
//! their configuration via the [`SPConfHelper`] trait

#![allow(dead_code)]

use super::config::PoweredClock;
use super::{ClockError, Clocks};
use crate::pac;

//
// Traits
//

/// Sealed Peripheral Configuration Handler
///
/// Trait for peripheral-specific configuration operations
pub trait SPConfHelper {
    /// This method is called AFTER `T::enable_perph_clock()`, and BEFORE
    /// `T::reset_perph()`.
    fn post_enable_config(&self, clocks: &Clocks) -> Result<u32, ClockError>;
}

//
// Structs and enums
//

/// Flexcomm Fractional Rate Generator Select
#[derive(Debug, Copy, Clone)]
pub enum FlexcommFrgSel {
    /// 0: Main Clock.
    MainClk = 0,
    /// 1: FRG PLL Clock.
    FrgPllClk = 1,
    /// 2: SFRO Clock.
    SfroClk = 2,
    /// 3: FFRO Clock.
    FfroClk = 3,
    /// 7: None, this may be selected in order to reduce power when no output is needed.
    None = 7,
}

/// Flexcomm Functional Clock Select
#[derive(Debug, Copy, Clone)]
pub enum FlexcommFclkSel {
    /// 0: SFRO Clock.
    SfroClk = 0,
    /// 1: FFRO Clock.
    FfroClk = 1,
    /// 2: Audio PLL Clock.
    AudioPllClk = 2,
    /// 3: Master Clock In.
    MasterClk = 3,
    /// 4: FCn FRG Clock.
    FcnFrgClk = 4,
    /// 7: None, this may be selected in order to reduce power when no output is needed.
    None = 7,
}

/// CTimer clock select
#[derive(Debug, Copy, Clone)]
pub enum CTimerSel {
    /// 0: Main Clock.
    MainClk = 0,
    /// 1: SFRO Clock.
    SfroClk = 1,
    /// 2: FFRO Clock.
    FfroClk = 2,
    /// 3: Audio PLL Clock.
    AudioPllClk = 3,
    /// 4: Master Clock In.
    MasterClk = 4,
    /// 5: Low Power Oscillator Clock (LPOSC).
    Lposc = 5,
    /// 7: None, this may be selected in order to reduce power when no output is needed.
    None = 7,
}

/// ADC0 Clock Select
#[derive(Debug, Copy, Clone)]
pub enum AdcSel0 {
    /// 0: SFRO Clock.
    SfroClk,
    /// 1: XTALIN Clock.
    XtalinClk,
    /// 2: Low Power Oscillator Clock (LPOSC).
    Lposc,
    /// 3: FFRO Clock.
    FfroClk,
    /// 7: None, this may be selected in order to reduce power when no output is needed.
    None,
}

/// ADC1 Clock Select
#[derive(Debug, Copy, Clone)]
pub enum AdcSel1 {
    /// 0: ADC0FCLKSEL0 Multiplexed Output.
    Adc0fclksel0MuxOut,
    /// 1: SYSPLL0 MAIN_CLK (PFD0 Output)
    Syspll0MainClk,
    /// 3: SYSPLL0 AUX0_PLL_Clock.
    Syspll0Aux0PllClock,
    /// 5: SYSPLL0 AUX1_PLL_Clock.
    Syspll0Aux1PllClock,
    /// 7: None, this may be selected in order to reduce power when no output is needed.
    None,
}

/// Flexcomm instance index
#[derive(Copy, Clone)]
#[repr(usize)]
pub enum FlexcommInstance {
    Flexcomm0 = 0,
    Flexcomm1 = 1,
    Flexcomm2 = 2,
    Flexcomm3 = 3,
    Flexcomm4 = 4,
    Flexcomm5 = 5,
    Flexcomm6 = 6,
    Flexcomm7 = 7,
}

/// Flexcomm 0..=7 configuration
pub struct FlexcommConfig {
    pub frg_clk_sel: FlexcommFrgSel,
    pub fc_clk_sel: FlexcommFclkSel,
    pub instance: FlexcommInstance,
    pub mult: u8,
    pub powered: PoweredClock,
}

/// Flexcomm14 configuration
pub struct FlexcommConfig14 {
    pub frg_clk_sel: FlexcommFrgSel,
    pub fc_clk_sel: FlexcommFclkSel,
    pub mult: u8,
    pub powered: PoweredClock,
}

/// Flexcomm15 configuration
pub struct FlexcommConfig15 {
    pub frg_clk_sel: FlexcommFrgSel,
    pub fc_clk_sel: FlexcommFclkSel,
    pub mult: u8,
    pub powered: PoweredClock,
}

/// ADC configuration
pub struct AdcConfig {
    pub sel0: AdcSel0,
    pub sel1: AdcSel1,
    pub div: u8,
    pub powered: PoweredClock,
}

/// clock source indicator for selecting while powering on the `SCTimer`
#[derive(Copy, Clone, Debug)]
pub enum SCTClockSource {
    /// main clock
    Main,

    /// main PLL clock (`main_pll_clk`)
    MainPLL,

    /// `aux0_pll_clk`
    Aux0Pll,

    /// `48/60m_irc`
    Ffro48_60Mhz,

    /// `aux1_pll_clk`
    Aux1Pll,

    /// `audio_pll_clk`
    AudioPLL,

    /// lowest power selection
    None,
}

/// SCTimer0 Configuration
pub struct Sct0Config {
    pub source: SCTClockSource,
    pub div: u8,
    pub powered: PoweredClock,
}

/// Watchdog Clock Select
pub enum WdtClkSel {
    LpOsc1m,
    None,
}

/// Watchdog Timer Index
pub enum WdtInstance {
    Wwdt0,
    Wwdt1,
}

/// Watchdog Timer Config
pub struct WdtConfig {
    pub source: WdtClkSel,
    pub instance: WdtInstance,
    pub powered: PoweredClock,
}

/// CTimer Instance
#[derive(Clone, Copy)]
#[repr(usize)]
pub enum CTimerInstance {
    CTimer0 = 0,
    CTimer1 = 1,
    CTimer2 = 2,
    CTimer3 = 3,
    CTimer4 = 4,
}

/// CTimer Config
pub struct CtimerConfig {
    pub source: CTimerSel,
    pub instance: CTimerInstance,
    pub powered: PoweredClock,
}

/// OS Event Clock Select
pub enum OsEventClockSelect {
    /// 0: Low Power Oscillator Clock (LPOSC).
    Lposc,
    /// 1: RTC 32KHz Clock.
    Rtc32khzClk,
    /// 2: Teal Free Running Clock (Global Time Stamping)
    TealFreeRunningClk,
    /// 7: None, this may be selected in order to reduce power when no output is needed.
    None,
}

/// OS Event Timer Config
pub struct OsEventConfig {
    pub select: OsEventClockSelect,
    pub powered: PoweredClock,
}

/// Used when a clock has no upstream clocks that need to be configured or verified.
pub struct NoConfig;

//
// impls
//

impl FlexcommFrgSel {
    fn into_pac(self) -> pac::clkctl1::flexcomm::frgclksel::Sel {
        match self {
            FlexcommFrgSel::MainClk => pac::clkctl1::flexcomm::frgclksel::Sel::MainClk,
            FlexcommFrgSel::FrgPllClk => pac::clkctl1::flexcomm::frgclksel::Sel::FrgPllClk,
            FlexcommFrgSel::SfroClk => pac::clkctl1::flexcomm::frgclksel::Sel::SfroClk,
            FlexcommFrgSel::FfroClk => pac::clkctl1::flexcomm::frgclksel::Sel::FfroClk,
            FlexcommFrgSel::None => pac::clkctl1::flexcomm::frgclksel::Sel::None,
        }
    }

    fn into_pac14(self) -> pac::clkctl1::frg14clksel::Sel {
        match self {
            FlexcommFrgSel::MainClk => pac::clkctl1::frg14clksel::Sel::MainClk,
            FlexcommFrgSel::FrgPllClk => pac::clkctl1::frg14clksel::Sel::FrgPllClk,
            FlexcommFrgSel::SfroClk => pac::clkctl1::frg14clksel::Sel::SfroClk,
            FlexcommFrgSel::FfroClk => pac::clkctl1::frg14clksel::Sel::FfroClk,
            FlexcommFrgSel::None => pac::clkctl1::frg14clksel::Sel::None,
        }
    }

    fn into_pac15(self) -> pac::clkctl1::frg15clksel::Sel {
        match self {
            FlexcommFrgSel::MainClk => pac::clkctl1::frg15clksel::Sel::MainClk,
            FlexcommFrgSel::FrgPllClk => pac::clkctl1::frg15clksel::Sel::FrgPllClk,
            FlexcommFrgSel::SfroClk => pac::clkctl1::frg15clksel::Sel::SfroClk,
            FlexcommFrgSel::FfroClk => pac::clkctl1::frg15clksel::Sel::FfroClk,
            FlexcommFrgSel::None => pac::clkctl1::frg15clksel::Sel::None,
        }
    }
}

impl FlexcommFclkSel {
    fn into_pac(self) -> pac::clkctl1::flexcomm::fcfclksel::Sel {
        match self {
            FlexcommFclkSel::SfroClk => pac::clkctl1::flexcomm::fcfclksel::Sel::SfroClk,
            FlexcommFclkSel::FfroClk => pac::clkctl1::flexcomm::fcfclksel::Sel::FfroClk,
            FlexcommFclkSel::AudioPllClk => pac::clkctl1::flexcomm::fcfclksel::Sel::AudioPllClk,
            FlexcommFclkSel::MasterClk => pac::clkctl1::flexcomm::fcfclksel::Sel::MasterClk,
            FlexcommFclkSel::FcnFrgClk => pac::clkctl1::flexcomm::fcfclksel::Sel::FcnFrgClk,
            FlexcommFclkSel::None => pac::clkctl1::flexcomm::fcfclksel::Sel::None,
        }
    }

    fn into_pac14(self) -> pac::clkctl1::fc14fclksel::Sel {
        match self {
            FlexcommFclkSel::SfroClk => pac::clkctl1::fc14fclksel::Sel::SfroClk,
            FlexcommFclkSel::FfroClk => pac::clkctl1::fc14fclksel::Sel::FfroClk,
            FlexcommFclkSel::AudioPllClk => pac::clkctl1::fc14fclksel::Sel::AudioPllClk,
            FlexcommFclkSel::MasterClk => pac::clkctl1::fc14fclksel::Sel::MasterClk,
            FlexcommFclkSel::FcnFrgClk => pac::clkctl1::fc14fclksel::Sel::FcnFrgClk,
            FlexcommFclkSel::None => pac::clkctl1::fc14fclksel::Sel::None,
        }
    }

    fn into_pac15(self) -> pac::clkctl1::fc15fclksel::Sel {
        match self {
            FlexcommFclkSel::SfroClk => pac::clkctl1::fc15fclksel::Sel::SfroClk,
            FlexcommFclkSel::FfroClk => pac::clkctl1::fc15fclksel::Sel::FfroClk,
            FlexcommFclkSel::AudioPllClk => pac::clkctl1::fc15fclksel::Sel::AudioPllClk,
            FlexcommFclkSel::MasterClk => pac::clkctl1::fc15fclksel::Sel::MasterClk,
            FlexcommFclkSel::FcnFrgClk => pac::clkctl1::fc15fclksel::Sel::FcnFrgClk,
            FlexcommFclkSel::None => pac::clkctl1::fc15fclksel::Sel::None,
        }
    }
}

impl CTimerSel {
    fn into_pac(self) -> pac::clkctl1::ct32bitfclksel::Sel {
        match self {
            CTimerSel::MainClk => pac::clkctl1::ct32bitfclksel::Sel::MainClk,
            CTimerSel::SfroClk => pac::clkctl1::ct32bitfclksel::Sel::SfroClk,
            CTimerSel::FfroClk => pac::clkctl1::ct32bitfclksel::Sel::FfroClk,
            CTimerSel::AudioPllClk => pac::clkctl1::ct32bitfclksel::Sel::AudioPllClk,
            CTimerSel::MasterClk => pac::clkctl1::ct32bitfclksel::Sel::MasterClk,
            CTimerSel::Lposc => pac::clkctl1::ct32bitfclksel::Sel::Lposc,
            CTimerSel::None => pac::clkctl1::ct32bitfclksel::Sel::None,
        }
    }
}

impl AdcSel0 {
    fn into_pac(self) -> pac::clkctl0::adc0fclksel0::Sel {
        match self {
            AdcSel0::SfroClk => pac::clkctl0::adc0fclksel0::Sel::SfroClk,
            AdcSel0::XtalinClk => pac::clkctl0::adc0fclksel0::Sel::XtalinClk,
            AdcSel0::Lposc => pac::clkctl0::adc0fclksel0::Sel::Lposc,
            AdcSel0::FfroClk => pac::clkctl0::adc0fclksel0::Sel::FfroClk,
            AdcSel0::None => pac::clkctl0::adc0fclksel0::Sel::None,
        }
    }
}

impl AdcSel1 {
    fn into_pac(self) -> pac::clkctl0::adc0fclksel1::Sel {
        match self {
            AdcSel1::Adc0fclksel0MuxOut => pac::clkctl0::adc0fclksel1::Sel::Adc0fclksel0MuxOut,
            AdcSel1::Syspll0MainClk => pac::clkctl0::adc0fclksel1::Sel::Syspll0MainClk,
            AdcSel1::Syspll0Aux0PllClock => pac::clkctl0::adc0fclksel1::Sel::Syspll0Aux0PllClock,
            AdcSel1::Syspll0Aux1PllClock => pac::clkctl0::adc0fclksel1::Sel::Syspll0Aux1PllClock,
            AdcSel1::None => pac::clkctl0::adc0fclksel1::Sel::None,
        }
    }
}

impl SPConfHelper for FlexcommConfig {
    //                                          16m_clk_irc ┌─────┐
    //                                           ──────────▶│000  │
    //                                           48/60m_irc │     │
    //                                           ──────────▶│001  │
    //   main_clk ┌─────┐                     audio_pll_clk │     │
    // ──────────▶│000  │                        ──────────▶│010  │ function clock
    //    frg_pll │     │                           mclk_in │     │────────────────▶
    // ──────────▶│001  │     ┌───────────────┐  ──────────▶│011  │  of Flexcomm n
    //    16m_irc │     │     │Fractional Rate│   frg_clk n │     │
    // ──────────▶│010  │────▶│Divider (FRG)  │────────────▶│100  │
    // 48/60m_irc │     │     └───────────────┘       "none"│     │
    // ──────────▶│011  │             ▲          ──────────▶│111  │
    //     "none" │     │             │                     └─────┘
    // ──────────▶│111  │       FRGnCTL[15:0]                  ▲
    //            └─────┘                                      │
    //               ▲                             Flexcomm n clock select
    //               │                                 FCnFCLKSEL[2:0]
    //       FRG clock select n
    //        FRGnCLKSEL[2:0]
    fn post_enable_config(&self, clocks: &Clocks) -> Result<u32, ClockError> {
        let clkctl1 = unsafe { pac::Clkctl1::steal() };
        let fcomm = clkctl1.flexcomm(self.instance as usize);
        let freq = match self.fc_clk_sel {
            FlexcommFclkSel::FcnFrgClk => {
                let freq = match self.frg_clk_sel {
                    FlexcommFrgSel::MainClk => clocks.main_clk,
                    FlexcommFrgSel::FrgPllClk => clocks.ensure_frg_pll_active(&self.powered)?,
                    FlexcommFrgSel::SfroClk => clocks.ensure_16mhz_sfro_active(&self.powered)?,
                    FlexcommFrgSel::FfroClk => clocks.ensure_48_60mhz_ffro_active(&self.powered)?,
                    FlexcommFrgSel::None => 0,
                };
                fcomm
                    .frgclksel()
                    .modify(|_r, w| w.sel().variant(self.frg_clk_sel.into_pac()));

                // Flexcomm Interface function clock = (clock selected via FRGCLKSEL) / (1 + MULT / DIV)
                fcomm.frgctl().modify(|_r, w| unsafe {
                    w.mult().bits(self.mult);
                    w.div().bits(0xFF);
                    w
                });

                // Since we fix div to 0xFF (256), this then becomes:
                //
                //              CLK                 CLK
                // FOUT = ---------------- => --------------------------
                //        (1 + (MULT/DIV))    ((256 / 256) + (MULT/256))
                //
                //              CLK                256 * CLK
                // FOUT = ------------------ => ---------------
                //        (256 + MULT) / 256      (256 + MULT)
                //
                // FOUT = (CLK * 256) / (256 + MULT)
                //
                // There's probably a smarter way to do this (w/o u64 math),
                // honestly maybe just floats? we have a hardware floating point.
                let freq = freq as u64;
                let freq = freq * 256u64;
                let fdiv = self.mult as u64 + 256u64;
                let freq = freq / fdiv;
                freq as u32
            }
            FlexcommFclkSel::SfroClk => clocks.ensure_16mhz_sfro_active(&self.powered)?,
            FlexcommFclkSel::FfroClk => clocks.ensure_48_60mhz_ffro_active(&self.powered)?,
            FlexcommFclkSel::AudioPllClk => return Err(ClockError::prog_err("not implemented")),
            FlexcommFclkSel::MasterClk => return Err(ClockError::prog_err("not implemented")),
            FlexcommFclkSel::None => 0,
        };
        fcomm
            .fcfclksel()
            .modify(|_r, w| w.sel().variant(self.fc_clk_sel.into_pac()));
        Ok(freq)
    }
}

impl SPConfHelper for FlexcommConfig14 {
    /// ```rust
    ///                                          16m_clk_irc ┌─────┐
    ///                                           ──────────▶│000  │
    ///                                           48/60m_irc │     │
    ///                                           ──────────▶│001  │
    ///   main_clk ┌─────┐                     audio_pll_clk │     │
    /// ──────────▶│000  │                        ──────────▶│010  │ function clock
    ///    frg_pll │     │                           mclk_in │     │────────────────▶
    /// ──────────▶│001  │     ┌───────────────┐  ──────────▶│011  │    of HS SPI
    ///    16m_irc │     │     │Fractional Rate│   frg_clk14 │     │
    /// ──────────▶│010  │────▶│Divider (FRG)  │────────────▶│100  │
    /// 48/60m_irc │     │     └───────────────┘       "none"│     │
    /// ──────────▶│011  │             ▲          ──────────▶│111  │
    ///     "none" │     │             │                     └─────┘
    /// ──────────▶│111  │       FRG14CTL[15:0]                 ▲
    ///            └─────┘                                      │
    ///               ▲                               HS SPI clock select
    ///               │                                 FC14FCLKSEL[2:0]
    ///    HS SPI FRG clock select
    ///       FRG14CLKSEL[2:0]
    /// ```
    fn post_enable_config(&self, clocks: &Clocks) -> Result<u32, ClockError> {
        let clkctl1 = unsafe { pac::Clkctl1::steal() };
        let freq = match self.fc_clk_sel {
            FlexcommFclkSel::FcnFrgClk => {
                let freq = match self.frg_clk_sel {
                    FlexcommFrgSel::MainClk => clocks.main_clk,
                    FlexcommFrgSel::FrgPllClk => clocks.ensure_frg_pll_active(&self.powered)?,
                    FlexcommFrgSel::SfroClk => clocks.ensure_16mhz_sfro_active(&self.powered)?,
                    FlexcommFrgSel::FfroClk => clocks.ensure_48_60mhz_ffro_active(&self.powered)?,
                    FlexcommFrgSel::None => 0,
                };
                clkctl1
                    .frg14clksel()
                    .modify(|_r, w| w.sel().variant(self.frg_clk_sel.into_pac14()));

                // Flexcomm Interface function clock = (clock selected via FRGCLKSEL) / (1 + MULT / DIV)
                clkctl1.frg14ctl().modify(|_r, w| unsafe {
                    w.mult().bits(self.mult);
                    w.div().bits(0xFF);
                    w
                });

                // Since we fix div to 0xFF (256), this then becomes:
                //
                //              CLK                 CLK
                // FOUT = ---------------- => --------------------------
                //        (1 + (MULT/DIV))    ((256 / 256) + (MULT/256))
                //
                //              CLK                256 * CLK
                // FOUT = ------------------ => ---------------
                //        (256 + MULT) / 256      (256 + MULT)
                //
                // FOUT = (CLK * 256) / (256 + MULT)
                //
                // There's probably a smarter way to do this (w/o u64 math),
                // honestly maybe just floats? we have a hardware floating point.
                let freq = freq as u64;
                let freq = freq * 256u64;
                let fdiv = self.mult as u64 + 256u64;
                let freq = freq / fdiv;
                freq as u32
            }
            FlexcommFclkSel::SfroClk => clocks.ensure_16mhz_sfro_active(&self.powered)?,
            FlexcommFclkSel::FfroClk => clocks.ensure_48_60mhz_ffro_active(&self.powered)?,
            FlexcommFclkSel::AudioPllClk => return Err(ClockError::prog_err("not implemented")),
            FlexcommFclkSel::MasterClk => return Err(ClockError::prog_err("not implemented")),
            FlexcommFclkSel::None => 0,
        };
        clkctl1
            .fc14fclksel()
            .modify(|_r, w| w.sel().variant(self.fc_clk_sel.into_pac14()));
        Ok(freq)
    }
}

impl SPConfHelper for FlexcommConfig15 {
    /// ```text
    ///                                          16m_clk_irc ┌─────┐
    ///                                           ──────────▶│000  │
    ///                                           48/60m_irc │     │
    ///                                           ──────────▶│001  │
    ///   main_clk ┌─────┐                     audio_pll_clk │     │
    /// ──────────▶│000  │                        ──────────▶│010  │ function clock
    ///    frg_pll │     │                           mclk_in │     │────────────────▶
    /// ──────────▶│001  │     ┌───────────────┐  ──────────▶│011  │   of PMIC I2C
    ///    16m_irc │     │     │Fractional Rate│   frg_clk14 │     │
    /// ──────────▶│010  │────▶│Divider (FRG)  │────────────▶│100  │
    /// 48/60m_irc │     │     └───────────────┘       "none"│     │
    /// ──────────▶│011  │             ▲          ──────────▶│111  │
    ///     "none" │     │             │                     └─────┘
    /// ──────────▶│111  │       FRG15CTL[15:0]                 ▲
    ///            └─────┘                                      │
    ///               ▲                              PMIC I2C clock select
    ///               │                                 FC15FCLKSEL[2:0]
    ///   PMIC I2C FRG clock select
    ///       FRG15CLKSEL[2:0]
    /// ```
    fn post_enable_config(&self, clocks: &Clocks) -> Result<u32, ClockError> {
        let clkctl1 = unsafe { pac::Clkctl1::steal() };
        let freq = match self.fc_clk_sel {
            FlexcommFclkSel::FcnFrgClk => {
                let freq = match self.frg_clk_sel {
                    FlexcommFrgSel::MainClk => clocks.main_clk,
                    FlexcommFrgSel::FrgPllClk => clocks.ensure_frg_pll_active(&self.powered)?,
                    FlexcommFrgSel::SfroClk => clocks.ensure_16mhz_sfro_active(&self.powered)?,
                    FlexcommFrgSel::FfroClk => clocks.ensure_48_60mhz_ffro_active(&self.powered)?,
                    FlexcommFrgSel::None => 0,
                };
                clkctl1
                    .frg15clksel()
                    .modify(|_r, w| w.sel().variant(self.frg_clk_sel.into_pac15()));

                // Flexcomm Interface function clock = (clock selected via FRGCLKSEL) / (1 + MULT / DIV)
                clkctl1.frg15ctl().modify(|_r, w| unsafe {
                    w.mult().bits(self.mult);
                    w.div().bits(0xFF);
                    w
                });

                // Since we fix div to 0xFF (256), this then becomes:
                //
                //              CLK                 CLK
                // FOUT = ---------------- => --------------------------
                //        (1 + (MULT/DIV))    ((256 / 256) + (MULT/256))
                //
                //              CLK                256 * CLK
                // FOUT = ------------------ => ---------------
                //        (256 + MULT) / 256      (256 + MULT)
                //
                // FOUT = (CLK * 256) / (256 + MULT)
                //
                // There's probably a smarter way to do this (w/o u64 math),
                // honestly maybe just floats? we have a hardware floating point.
                let freq = freq as u64;
                let freq = freq * 256u64;
                let fdiv = self.mult as u64 + 256u64;
                let freq = freq / fdiv;
                freq as u32
            }
            FlexcommFclkSel::SfroClk => clocks.ensure_16mhz_sfro_active(&self.powered)?,
            FlexcommFclkSel::FfroClk => clocks.ensure_48_60mhz_ffro_active(&self.powered)?,
            FlexcommFclkSel::AudioPllClk => return Err(ClockError::prog_err("not implemented")),
            FlexcommFclkSel::MasterClk => return Err(ClockError::prog_err("not implemented")),
            FlexcommFclkSel::None => 0,
        };
        clkctl1
            .fc15fclksel()
            .modify(|_r, w| w.sel().variant(self.fc_clk_sel.into_pac15()));
        Ok(freq)
    }
}

impl SPConfHelper for AdcConfig {
    /// ```text
    ///    16m_irc ┌─────┐                      ┌─────┐
    /// ──────────▶│000  │    ┌────────────────▶│000  │
    ///     clk_in │     │    │     main_pll_clk│     │
    /// ──────────▶│001  │    │      ──────────▶│001  │        ┌─────────┐
    ///   1m_lposc │     │    │     aux0_pll_clk│     │        │ADC Clock│ to ADC
    /// ──────────▶│010  │────┘      ──────────▶│010  │───────▶│Divider  │───────▶
    /// 48/60m_irc │     │          aux1_pll_clk│     │        └─────────┘  fclk
    /// ──────────▶│011  │           ──────────▶│011  │             ▲
    ///    "none"  │     │              "none"  │     │             │
    /// ──────────▶│111  │           ──────────▶│111  │       ADC0FCLKDIV
    ///            └─────┘                      └─────┘
    ///               ▲                            ▲
    ///               │                            │
    ///      ADC clock select 0           ADC clock select 1
    ///       ADC0FCLKSEL0[2:0]            ADC0FCLKSEL1[2:0]
    /// ```
    fn post_enable_config(&self, clocks: &Clocks) -> Result<u32, ClockError> {
        let clkctl0 = unsafe { pac::Clkctl0::steal() };
        let mut freq = match self.sel1 {
            AdcSel1::Adc0fclksel0MuxOut => {
                let freq = match self.sel0 {
                    AdcSel0::SfroClk => clocks.ensure_16mhz_sfro_active(&self.powered)?,
                    AdcSel0::XtalinClk => clocks.ensure_clk_in_active(&self.powered)?,
                    AdcSel0::Lposc => clocks.ensure_1mhz_lposc_active(&self.powered)?,
                    AdcSel0::FfroClk => clocks.ensure_48_60mhz_ffro_active(&self.powered)?,
                    AdcSel0::None => 0,
                };
                clkctl0
                    .adc0fclksel0()
                    .modify(|_r, w| w.sel().variant(self.sel0.into_pac()));
                freq
            }
            AdcSel1::Syspll0MainClk => clocks.main_clk,
            AdcSel1::Syspll0Aux0PllClock => clocks.ensure_aux0_pll_clk_active(&self.powered)?,
            AdcSel1::Syspll0Aux1PllClock => clocks.ensure_aux1_pll_clk_active(&self.powered)?,
            AdcSel1::None => 0,
        };
        // If we don't use select 0 at all, mark it to none.
        if !matches!(self.sel1, AdcSel1::Adc0fclksel0MuxOut) {
            clkctl0.adc0fclksel0().modify(|_r, w| w.sel().none());
        }
        clkctl0
            .adc0fclksel1()
            .modify(|_r, w| w.sel().variant(self.sel1.into_pac()));

        clkctl0
            .adc0fclkdiv()
            .modify(|_, w| w.halt().set_bit().reset().set_bit());
        // SAFETY: safe as long as the above is still true
        clkctl0.adc0fclkdiv().modify(|_, w| unsafe { w.div().bits(self.div) });
        clkctl0.adc0fclkdiv().modify(|_, w| w.halt().clear_bit());
        while clkctl0.adc0fclkdiv().read().reqflag().bit_is_set() {}

        freq /= 1u32 + self.div as u32;

        Ok(freq)
    }
}

impl SPConfHelper for Sct0Config {
    /// ```text
    ///     main clk ┌─────┐
    /// ────────────▶│000  │
    /// main_pll_clk │     │
    /// ────────────▶│001  │
    /// aux0_pll_clk │     │
    /// ────────────▶│010  │        ┌─────────────┐
    ///   48/60m_irc │     │        │SCTimer/PWM  │ to SCTimer/PWM
    /// ────────────▶│011  │───────▶│Clock Divider│───────────────▶
    /// aux1_pll_clk │     │        └─────────────┘  input clock 7
    /// ────────────▶│100  │               ▲
    ///audio_pll_clk │     │               │
    /// ────────────▶│101  │           SCTFCLKDIV
    ///       "none" │     │
    /// ────────────▶│111  │
    ///              └─────┘
    ///                 ▲
    ///                 │
    ///     SCTimer/PWM clock select
    ///         SCTFCLKSEL[2:0]
    /// ```
    fn post_enable_config(&self, clocks: &Clocks) -> Result<u32, ClockError> {
        let clkctl0 = unsafe { pac::Clkctl0::steal() };
        let mut freq = match self.source {
            SCTClockSource::Main => {
                // main_clk is ALWAYS enabled.
                clkctl0.sctfclksel().write(|w| w.sel().main_clk());
                clocks.main_clk
            }
            SCTClockSource::MainPLL => {
                // main_pll_may not be enabled
                let freq = clocks.ensure_main_pll_clk_active(&self.powered)?;
                clkctl0.sctfclksel().write(|w| w.sel().main_sys_pll_clk());
                freq
            }
            SCTClockSource::Aux0Pll => {
                // aux0_pll_clk may not be enabled
                let freq = clocks.ensure_aux0_pll_clk_active(&self.powered)?;
                clkctl0.sctfclksel().write(|w| w.sel().syspll0_aux0_pll_clock());
                freq
            }
            SCTClockSource::Ffro48_60Mhz => {
                // FFRO/48_60mhz may not be enabled
                let freq = clocks.ensure_48_60mhz_ffro_active(&self.powered)?;
                clkctl0.sctfclksel().write(|w| w.sel().ffro_clk());
                freq
            }
            SCTClockSource::Aux1Pll => {
                // aux1_pll_clk may not be enabled
                let freq = clocks.ensure_aux1_pll_clk_active(&self.powered)?;
                clkctl0.sctfclksel().write(|w| w.sel().syspll0_aux1_pll_clock());
                freq
            }
            SCTClockSource::AudioPLL => {
                // clkctl0.sctfclksel().write(|w| w.sel().audio_pll_clk());
                return Err(ClockError::prog_err("audio pll not yet supported"));
            }
            SCTClockSource::None => {
                clkctl0.sctfclksel().write(|w| w.sel().none());
                0
            }
        };

        if !matches!(self.source, SCTClockSource::None) {
            clkctl0.sctfclkdiv().modify(|_, w| w.halt().set_bit().reset().set_bit());
            // SAFETY: safe as long as the above is still true
            clkctl0.sctfclkdiv().modify(|_, w| unsafe { w.div().bits(self.div) });
            clkctl0.sctfclkdiv().modify(|_, w| w.halt().clear_bit());
            while clkctl0.sctfclkdiv().read().reqflag().bit_is_set() {}

            freq /= 1u32 + self.div as u32;
        }

        Ok(freq)
    }
}

impl SPConfHelper for WdtConfig {
    /// ```text
    ///   1m_lposc ┌─────┐
    /// ──────────▶│000  │ to WDTn
    ///     "none" │     │────────▶
    /// ──────────▶│111  │   fclk
    ///            └─────┘
    ///               ▲
    ///               │
    ///       WDTn Clock Select
    ///       WDTnFCLKSEL[2:0]
    /// ```
    fn post_enable_config(&self, clocks: &Clocks) -> Result<u32, ClockError> {
        let freq = match self.source {
            WdtClkSel::LpOsc1m => clocks.ensure_1mhz_lposc_active(&self.powered)?,
            // TODO: Should we allow "None" settings? This seems a little foot-gunny.
            WdtClkSel::None => 0,
        };
        match self.instance {
            WdtInstance::Wwdt0 => {
                let clkctl0 = unsafe { pac::Clkctl0::steal() };
                clkctl0.wdt0fclksel().modify(|_r, w| match self.source {
                    WdtClkSel::LpOsc1m => w.sel().lposc(),
                    WdtClkSel::None => w.sel().none(),
                });
            }
            WdtInstance::Wwdt1 => {
                let clkctl1 = unsafe { pac::Clkctl1::steal() };
                clkctl1.wdt1fclksel().modify(|_r, w| match self.source {
                    WdtClkSel::LpOsc1m => w.sel().lposc(),
                    WdtClkSel::None => w.sel().none(),
                });
            }
        }
        Ok(freq)
    }
}

impl SPConfHelper for CtimerConfig {
    /// ```text
    ///     main clk ┌─────┐
    /// ────────────▶│000  │
    ///      16m_irc │     │
    /// ────────────▶│001  │
    ///   48/60m_irc │     │ function clock of
    /// ────────────▶│010  │     CTIMER n
    ///audio_pll_clk │     │──────────────────▶
    /// ────────────▶│011  │ CTIMERs 0 thru 4
    ///      mclk_in │     │
    /// ────────────▶│100  │
    ///       "none" │     │
    /// ────────────▶│111  │
    ///              └─────┘
    ///                 ▲
    ///                 │
    ///       TIMER n clock select
    ///       CT32BITnFCLKSEL[2:0]
    /// ```
    fn post_enable_config(&self, clocks: &Clocks) -> Result<u32, ClockError> {
        let clkctl1 = unsafe { pac::Clkctl1::steal() };
        let freq = match self.source {
            CTimerSel::MainClk => clocks.main_clk,
            CTimerSel::SfroClk => clocks.ensure_16mhz_sfro_active(&self.powered)?,
            CTimerSel::FfroClk => clocks.ensure_48_60mhz_ffro_active(&self.powered)?,
            CTimerSel::AudioPllClk => return Err(ClockError::prog_err("not implemented")),
            CTimerSel::MasterClk => return Err(ClockError::prog_err("not implemented")),
            CTimerSel::Lposc => clocks.ensure_1mhz_lposc_active(&self.powered)?,
            CTimerSel::None => 0,
        };
        clkctl1
            .ct32bitfclksel(self.instance as usize)
            .modify(|_r, w| w.sel().variant(self.source.into_pac()));
        Ok(freq)
    }
}

impl SPConfHelper for NoConfig {
    fn post_enable_config(&self, _clocks: &Clocks) -> Result<u32, ClockError> {
        // TODO: do we want this to be an Option, or an associated type?
        // For "NoConfig" items, we generally don't track/encode their
        // upstream source, it is often AHB/APB clocks, but I'm not sure
        // if this is ALWAYS true.
        Ok(0)
    }
}

impl SPConfHelper for OsEventConfig {
    /// ```text
    ///     1m_lposc ┌─────┐
    /// ────────────▶│000  │
    ///      32k_clk │     │
    /// ────────────▶│001  │ ostimer_clk
    ///         hclk │     │────────────▶
    /// ────────────▶│010  │
    ///       "none" │     │
    /// ────────────▶│111  │
    ///              └─────┘
    ///                 ▲
    ///                 │
    ///      OS Timer Clock Select
    ///       OSEVENTTFCLKSEL[2:0]
    /// ```
    fn post_enable_config(&self, clocks: &Clocks) -> Result<u32, ClockError> {
        let clkctl1 = unsafe { pac::Clkctl1::steal() };
        let (freq, variant) = match self.select {
            OsEventClockSelect::Lposc => {
                let freq = clocks.ensure_1mhz_lposc_active(&self.powered)?;
                let var = pac::clkctl1::oseventfclksel::Sel::Lposc;
                (freq, var)
            }
            OsEventClockSelect::Rtc32khzClk => {
                let freq = clocks.ensure_32k_clk_active(&self.powered)?;
                let var = pac::clkctl1::oseventfclksel::Sel::Rtc32khzClk;
                (freq, var)
            }
            OsEventClockSelect::TealFreeRunningClk => {
                let freq = clocks.sys_cpu_ahb_clk;
                let var = pac::clkctl1::oseventfclksel::Sel::TealFreeRunningClk;
                (freq, var)
            }
            OsEventClockSelect::None => {
                let freq = 0;
                let var = pac::clkctl1::oseventfclksel::Sel::None;
                (freq, var)
            }
        };
        clkctl1.oseventfclksel().modify(|_r, w| w.sel().variant(variant));
        Ok(freq)
    }
}

/// Placeholder Config for peripherals that are not implemented yet, but definitely
/// require some kind of "pre-flight check" to ensure upstream clocks are enabled and
/// select/divs are made.
pub(super) mod sealed {
    use super::SPConfHelper;
    use crate::clocks::{ClockError, Clocks};

    pub struct UnimplementedConfig;
    impl SPConfHelper for UnimplementedConfig {
        fn post_enable_config(&self, _clocks: &Clocks) -> Result<u32, ClockError> {
            Err(ClockError::prog_err("peripheral not implemented"))
        }
    }
}
