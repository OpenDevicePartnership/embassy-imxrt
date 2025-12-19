//! This module provides voltage scaling and frequency management for iMX RT600 series MCUs.
//! It includes lookup tables for supported CPU and DSP frequencies at different voltage levels,
//! and functions to calculate appropriate LDO voltage settings based on target frequencies.
//!
//! Portions
//! * Copyright 2018-2021, 2023 NXP
//! * All rights reserved.
//! *
//! * SPDX-License-Identifier: BSD-3-Clause

use core::sync::atomic::{AtomicU32, Ordering};

// Constants
const MEGA: u32 = 1_000_000;

// Frequency tables (equivalent dimensions as C arrays)
/// CM33 low voltage frequency levels [temp_range][level]
pub const POWER_LOW_CM33_FREQ_LEVEL: [[u32; 3]; 2] =
    [[220 * MEGA, 150 * MEGA, 70 * MEGA], [215 * MEGA, 140 * MEGA, 60 * MEGA]];

/// DSP low voltage frequency levels [temp_range][level]
pub const POWER_LOW_DSP_FREQ_LEVEL: [[u32; 3]; 2] = [
    [375 * MEGA, 260 * MEGA, 115 * MEGA],
    [355 * MEGA, 235 * MEGA, 95 * MEGA],
];

/// CM33 full voltage frequency levels [temp_range][level]
pub const POWER_FULL_CM33_FREQ_LEVEL: [[u32; 5]; 2] = [
    [300 * MEGA, 275 * MEGA, 210 * MEGA, 140 * MEGA, 65 * MEGA],
    [300 * MEGA, 270 * MEGA, 200 * MEGA, 135 * MEGA, 50 * MEGA],
];

/// DSP full voltage frequency levels [temp_range][level]
pub const POWER_FULL_DSP_FREQ_LEVEL: [[u32; 5]; 2] = [
    [600 * MEGA, 480 * MEGA, 300 * MEGA, 195 * MEGA, 70 * MEGA],
    [550 * MEGA, 440 * MEGA, 285 * MEGA, 170 * MEGA, 55 * MEGA],
];

/// LDO voltage levels for frequency thresholds
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LDOVoltLevel {
    /// 1.13V LDO setting
    Ldo1p13v = 0x32,
    /// 1.0V LDO setting
    Ldo1p0v = 0x26,
    /// 0.9V LDO setting
    Ldo0p9v = 0x1D,
    /// 0.8V LDO setting
    Ldo0p8v = 0x13,
    /// 0.7V LDO setting
    Ldo0p7v = 0x0A,
}

const POWER_LDO_VOLT_LEVEL: [LDOVoltLevel; 5] = [
    LDOVoltLevel::Ldo1p13v,
    LDOVoltLevel::Ldo1p0v,
    LDOVoltLevel::Ldo0p9v,
    LDOVoltLevel::Ldo0p8v,
    LDOVoltLevel::Ldo0p7v,
];

/// Sentinel for invalid/unsupported voltage level
pub const POWER_INVALID_VOLT_LEVEL: u32 = 0xFFFFFFFF;

// Global (simulated) state variables from the C file
static OSC_SETTLING_TIME: AtomicU32 = AtomicU32::new(0);
static PMIC_VDDCORE_RECOVERY_TIME: AtomicU32 = AtomicU32::new(0);
static LVD_CHANGE_FLAG: AtomicU32 = AtomicU32::new(0);

// Public setters mirroring the C APIs
/// Set oscillator settling time (µs)
pub fn update_osc_settling_time(us: u32) {
    OSC_SETTLING_TIME.store(us, Ordering::SeqCst);
}

/// Set PMIC VDDCORE recovery time (µs)
pub fn update_pmic_recovery_time(us: u32) {
    PMIC_VDDCORE_RECOVERY_TIME.store(us, Ordering::SeqCst);
}

/// Disables the Low Voltage Detector (LVD), saving its state.
pub fn disable_lvd(pmc: &crate::pac::Pmc) {
    let ctrl = pmc.ctrl().read().bits();
    const LVD_MASK: u32 = 0x0000_0300; // LVDCORERE_MASK | LVDCOREIE_MASK

    if (ctrl & LVD_MASK) != 0 {
        LVD_CHANGE_FLAG.store(ctrl & LVD_MASK, Ordering::SeqCst);
        pmc.ctrl().modify(|r, w| unsafe { w.bits(r.bits() & !LVD_MASK) });
    }
}

/// Restores the Low Voltage Detector (LVD) to its previous state.
pub fn restore_lvd(pmc: &crate::pac::Pmc) {
    let flags = LVD_CHANGE_FLAG.load(Ordering::SeqCst);
    if flags != 0 {
        pmc.ctrl().modify(|r, w| unsafe { w.bits(r.bits() | flags) });
        LVD_CHANGE_FLAG.store(0, Ordering::SeqCst);
    }
}

/// Applies PMC power domain config changes, waiting for FSM idle.
pub fn apply_pd(pmc: &crate::pac::Pmc) {
    // Cannot set APPLYCFG when ACTIVEFSM is 1
    while pmc.status().read().activefsm().bit_is_set() {}

    // Set APPLYCFG bit
    pmc.ctrl().modify(|_, w| w.applycfg().set_bit());

    // Wait all PMC finite state machines finished
    while pmc.status().read().activefsm().bit_is_set() {}
}

/// Body bias mode for power management
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BodyBiasMode {
    /// Forward Body Bias - increases performance, higher leakage
    Fbb = 1,
    /// Reverse Body Bias - reduces leakage, lower performance
    Rbb = 2,
    /// No Body Bias - neutral mode
    Nbb = 3,
}

/// Returns the current body bias mode.
pub fn get_body_bias_mode(pmc: &crate::pac::Pmc) -> BodyBiasMode {
    let runctrl = pmc.runctrl().read().bits();
    let bias_bits = (runctrl >> 13) & 0b11; // Extract bits 13-14

    match bias_bits {
        0b10 => BodyBiasMode::Fbb, // FBB bit set (bit 14)
        0b01 => BodyBiasMode::Rbb, // RBB bit set (bit 13)
        _ => BodyBiasMode::Nbb,    // Both cleared or invalid
    }
}

/// Enter Forward Body Bias (FBB) mode
///
/// FBB increases performance at the cost of higher leakage power.
/// This function sets the chip to sleep to safely switch body bias modes then wakes again.
///
/// # Important
/// This function uses WFI (Wait For Interrupt) and manipulates power domain configurations.
pub fn enter_fbb(pmc: &crate::pac::Pmc) {
    use cortex_m::peripheral::SCB;

    critical_section::with(|_cs| {
        // # Safety: We're in a critical section
        let sysctl0 = unsafe { crate::pac::Sysctl0::steal() };
        let scb = unsafe { &*SCB::PTR };

        // Save current PMC CTRL state
        let pmc_ctrl = pmc.ctrl().read().bits();

        // Enable deep sleep mode (set SLEEPDEEP bit in SCR)
        const SCB_SCR_SLEEPDEEP: u32 = 1 << 2;
        // # Safety: Unsafe required to modify SCR register to set SLEEPDEEP bit
        unsafe { scb.scr.modify(|v| v | SCB_SCR_SLEEPDEEP) };

        // Configure power domains for sleep: MAINCLK_SHUTOFF=1, FBB_PD=0 (keep FBB powered)
        let pdsleepcfg0 = (sysctl0.pdruncfg0().read().bits()
            | (1 << 20)) // MAINCLK_SHUTOFF_MASK
            & !(1 << 17); // ~FBB_PD_MASK - keep FBB powered during sleep

        sysctl0.pdsleepcfg0().write(|w| unsafe { w.bits(pdsleepcfg0) });
        sysctl0
            .pdsleepcfg1()
            .write(|w| unsafe { w.bits(sysctl0.pdruncfg1().read().bits()) });
        sysctl0
            .pdsleepcfg2()
            .write(|w| unsafe { w.bits(sysctl0.pdruncfg2().read().bits()) });
        sysctl0
            .pdsleepcfg3()
            .write(|w| unsafe { w.bits(sysctl0.pdruncfg3().read().bits()) });

        // PDWAKECFG: Keep FBB state after wake (FBBKEEPST_MASK = bit 17)
        sysctl0.pdwakecfg().write(|w| unsafe { w.bits(1 << 17) });

        // Set auto-wakeup timer (0x800 counts at 16MHz = ~128µs)
        pmc.autowkup().write(|w| unsafe { w.bits(0x800) });

        // Configure PMC: enable auto-wakeup, disable LVD during transition
        pmc.ctrl().write(|w| unsafe {
            w.bits(
                (pmc_ctrl | (1 << 15)) // AUTOWKEN_MASK
                & !(0x0000_0300),
            ) // ~(LVDCORERE_MASK | LVDCOREIE_MASK)
        });

        // Enable PMC interrupt for auto-wake (IRQ 49, bit 49-32=17 in STARTEN1)
        sysctl0.starten1_set().write(|w| unsafe { w.bits(1 << 17) });

        // Execute WFI - will wake automatically via PMC timer
        cortex_m::asm::wfi();

        // Restore PMC CTRL
        pmc.ctrl().write(|w| unsafe { w.bits(pmc_ctrl) });

        // Clear auto-wake flag
        pmc.flags().write(|w| w.autowkf().set_bit());

        // Disable PMC start event
        sysctl0.starten1_clr().write(|w| unsafe { w.bits(1 << 17) });

        // Clear PDWAKECFG
        sysctl0.pdwakecfg().write(|w| unsafe { w.bits(0) });

        // Disable deep sleep (clear SLEEPDEEP bit in SCR)
        // # Safety: Unsafe required to modify SCR register to clear SLEEPDEEP bit
        unsafe { scb.scr.modify(|v| v & !SCB_SCR_SLEEPDEEP) };
    });
}

/// LVD falling trip voltage values
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LvdFallingTripVoltage {
    /// 720mV
    Vol720 = 0,
    /// 735mV
    Vol735 = 1,
    /// 750mV
    Vol750 = 2,
    /// 765mV
    Vol765 = 3,
    /// 780mV
    Vol780 = 4,
    /// 795mV
    Vol795 = 5,
    /// 810mV
    Vol810 = 6,
    /// 825mV
    Vol825 = 7,
    /// 840mV
    Vol840 = 8,
    /// 855mV
    Vol855 = 9,
    /// 870mV
    Vol870 = 10,
    /// 885mV
    Vol885 = 11,
    /// 900mV
    Vol900 = 12,
    /// 915mV
    Vol915 = 13,
    /// 930mV
    Vol930 = 14,
    /// 945mV
    Vol945 = 15,
}

/// Set vddcore LVD falling trip voltage.
pub fn set_lvd_falling_trip_voltage(pmc: &crate::pac::Pmc, volt: LvdFallingTripVoltage) {
    pmc.lvdcorectrl().write(|w| unsafe { w.lvdcorelvl().bits(volt as u8) });
    apply_pd(pmc);
}

/// Get current vddcore LVD falling trip voltage.
pub fn get_lvd_falling_trip_voltage(pmc: &crate::pac::Pmc) -> LvdFallingTripVoltage {
    let val = pmc.lvdcorectrl().read().lvdcorelvl().bits();
    // SAFETY: The hardware register is 4 bits (0-15) and LvdFallingTripVoltage
    // has all 16 variants (0-15) defined with #[repr(u8)], so transmute is safe
    unsafe { core::mem::transmute(val) }
}

/// Returns the LDO voltage level for a given frequency, or `POWER_INVALID_VOLT_LEVEL` if too high.
/// `freq_levels` must be descending; each threshold maps to a voltage in `POWER_LDO_VOLT_LEVEL`.
pub fn calc_volt_level(freq_levels: &[u32], freq: u32) -> u32 {
    // Debug assert: freq_levels must be in descending order
    // Nothing will happen in release builds if this is not met.
    debug_assert!(
        freq_levels.windows(2).all(|w| w[0] >= w[1]),
        "freq_levels must be in descending order"
    );

    // Find the first frequency threshold that freq is greater than
    let position = freq_levels.iter().position(|&threshold| freq > threshold);

    match position {
        // freq is greater than freq_levels[0], meaning freq is too high
        Some(0) => POWER_INVALID_VOLT_LEVEL,
        // freq is between thresholds - calculate voltage index
        Some(i) => {
            let idx = POWER_LDO_VOLT_LEVEL.len() - freq_levels.len() + i - 1;
            if idx < POWER_LDO_VOLT_LEVEL.len() {
                POWER_LDO_VOLT_LEVEL[idx] as u32
            } else {
                POWER_INVALID_VOLT_LEVEL
            }
        }
        // freq is not greater than any threshold (freq <= all values)
        // default to lowest voltage level
        None => POWER_LDO_VOLT_LEVEL[POWER_LDO_VOLT_LEVEL.len() - 1] as u32,
    }
}

/// Temperature range for voltage/frequency lookup
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TempRange {
    /// Part temp range 0°C - 85°C.
    Temp0Cto85C = 0,
    /// Part temp range -20°C - 85°C.
    TempN20CtoP85C = 1,
}

/// Voltage operating range
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VoltOpRange {
    /// Low voltage range (0.8V - 1.0V)
    Low,
    /// Full voltage range (0.8V - 1.2V)
    Full,
}

/// Sets the LDO voltage for given CM33/DSP frequencies and temperature/voltage range.
/// Returns true if voltage was set, false if unsupported.
pub fn set_ldo_voltage_for_freq(
    temp_range: TempRange,
    volt_op_range: VoltOpRange,
    cm33_freq: u32,
    dsp_freq: u32,
) -> bool {
    critical_section::with(|_cs| {
        // SAFETY: This critical section ensures exclusive access to PMC
        let pmc = unsafe { crate::pac::Pmc::steal() };

        // Enter FBB mode if not already in FBB
        if get_body_bias_mode(&pmc) != BodyBiasMode::Fbb {
            #[cfg(feature = "defmt")]
            defmt::info!("Entering FBB mode for voltage scaling");
            enter_fbb(&pmc);
        }

        let idx = temp_range as usize;
        if idx >= 2 {
            return false;
        }

        let cm33_levels: &[u32] = match volt_op_range {
            VoltOpRange::Low => &POWER_LOW_CM33_FREQ_LEVEL[idx][..],
            VoltOpRange::Full => &POWER_FULL_CM33_FREQ_LEVEL[idx][..],
        };
        let dsp_levels: &[u32] = match volt_op_range {
            VoltOpRange::Low => &POWER_LOW_DSP_FREQ_LEVEL[idx][..],
            VoltOpRange::Full => &POWER_FULL_DSP_FREQ_LEVEL[idx][..],
        };

        let cm33_volt = calc_volt_level(cm33_levels, cm33_freq);
        let dsp_volt = calc_volt_level(dsp_levels, dsp_freq);

        let volt = match (cm33_volt, dsp_volt, cm33_freq, dsp_freq) {
            // Both cores active and valid - use higher voltage
            (c, d, _, _) if c != POWER_INVALID_VOLT_LEVEL && d != POWER_INVALID_VOLT_LEVEL => core::cmp::max(c, d),
            // Only CM33 active with valid frequency
            (c, _, c_freq, _) if c != POWER_INVALID_VOLT_LEVEL && c_freq != 0 => c,
            // Only DSP active with valid frequency
            (_, d, _, d_freq) if d != POWER_INVALID_VOLT_LEVEL && d_freq != 0 => d,
            // Invalid configuration
            _ => POWER_INVALID_VOLT_LEVEL,
        };

        if volt != POWER_INVALID_VOLT_LEVEL {
            // Manage LVD thresholds to prevent false triggers during voltage change
            match volt {
                // <0.8V desired - disable LVD entirely
                v if v < LDOVoltLevel::Ldo0p8v as u32 => {
                    disable_lvd(&pmc);
                }
                // [0.8-0.9V) desired - decrease LVD level if higher than 795mV
                v if v < LDOVoltLevel::Ldo0p9v as u32 => {
                    let current = get_lvd_falling_trip_voltage(&pmc);
                    if (current as u8) > (LvdFallingTripVoltage::Vol795 as u8) {
                        set_lvd_falling_trip_voltage(&pmc, LvdFallingTripVoltage::Vol795);
                    }
                }
                // [0.9-1.0V) desired - decrease LVD level if higher than 885mV
                v if v < LDOVoltLevel::Ldo1p0v as u32 => {
                    let current = get_lvd_falling_trip_voltage(&pmc);
                    if (current as u8) > (LvdFallingTripVoltage::Vol885 as u8) {
                        set_lvd_falling_trip_voltage(&pmc, LvdFallingTripVoltage::Vol885);
                    }
                }
                _ => (),
            };

            // Set the voltage in PMC RUNCTRL
            pmc.runctrl().modify(|_, w| unsafe { w.corelvl().bits(volt as u8) });

            // Apply power domain configuration
            apply_pd(&pmc);

            // Re-enable LVD if voltage is high enough (>= 0.8V)
            if volt >= LDOVoltLevel::Ldo0p8v as u32 {
                restore_lvd(&pmc);
            }

            return true;
        }

        false
    }) // End of critical section
}

/// Applies the LDO voltage for run mode.
pub fn apply_ldo_voltage(pmc: &crate::pac::Pmc, volt: u8) {
    // Write the vddcore voltage level to the PMC RUNCTRL register
    // The voltage value maps to specific voltage ranges defined in POWER_LDO_VOLT_LEVEL
    pmc.runctrl().modify(|_, w| unsafe { w.corelvl().bits(volt) });
}

/// Applies the LDO voltage for sleep mode.
pub fn apply_ldo_voltage_sleep(pmc: &crate::pac::Pmc, volt: u8) {
    // Write the vddcore voltage level to the PMC SLEEPCTRL register
    pmc.sleepctrl().modify(|_, w| unsafe { w.corelvl().bits(volt) });
}

/// Reads and returns the current LDO voltage.
pub fn read_ldo_voltage(pmc: &crate::pac::Pmc) -> u8 {
    // Read the current vddcore voltage level from the PMC RUNCTRL register
    pmc.runctrl().read().corelvl().bits()
}

/// Reads and returns the current LDO voltage (sleep mode).
pub fn read_ldo_voltage_sleep(pmc: &crate::pac::Pmc) -> u8 {
    // Read the current vddcore voltage level from the PMC SLEEPCTRL register
    pmc.sleepctrl().read().corelvl().bits()
}

// Unit tests for power management functions
// TODO: Figure out if `cargo test` can be fixed, linker issues for embedded targets
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_calc_volt_level_edges() {
        let table = [300 * MEGA, 200 * MEGA, 100 * MEGA];
        // freq > highest threshold -> invalid
        assert_eq!(calc_volt_level(&table, 400 * MEGA), POWER_INVALID_VOLT_LEVEL);

        // freq = 300 MHz -> freq > 200 but not freq > 300, so position=1, idx=2
        assert_eq!(calc_volt_level(&table, 300 * MEGA), POWER_LDO_VOLT_LEVEL[2] as u32);

        // freq between 200-300 MHz -> freq > 200, so position=1, idx=2
        assert_eq!(calc_volt_level(&table, 250 * MEGA), POWER_LDO_VOLT_LEVEL[2] as u32);

        // freq < 100 MHz -> should use lowest voltage
        assert_eq!(calc_volt_level(&table, 50 * MEGA), POWER_LDO_VOLT_LEVEL[4] as u32);
    }

    #[test]
    fn test_invalid_volt_level_constant() {
        // Verify invalid voltage level sentinel value
        assert_eq!(POWER_INVALID_VOLT_LEVEL, 0xFFFFFFFF);
    }

    #[test]
    fn test_body_bias_mode_enum() {
        // Verify BodyBiasMode enum values
        assert_eq!(BodyBiasMode::Fbb as u32, 1);
        assert_eq!(BodyBiasMode::Rbb as u32, 2);
        assert_eq!(BodyBiasMode::Nbb as u32, 3);
    }
}
