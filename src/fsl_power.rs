//! Power management utilities ported from NXP's fsl_power.c
//!
//! This module provides voltage scaling and frequency management for iMX RT600 series MCUs.
//! It includes lookup tables for supported CPU and DSP frequencies at different voltage levels,
//! and functions to calculate appropriate LDO voltage settings based on target frequencies.

use core::sync::atomic::{AtomicU32, Ordering};

// Constants
const MEGA: u32 = 1_000_000;

// Frequency tables (equivalent dimensions as C arrays)
/// CM33 frequency levels for low voltage operating range [temp_range][level]
pub const POWER_LOW_CM33_FREQ_LEVEL: [[u32; 3]; 2] =
    [[220 * MEGA, 150 * MEGA, 70 * MEGA], [215 * MEGA, 140 * MEGA, 60 * MEGA]];

/// DSP frequency levels for low voltage operating range [temp_range][level]
pub const POWER_LOW_DSP_FREQ_LEVEL: [[u32; 3]; 2] = [
    [375 * MEGA, 260 * MEGA, 115 * MEGA],
    [355 * MEGA, 235 * MEGA, 95 * MEGA],
];

/// CM33 frequency levels for full voltage operating range [temp_range][level]
pub const POWER_FULL_CM33_FREQ_LEVEL: [[u32; 5]; 2] = [
    [300 * MEGA, 275 * MEGA, 210 * MEGA, 140 * MEGA, 65 * MEGA],
    [300 * MEGA, 270 * MEGA, 200 * MEGA, 135 * MEGA, 50 * MEGA],
];

/// DSP frequency levels for full voltage operating range [temp_range][level]
pub const POWER_FULL_DSP_FREQ_LEVEL: [[u32; 5]; 2] = [
    [600 * MEGA, 480 * MEGA, 300 * MEGA, 195 * MEGA, 70 * MEGA],
    [550 * MEGA, 440 * MEGA, 285 * MEGA, 170 * MEGA, 55 * MEGA],
];

const POWER_LDO_VOLT_LEVEL: [u32; 5] = [0x32, 0x26, 0x1D, 0x13, 0x0A];

/// Sentinel value indicating an invalid or unsupported voltage level
pub const POWER_INVALID_VOLT_LEVEL: u32 = 0xFFFFFFFF;

// Global (simulated) state variables from the C file
static OSC_SETTLING_TIME: AtomicU32 = AtomicU32::new(0);
static PMIC_VDDCORE_RECOVERY_TIME: AtomicU32 = AtomicU32::new(0);
static LVD_CHANGE_FLAG: AtomicU32 = AtomicU32::new(0);

// Public setters mirroring the C APIs
/// Updates the oscillator settling time in microseconds
pub fn update_osc_settling_time(us: u32) {
    OSC_SETTLING_TIME.store(us, Ordering::SeqCst);
}

/// Updates the PMIC VDDCORE recovery time in microseconds
pub fn update_pmic_recovery_time(us: u32) {
    PMIC_VDDCORE_RECOVERY_TIME.store(us, Ordering::SeqCst);
}

/// Disables the Low Voltage Detector (LVD)
///
/// Disables LVD core reset and interrupt if they were enabled, saving the state
pub fn disable_lvd() {
    // SAFETY: unsafe needed to take pointer to PMC peripheral
    let pmc = unsafe { crate::pac::Pmc::steal() };

    let ctrl = pmc.ctrl().read().bits();
    const LVD_MASK: u32 = 0x0000_0300; // LVDCORERE_MASK | LVDCOREIE_MASK

    if (ctrl & LVD_MASK) != 0 {
        LVD_CHANGE_FLAG.store(ctrl & LVD_MASK, Ordering::SeqCst);
        pmc.ctrl().modify(|r, w| unsafe { w.bits(r.bits() & !LVD_MASK) });
    }
}

/// Restores the Low Voltage Detector (LVD) to its previous state
pub fn restore_lvd() {
    let flags = LVD_CHANGE_FLAG.load(Ordering::SeqCst);
    if flags != 0 {
        // SAFETY: unsafe needed to take pointer to PMC peripheral
        let pmc = unsafe { crate::pac::Pmc::steal() };
        pmc.ctrl().modify(|r, w| unsafe { w.bits(r.bits() | flags) });
        LVD_CHANGE_FLAG.store(0, Ordering::SeqCst);
    }
}

/// Apply updated PMC PDRUNCFG bits in the Sysctl0
///
/// This function triggers the PMC to apply power domain configuration changes.
/// It waits for the PMC finite state machine to be idle before and after applying changes.
pub fn apply_pd() {
    // SAFETY: unsafe needed to take pointer to PMC peripheral
    let pmc = unsafe { crate::pac::Pmc::steal() };

    // Cannot set APPLYCFG when ACTIVEFSM is 1
    while pmc.status().read().activefsm().bit_is_set() {}

    // Set APPLYCFG bit
    pmc.ctrl().modify(|_, w| w.applycfg().set_bit());

    // Wait all PMC finite state machines finished
    while pmc.status().read().activefsm().bit_is_set() {}
}

/// Body bias mode for power management
///
/// Body biasing adjusts the threshold voltage of transistors to optimize
/// performance vs. power consumption.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BodyBiasMode {
    /// Forward Body Bias - increases performance, higher leakage
    Fbb = 1,
    /// Reverse Body Bias - reduces leakage, lower performance
    Rbb = 2,
    /// No Body Bias - neutral mode
    Nbb = 3,
}

/// Get the current body bias mode
///
/// # Returns
/// The current body bias mode (RBB, FBB, or NBB)
pub fn get_body_bias_mode() -> BodyBiasMode {
    // SAFETY: unsafe needed to take pointer to PMC peripheral
    let pmc = unsafe { crate::pac::Pmc::steal() };

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
/// Typically used in high-performance operating modes.
pub fn enter_fbb() {
    // SAFETY: unsafe needed to take pointer to PMC peripheral
    let pmc = unsafe { crate::pac::Pmc::steal() };

    // Set FBB enable bit in RUNCTRL register (bit 14)
    pmc.runctrl().modify(|r, w| unsafe { w.bits(r.bits() | (1 << 14)) });
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

/// Set vddcore low voltage detection falling trip voltage
///
/// # Arguments
/// * `volt` - Target LVD voltage to set
pub fn set_lvd_falling_trip_voltage(volt: LvdFallingTripVoltage) {
    // SAFETY: unsafe needed to take pointer to PMC peripheral
    let pmc = unsafe { crate::pac::Pmc::steal() };
    pmc.lvdcorectrl().write(|w| unsafe { w.lvdcorelvl().bits(volt as u8) });
    apply_pd();
}

/// Get current vddcore low voltage detection falling trip voltage
///
/// # Returns
/// Current LVD voltage setting
pub fn get_lvd_falling_trip_voltage() -> LvdFallingTripVoltage {
    // SAFETY: unsafe needed to take pointer to PMC peripheral
    let pmc = unsafe { crate::pac::Pmc::steal() };
    let val = pmc.lvdcorectrl().read().lvdcorelvl().bits();

    // SAFETY: The hardware register is 4 bits (0-15) and LvdFallingTripVoltage
    // has all 16 variants (0-15) defined with #[repr(u8)], so transmute is safe
    unsafe { core::mem::transmute(val) }
}

/// Calculates the required LDO voltage level for a given frequency
///
/// # Arguments
/// * `freq_levels` - Slice of frequency thresholds in descending order
/// * `freq` - Target frequency in Hz
///
/// # Returns
/// LDO voltage register value, or `POWER_INVALID_VOLT_LEVEL` if frequency is too high
pub fn calc_volt_level(freq_levels: &[u32], freq: u32) -> u32 {
    // Find the first frequency threshold that freq is greater than
    let position = freq_levels.iter().position(|&threshold| freq > threshold);

    match position {
        // freq is greater than freq_levels[0], meaning freq is too high
        Some(0) => POWER_INVALID_VOLT_LEVEL,
        // freq is between thresholds - calculate voltage index
        Some(i) => {
            let idx = i + POWER_LDO_VOLT_LEVEL.len() - freq_levels.len() - 1;
            POWER_LDO_VOLT_LEVEL[idx]
        }
        // freq is not greater than any threshold (freq <= all values)
        None => {
            let idx = freq_levels.len() + POWER_LDO_VOLT_LEVEL.len() - freq_levels.len() - 1;
            POWER_LDO_VOLT_LEVEL[idx]
        }
    }
}

/// Temperature range for voltage/frequency lookup
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TempRange {
    /// Part temp range 0C - 85C.
    Temp0Cto85C = 0,
    /// Part temp range -20C - 85C.
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

/// Sets the LDO voltage for given frequencies
///
/// This function calculates the appropriate voltage level based on the target frequencies
/// for the CM33 core and DSP, then applies that voltage to the hardware. It is the main
/// entry point for frequency scaling.
///
/// Key operations performed:
/// 1. Validates inputs and looks up frequency thresholds for the given temperature/voltage range
/// 2. Calculates required voltage for both CM33 and DSP cores
/// 3. Takes the higher voltage (most conservative) if both cores are active
/// 4. Manages LVD thresholds to prevent false voltage detection triggers during transitions
/// 5. Applies the voltage using PMC registers in a critical section
/// 6. Triggers hardware power domain updates via `apply_pd()`
/// 7. Manages Forward Body Bias (FBB) mode for performance optimization
///
/// # Arguments
/// * `temp_range` - Temperature range for the lookup tables
/// * `volt_op_range` - Voltage operating range (Low or Full)
/// * `cm33_freq` - Target CM33 core frequency in Hz
/// * `dsp_freq` - Target DSP core frequency in Hz
///
/// # Returns
/// `true` if voltage was successfully calculated and applied, `false` if frequencies are unsupported
///
/// # Safety
/// This function uses a critical section to prevent race conditions during voltage changes.
/// It temporarily disables LVD during low voltage transitions to prevent false resets.
///
/// # Implementation Notes
/// This is a direct port of NXP's `POWER_SetLdoVoltageForFreq` from fsl_power.c, including:
/// - FBB mode management (enters FBB if not already in FBB mode)
/// - LVD threshold management (795mV for 0.9V target, 885mV for 1.0V target, disabled for 0.8V)
/// - Critical section protection during voltage changes
/// - Hardware synchronization via `apply_pd()` FSM wait
pub fn set_ldo_voltage_for_freq(
    temp_range: TempRange,
    volt_op_range: VoltOpRange,
    cm33_freq: u32,
    dsp_freq: u32,
) -> bool {
    critical_section::with(|_cs| {
        // If not in FBB mode, enter it for optimal performance
        if get_body_bias_mode() != BodyBiasMode::Fbb {
            enter_fbb();
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
        let volt = core::cmp::max(cm33_volt, dsp_volt);

        if volt != POWER_INVALID_VOLT_LEVEL {
            // Manage LVD thresholds to prevent false triggers during voltage change
            match volt {
                // 0.8V desired - disable LVD entirely
                v if v < 0x13 => {
                    disable_lvd();
                }
                // 0.9V desired - decrease LVD level if higher than 795mV
                v if v < 0x1D => {
                    let current = get_lvd_falling_trip_voltage();
                    if (current as u8) > (LvdFallingTripVoltage::Vol795 as u8) {
                        set_lvd_falling_trip_voltage(LvdFallingTripVoltage::Vol795);
                    }
                }
                // 1.0V desired - decrease LVD level if higher than 885mV
                v if v < 0x26 => {
                    let current = get_lvd_falling_trip_voltage();
                    if (current as u8) > (LvdFallingTripVoltage::Vol885 as u8) {
                        set_lvd_falling_trip_voltage(LvdFallingTripVoltage::Vol885);
                    }
                }
                _ => (),
            };

            // Set the voltage in PMC RUNCTRL
            let pmc = unsafe { crate::pac::Pmc::steal() };
            pmc.runctrl().modify(|_, w| unsafe { w.corelvl().bits(volt as u8) });

            // Apply power domain configuration
            apply_pd();

            // Re-enable LVD if voltage is high enough (>= 0.8V)
            if volt >= 0x13 {
                restore_lvd();
            }

            return true;
        }

        false
    }) // End of critical section
}

/// Applies the calculated LDO voltage to hardware for run mode
///
/// # Arguments
/// * `volt` - The LDO voltage register value to apply (from `calc_volt_level` or `set_ldo_voltage_for_freq`)
///
/// # Safety
/// This function directly accesses hardware registers and should only be called during
/// initialization or when proper synchronization is in place.
pub fn apply_ldo_voltage(volt: u8) {
    // SAFETY: unsafe needed to take pointer to PMC peripheral for voltage control
    let pmc = unsafe { crate::pac::Pmc::steal() };

    // Write the vddcore voltage level to the PMC RUNCTRL register
    // The voltage value maps to specific voltage ranges defined in POWER_LDO_VOLT_LEVEL
    pmc.runctrl().modify(|_, w| unsafe { w.corelvl().bits(volt) });
}

/// Applies the calculated LDO voltage to hardware for sleep mode
///
/// # Arguments
/// * `volt` - The LDO voltage register value to apply (from `calc_volt_level` or `set_ldo_voltage_for_freq`)
pub fn apply_ldo_voltage_sleep(volt: u8) {
    // SAFETY: unsafe needed to take pointer to PMC peripheral for voltage control
    let pmc = unsafe { crate::pac::Pmc::steal() };

    // Write the vddcore voltage level to the PMC SLEEPCTRL register
    pmc.sleepctrl().modify(|_, w| unsafe { w.corelvl().bits(volt) });
}

/// Reads the current LDO voltage setting from hardware (run mode)
///
/// # Returns
/// The current LDO voltage register value
pub fn read_ldo_voltage() -> u8 {
    // SAFETY: unsafe needed to take pointer to PMC peripheral
    let pmc = unsafe { crate::pac::Pmc::steal() };

    // Read the current vddcore voltage level from the PMC RUNCTRL register
    pmc.runctrl().read().corelvl().bits()
}

/// Reads the current LDO voltage setting from hardware (sleep mode)
///
/// # Returns
/// The current LDO voltage register value for sleep mode
pub fn read_ldo_voltage_sleep() -> u8 {
    // SAFETY: unsafe needed to take pointer to PMC peripheral
    let pmc = unsafe { crate::pac::Pmc::steal() };

    // Read the current vddcore voltage level from the PMC SLEEPCTRL register
    pmc.sleepctrl().read().corelvl().bits()
}

// Tests are disabled for embedded targets (no_std) as they require the Rust test framework.
// These tests validate pure logic, constants, and data structures (no hardware access).
// For embedded testing, use defmt-test or hardware integration tests.
// The test code below serves as documentation and can be manually validated.
#[cfg(all(test, not(target_arch = "arm")))]
mod tests {
    use super::*;

    #[test]
    fn test_calc_volt_level_edges() {
        // Use a small frequency table: descending values
        let table = [300 * MEGA, 200 * MEGA, 100 * MEGA];
        // freq greater than first -> invalid
        assert_eq!(calc_volt_level(&table, 400 * MEGA), POWER_INVALID_VOLT_LEVEL);
        // freq equal to first -> not greater, so moves to next
        let got_eq = calc_volt_level(&table, 300 * MEGA);
        // compute expected via same index formula
        let num = table.len();
        let mut i = 0usize;
        while i < num {
            if 300 * MEGA > table[i] {
                break;
            }
            i += 1;
        }
        let expected_eq = if i == 0 {
            POWER_INVALID_VOLT_LEVEL
        } else {
            let idx = i + POWER_LDO_VOLT_LEVEL.len() - num - 1;
            POWER_LDO_VOLT_LEVEL[idx]
        };
        assert_eq!(got_eq, expected_eq);

        // freq between first and second
        let got_mid = calc_volt_level(&table, 250 * MEGA);
        let mut i = 0usize;
        while i < num {
            if 250 * MEGA > table[i] {
                break;
            }
            i += 1;
        }
        let expected_mid = if i == 0 {
            POWER_INVALID_VOLT_LEVEL
        } else {
            let idx = i + POWER_LDO_VOLT_LEVEL.len() - num - 1;
            POWER_LDO_VOLT_LEVEL[idx]
        };
        assert_eq!(got_mid, expected_mid);

        // freq less than last -> uses last level
        let got_low = calc_volt_level(&table, 50 * MEGA);
        let mut i = 0usize;
        while i < num {
            if 50 * MEGA > table[i] {
                break;
            }
            i += 1;
        }
        let expected_low = if i == 0 {
            POWER_INVALID_VOLT_LEVEL
        } else {
            let idx = i + POWER_LDO_VOLT_LEVEL.len() - num - 1;
            POWER_LDO_VOLT_LEVEL[idx]
        };
        assert_eq!(got_low, expected_low);
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
