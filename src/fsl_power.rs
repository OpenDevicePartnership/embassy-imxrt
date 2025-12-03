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

/// LDO voltage levels corresponding to frequency thresholds
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
///
/// # Safety
/// This function should not be called concurrently from multiple contexts
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
    // Clear RBB bit (bit 13) if set
    pmc.runctrl()
        .modify(|r, w| unsafe { w.bits((r.bits() & !(1 << 13)) | (1 << 14)) });
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

/// Calculates the required LDO voltage level for a given frequency.
///
/// # Arguments
/// * `freq_levels` - Slice of frequency thresholds in Hz, in descending order.
///   The length of `freq_levels` must be less than or equal to `POWER_LDO_VOLT_LEVEL.len()`.
///   Each threshold corresponds to a voltage level in `POWER_LDO_VOLT_LEVEL`, such that
///   frequencies above a threshold require a higher voltage.
/// * `freq` - Target frequency in Hz.
///
/// # Returns
/// LDO voltage register value, or `POWER_INVALID_VOLT_LEVEL` if frequency is too high.
///
/// # Example
/// ```
/// // Suppose POWER_LDO_VOLT_LEVEL = [0x1, 0x2, 0x3]
/// // and freq_levels = [300_000_000, 200_000_000]
/// // For freq = 250_000_000, the function returns 0x2
/// // For freq = 350_000_000, the function returns POWER_INVALID_VOLT_LEVEL
/// // For freq = 150_000_000, the function returns 0x3
/// ```
pub fn calc_volt_level(freq_levels: &[u32], freq: u32) -> u32 {
    // Find the first frequency threshold that freq is greater than
    let position = freq_levels.iter().position(|&threshold| freq > threshold);

    match position {
        // freq is greater than freq_levels[0], meaning freq is too high
        Some(0) => POWER_INVALID_VOLT_LEVEL,
        // freq is between thresholds - calculate voltage index
        Some(i) => {
            let idx = i + POWER_LDO_VOLT_LEVEL.len() - freq_levels.len() - 1;
            POWER_LDO_VOLT_LEVEL[idx] as u32
        }
        // freq is not greater than any threshold (freq <= all values)
        // default to lowest voltage level
        None => POWER_LDO_VOLT_LEVEL[POWER_LDO_VOLT_LEVEL.len() - 1] as u32,
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
        // Enter FBB mode for optimal performance
        enter_fbb();

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
            (c, _, freq, _) if c != POWER_INVALID_VOLT_LEVEL && freq != 0 => c,
            // Only DSP active with valid frequency
            (_, d, _, freq) if d != POWER_INVALID_VOLT_LEVEL && freq != 0 => d,
            // Invalid configuration
            _ => POWER_INVALID_VOLT_LEVEL,
        };

        if volt != POWER_INVALID_VOLT_LEVEL {
            // Manage LVD thresholds to prevent false triggers during voltage change
            match volt {
                // <0.8V desired - disable LVD entirely
                v if v < LDOVoltLevel::Ldo0p8v as u32 => {
                    disable_lvd();
                }
                // [0.8-0.9V) desired - decrease LVD level if higher than 795mV
                v if v < LDOVoltLevel::Ldo0p9v as u32 => {
                    let current = get_lvd_falling_trip_voltage();
                    if (current as u8) > (LvdFallingTripVoltage::Vol795 as u8) {
                        set_lvd_falling_trip_voltage(LvdFallingTripVoltage::Vol795);
                    }
                }
                // [0.9-1.0V) desired - decrease LVD level if higher than 885mV
                v if v < LDOVoltLevel::Ldo1p0v as u32 => {
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
            if volt >= LDOVoltLevel::Ldo0p8v as u32 {
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
