//! implements embedded-hal trait for PWM controller(s) in the iMXRT chipset
// =====
// PWM can be driven by two different sources at the hardware level within the iMXRT (6) devices:
// 1. SCTimer/PWM (SCT)
// 2. CTimer[n]
//
// SCT-based PWM
// ---
// [UM11147] SCTimer/PWM Supports:
//  - 8 inputs
//  - 10 outputs
//  - 16 match/capture registers
//  - 16 events
//  - 32 states
//  ...
// PWM Features:
//   - can be used in conjunction with match registers to toggle outputs to create time-proportioned PWM signals
//   - up to 10 single-edge or 7 dual-edge PWM outputs w/ independent duty cycle and common PWM cycle length
// Said simpler: the 10 output channels can be used as PWM drivers by using a common clock source divided by the match registers.
//
// For the RT6 series of iMXRT devices, there is typically only a single SCT instance
//
// CTimer[n] based PWM
// ---
// RT6xx series has 4 Ctimer instances. Each Ctimer has 4 external match outputs.
// PWM output can be configured on Ctimer MATn2:0 output pins
// One additional match register determines PWM cycle length.
// When match occurs in any of the other match registers, PWM out is set to high.
// The timer is reset by the match register that is configured to set the PWM cycle length.
// When the timer is reset to zero, all currently HIGH match outputs configured as PWM outputs are cleared

/// include the traits that are implemented + exposed via this implementation
use crate::Peri;
/// include pac definitions for instancing
use crate::pac;

/// clock source indicator for selecting while powering on the `SCTimer`
#[derive(Copy, Clone, Debug)]
pub enum SCTClockSource {
    /// main clock
    Main,

    /// main PLL clock (`main_pll_clk`)
    MainPLL,

    /// `aux0_pll_clk`
    AUX0PLL,

    /// `48/60m_irc`
    FFRO,

    /// `aux1_pll_clk`
    AUX1PLL,

    /// `audio_pll_clk`
    AudioPLL,

    /// lowest power selection
    None,
}

/// `SCTimer` based PWM Interface Constraints
#[derive(Copy, Clone, Debug)]
pub enum Channel {
    /// Channel 0
    Ch0,
    /// Channel 1
    Ch1,
    /// Channel 2
    Ch2,
    /// Channel 3
    Ch3,
    /// Channel 4
    Ch4,
    /// Channel 5
    Ch5,
    /// Channel 6
    Ch6,
    /// Channel 7
    Ch7,
    /// Channel 8
    Ch8,
    /// Channel 9
    Ch9,
}

// iterable channel array for brevity
static CHANNELS: [Channel; 10] = [
    Channel::Ch0,
    Channel::Ch1,
    Channel::Ch2,
    Channel::Ch3,
    Channel::Ch4,
    Channel::Ch5,
    Channel::Ch6,
    Channel::Ch7,
    Channel::Ch8,
    Channel::Ch9,
];

impl Channel {
    fn bit(&self) -> u32 {
        use Channel::{Ch0, Ch1, Ch2, Ch3, Ch4, Ch5, Ch6, Ch7, Ch8, Ch9};
        match self {
            Ch0 => 0b1,
            Ch1 => 0b10,
            Ch2 => 0b100,
            Ch3 => 0b1000,
            Ch4 => 0b10000,
            Ch5 => 0b10_0000,
            Ch6 => 0b100_0000,
            Ch7 => 0b1000_0000,
            Ch8 => 0b1_0000_0000,
            Ch9 => 0b10_0000_0000,
        }
    }

    fn number(&self) -> usize {
        use Channel::{Ch0, Ch1, Ch2, Ch3, Ch4, Ch5, Ch6, Ch7, Ch8, Ch9};
        match self {
            Ch0 => 0,
            Ch1 => 1,
            Ch2 => 2,
            Ch3 => 3,
            Ch4 => 4,
            Ch5 => 5,
            Ch6 => 6,
            Ch7 => 7,
            Ch8 => 8,
            Ch9 => 9,
        }
    }
}

// non-reexported (sealed) traits
mod sealed {
    use crate::PeripheralType;
    use crate::clocks::SysconPeripheral;

    pub trait SCTimer: PeripheralType + SysconPeripheral + 'static + Send {
        fn set_clock_source(clock: super::SCTClockSource);
        fn get_clock_rate(clock: super::SCTClockSource) -> super::Hertz;
        fn set_divisor(divisor: u8);
        fn configure(base_period: u32);
    }
}

/// units per second
#[derive(Copy, Clone, Debug)]
pub struct Hertz(pub u32);

/// 1^(-6) seconds
#[derive(Copy, Clone, Debug)]
pub struct MicroSeconds(pub u32);

/// (CentiPercent.0) . (CentiPercent.1) % => [0-100].[0-99]
#[derive(Copy, Clone, Debug)]
pub struct CentiPercent(pub u8, pub u8);

impl CentiPercent {
    /// 100.00%
    pub const MAX: CentiPercent = CentiPercent(100, 0);

    /// 00.00%
    pub const MIN: CentiPercent = CentiPercent(0, 0);

    /// Convert from this `CentiPercent` into a u32 (X) / max
    #[must_use]
    pub fn as_scaled(&self, max: u32) -> u32 {
        (u64::from(self.0) * u64::from(max) / 100 + u64::from(self.1) * u64::from(max) / 10_000) as u32
    }

    /// Convert from a u32 ratio (value / max) to a `CentiPercent` (PCT.pp%)
    #[must_use]
    pub fn from_scaled(value: u32, max: u32) -> CentiPercent {
        // extract percentage
        let pct = ((u64::from(value) * 100) / u64::from(max)) as u8;
        let dec = (u64::from(value) * 10_000) / u64::from(max);
        let dec = (dec - u64::from(pct) * 100) as u8;

        CentiPercent(pct, dec)
    }
}

impl From<MicroSeconds> for Hertz {
    fn from(value: MicroSeconds) -> Self {
        // 1us = 1 MHz, 2us = 500 kHz, etc.
        Hertz(1_000_000 / value.0)
    }
}

// only allow specified instances to SCTPwm construct
impl sealed::SCTimer for crate::peripherals::SCT0 {
    fn set_clock_source(clock: self::SCTClockSource) {
        use SCTClockSource::{AUX0PLL, AUX1PLL, AudioPLL, FFRO, Main, MainPLL, None};

        // SAFETY: safe so long as executed from single executor context or during initialization only
        let clkctl0 = unsafe { pac::Clkctl0::steal() };

        match clock {
            Main => {
                clkctl0.sctfclksel().write(|w| w.sel().main_clk());
            }
            MainPLL => {
                clkctl0.sctfclksel().write(|w| w.sel().main_sys_pll_clk());
            }
            AUX0PLL => {
                clkctl0.sctfclksel().write(|w| w.sel().syspll0_aux0_pll_clock());
            }
            FFRO => {
                clkctl0.sctfclksel().write(|w| w.sel().ffro_clk());
            }
            AUX1PLL => {
                clkctl0.sctfclksel().write(|w| w.sel().syspll0_aux1_pll_clock());
            }
            AudioPLL => {
                clkctl0.sctfclksel().write(|w| w.sel().audio_pll_clk());
            }
            None => {
                clkctl0.sctfclksel().write(|w| w.sel().none());
            }
        }

        enable_and_reset::<SCT0>();
    }

    fn get_clock_rate(clock: self::SCTClockSource) -> Hertz {
        use SCTClockSource::{AUX0PLL, AUX1PLL, AudioPLL, FFRO, Main, MainPLL, None};

        // TODO - fix these
        match clock {
            None => Hertz(0),
            Main => Hertz(12_000_000), // TODO - integrate proper clock freq's when clocks.rs is ready
            MainPLL => Hertz(64_000_000), // TODO - integrate proper clock freq's when clocks.rs is ready
            AUX0PLL => Hertz(32_000),  // TODO - integrate proper clock freq's when clocks.rs is ready
            AUX1PLL => Hertz(32_000),  // TODO - integrate proper clock freq's when clocks.rs is ready
            FFRO => Hertz(48_000_000), // TODO - integrate proper clock freq's when clocks.rs is ready
            AudioPLL => Hertz(32_000), // TODO - ""
        }
    }

    /// configure SCT divisor
    fn set_divisor(div: u8) {
        // SAFETY: safe so long as executed from single executor context or during initialization only
        let clkctl0 = unsafe { pac::Clkctl0::steal() };

        clkctl0.sctfclkdiv().modify(|_, w| w.halt().set_bit().reset().set_bit());
        clkctl0.sctfclkdiv().modify(|_, w|
                // SAFETY: safe as long as the above is still true
                unsafe { w.div().bits(div) });
        clkctl0.sctfclkdiv().modify(|_, w| w.halt().clear_bit());
    }

    fn configure(base_period: u32) {
        // SAFETY: safe so long as executed from single executor context or during initialization only
        let sct0 = unsafe { pac::Sct0::steal() };

        // unified (32 bit) counter mode
        sct0.config()
            .modify(|_, w| w.unify().unified_counter().clkmode().system_clock_mode());

        // halt the timer so that it can be configured
        sct0.ctrl().modify(|_, w| w.halt_l().set_bit());

        // clear any previous values out of the timer counter
        sct0.ctrl().modify(|_, w| w.clrctr_l().set_bit());

        // ensure all events are in MATCH mode (0)
        sct0.regmode().modify(|_, w|
            // SAFETY: safe with same constraints above around sct0
            unsafe { w.regmod_l().bits(0) });

        // set the maximum period
        // here we use event 10 as the limit event (b10 == ev10)
        sct0.limit().modify(|_, w|
            // SAFETY: section is safe given same constraints on sct0 above
            unsafe { w.limmsk_l().bits(1 << 10) });

        // now we need to set up the corresponding event 0 limit event. We do this by configuring
        // event 0 as a match event, and setting its match register to base_period
        sct0.match10().write(|w|
            // SAFETY: same safety constraints as above
            unsafe { w.bits(base_period) });
        sct0.matchrel10().write(|w|
                // SAFETY: same safety constraints as above
            unsafe { w.bits(base_period) });

        // set event 10 as match, persistent, select register 10
        sct0.ev(10).ev_ctrl().modify(|_, w|
            // SAFETY: same safety constraints as above (unsafe only used for unnamed bits on matchsel)
                unsafe { w.combmode().match_().matchmem().set_bit().matchsel().bits(10) });

        sct0.ev(10).ev_state().modify(|_, w|
                    // SAFETY: same safety constraint as above (unsafe due to .bits on statemskn)
                unsafe { w.statemskn().bits(0xFF) });

        // configure the SCT for simple PWM operation (count up)
        sct0.ctrl().modify(|_, w| w.bidir_l().up());

        // unhalt the SCT
        sct0.ctrl().modify(|_, w| w.halt_l().clear_bit().stop_l().clear_bit());
    }
}

/// Basic PWM Object, Consumes a `SCTimer` peripheral hardware instance on construction
pub struct SCTPwm<'d, T: sealed::SCTimer> {
    _p: Peri<'d, T>,
    period: MicroSeconds,
    clock: SCTClockSource,
    count_max: u32,
}

impl<'d, T: sealed::SCTimer> SCTPwm<'d, T> {
    /// Take the `SCTimer` instance supplied and use it as a simple PWM driver. Function returns constructed Pwm instance.
    pub fn new(sct: Peri<'d, T>, period: MicroSeconds, clock: SCTClockSource) -> Self {
        // requested period must be possible with configured clock selection (within bounds of u8 divisor)!

        let clock_rate = T::get_clock_rate(clock);
        let requested_pwm_rate: Hertz = period.into();

        // we cannot clock faster than the supplied clock rate
        assert!(period.0 > 0);
        // assure precision is possible (10_000 ticks within PWM minimum)
        assert!(requested_pwm_rate.0 <= clock_rate.0 / 10_000);

        // we want precision of 100.00% steps. We also want to fit this to clock_rate and period.
        // precision: 10_000 ticks
        // 10_000 ticks = 1 period
        // => 1/clock_rate * ticks = period
        //    clock_rate = ticks / period
        // In other words, we need 10_000 clocks per period to achieve the desired precision.
        // we can then add a scale factor to this 10_000 (up to saturation of u32::MAX) to divide clock further
        let factor = clock_rate.0 / requested_pwm_rate.0;
        // should already be caught in assert above, placing redundant constraint here for clarity
        assert!(factor > 0);

        // factor here is the amount of ticks in one period at clock_rate to achieve period and precision.
        // This sets the limit for what COUNTER can be

        // now that the input configuration for rate has been validated, we can set the divisor accordingly
        T::set_clock_source(clock);
        //T::set_divisor((clock_rate.0 / requested_pwm_rate.0) as u8);
        // TODO: if further precision is needed for rates beyond u32::MAX clock_rate to pwm_Rate conversions, we can scale up to 256x
        // to the factor term here.
        T::set_divisor(0);
        T::configure(factor);

        Self {
            _p: sct,
            period,
            clock,
            count_max: factor,
        }
    }
}

impl<T: sealed::SCTimer> Drop for SCTPwm<'_, T> {
    fn drop(&mut self) {
        // disable resources
        T::set_clock_source(SCTClockSource::None);
    }
}

pub use embedded_hal_02::Pwm;

use crate::clocks::enable_and_reset;
use crate::peripherals::SCT0;

impl<T: sealed::SCTimer> embedded_hal_02::Pwm for SCTPwm<'_, T> {
    type Channel = Channel;
    type Time = MicroSeconds;
    type Duty = CentiPercent;

    fn disable(&mut self, channel: Self::Channel) {
        // SAFETY: safe so long as SCTPwm is not used across multiple executors
        let sct0 = unsafe { pac::Sct0::steal() };

        // halt the timer so that it can be configured
        sct0.ctrl().modify(|_, w| w.halt_l().set_bit());

        // disable the corresponding event in the ev control block (disable event in all states)

        sct0.ev(channel.number()).ev_state().modify(|_, w|
            // SAFETY: unsafe only required here due to bits() (missing match select specifier), no new conditions from above unsafe (single executor)
                unsafe { w.statemskn().bits(0) });

        // unhalt the SCT
        sct0.ctrl().modify(|_, w| w.halt_l().clear_bit().stop_l().clear_bit());
    }

    fn enable(&mut self, channel: Self::Channel) {
        // SAFETY: safe so long as SCTPwm is not used across multiple executors
        let sct0 = unsafe { pac::Sct0::steal() };

        // halt the timer so that it can be configured
        sct0.ctrl().modify(|_, w| w.halt_l().set_bit());

        // set the channel for up + down match register event generation (ev# = channel number)

        sct0.ev(channel.number()).ev_ctrl().modify(|_, w|
            // SAFETY: unsafe only required here due to bits() (missing match select specifier), no new conditions from above unsafe (single executor)
            unsafe {
            // combmode to match indicates we are not using this channel for capture/compare functions
            w.combmode()
                .match_()
                // set the direction to UP, redundant
                .direction()
                .counting_up()
                // set the match register (match select) to the corresponding match register we are managing here (same as channel number)
                .matchsel()
                .bits(channel.number() as u8)
                // set this event as an output event
                .outsel()
                .output()
                // enable the entire time we are >= count
                .matchmem()
                .set_bit()
        });

        // enable the corresponding event in the ev control block (allow event in all states)

        sct0.ev(channel.number()).ev_state().modify(|_, w|
            // SAFETY: unsafe only required here due to bits() (missing match select specifier), no new conditions from above unsafe (single executor)
                unsafe { w.statemskn().bits(0xFF) });

        // set the duty cycle positive edge to correspond to the up counter
        // logic is as follows (example 50% duty cycle for channel n):
        //                           P
        // EVn -----------++++++++++ |
        //     0...... 50%^ ...... 100%
        //                CLR-------
        // SET +++++++++++
        // IOn 111111111110000000000
        // match register n is essentially the tick during period P where we turn "off" IOn

        sct0.out(channel.number()).out_clr().modify(|_, w|
            // SAFETY: unsafe only required here due to bits() (missing match select specifier), no new conditions from above unsafe (single executor)
                unsafe { w.clr().bits(channel.bit() as u16) });

        sct0.out(channel.number()).out_set().modify(|_, w|
                    // SAFETY: unsafe only required here due to bits(), no new conditions imposed
                unsafe { w.set_().bits(1 << 10) });

        // set conflict resolution to SET so that 100% is not treated as 0%
        sct0.res().modify(|_, w| match channel {
            Channel::Ch0 => w.o0res().set_(),
            Channel::Ch1 => w.o1res().set_(),
            Channel::Ch2 => w.o2res().set_(),
            Channel::Ch3 => w.o3res().set_(),
            Channel::Ch4 => w.o4res().set_(),
            Channel::Ch5 => w.o5res().set_(),
            Channel::Ch6 => w.o6res().set_(),
            Channel::Ch7 => w.o7res().set_(),
            Channel::Ch8 => w.o8res().set_(),
            Channel::Ch9 => w.o9res().set_(),
        });

        // set the output direction control to invert behavior on down counter
        sct0.outputdirctrl().modify(|_, w| match channel {
            Channel::Ch0 => w.setclr0().independent(),
            Channel::Ch1 => w.setclr1().independent(),
            Channel::Ch2 => w.setclr2().independent(),
            Channel::Ch3 => w.setclr3().independent(),
            Channel::Ch4 => w.setclr4().independent(),
            Channel::Ch5 => w.setclr5().independent(),
            Channel::Ch6 => w.setclr6().independent(),
            Channel::Ch7 => w.setclr7().independent(),
            Channel::Ch8 => w.setclr8().independent(),
            Channel::Ch9 => w.setclr9().independent(),
        });

        // unhalt the SCT
        sct0.ctrl().modify(|_, w| w.halt_l().clear_bit().stop_l().clear_bit());
    }

    fn get_period(&self) -> Self::Time {
        self.period
    }

    fn get_duty(&self, channel: Self::Channel) -> Self::Duty {
        use Channel::{Ch0, Ch1, Ch2, Ch3, Ch4, Ch5, Ch6, Ch7, Ch8, Ch9};
        // SAFETY: safe so long as SCTPwm is not used across multiple executors
        let sct0 = unsafe { pac::Sct0::steal() };

        let channel_match = match channel {
            Ch0 => sct0.matchrel0().read().bits(),
            Ch1 => sct0.matchrel1().read().bits(),
            Ch2 => sct0.matchrel2().read().bits(),
            Ch3 => sct0.matchrel3().read().bits(),
            Ch4 => sct0.matchrel4().read().bits(),
            Ch5 => sct0.matchrel5().read().bits(),
            Ch6 => sct0.matchrel6().read().bits(),
            Ch7 => sct0.matchrel7().read().bits(),
            Ch8 => sct0.matchrel8().read().bits(),
            Ch9 => sct0.matchrel9().read().bits(),
        };

        CentiPercent::from_scaled(channel_match, self.count_max)
    }

    fn get_max_duty(&self) -> Self::Duty {
        CentiPercent::MAX
    }

    fn set_duty(&mut self, channel: Self::Channel, duty: Self::Duty) {
        // set match register accordingly
        let scaled = duty.as_scaled(self.count_max);

        // SAFETY: safe so long as SCTPwm is not used across multiple executors
        let sct0 = unsafe { pac::Sct0::steal() };

        use Channel::{Ch0, Ch1, Ch2, Ch3, Ch4, Ch5, Ch6, Ch7, Ch8, Ch9};

        match channel {
            Ch0 => {
                sct0.matchrel0().write(|w|
                // SAFETY: safe as both L and H are used
                unsafe { w.bits(scaled) });
            }
            Ch1 => {
                sct0.matchrel1().write(|w|
                    // SAFETY: safe as both L and H are used
                unsafe { w.bits(scaled) });
            }
            Ch2 => {
                sct0.matchrel2().write(|w|
                    // SAFETY: safe as both L and H are used
                unsafe { w.bits(scaled) });
            }
            Ch3 => {
                sct0.matchrel3().write(|w|
                    // SAFETY: safe as both L and H are used
                unsafe { w.bits(scaled) });
            }
            Ch4 => {
                sct0.matchrel4().write(|w|
                    // SAFETY: safe as both L and H are used
                unsafe { w.bits(scaled) });
            }
            Ch5 => {
                sct0.matchrel5().write(|w|
                    // SAFETY: safe as both L and H are used
                unsafe { w.bits(scaled) });
            }
            Ch6 => {
                sct0.matchrel6().write(|w|
                    // SAFETY: safe as both L and H are used
                unsafe { w.bits(scaled) });
            }
            Ch7 => {
                sct0.matchrel7().write(|w|
                    // SAFETY: safe as both L and H are used
                unsafe { w.bits(scaled) });
            }
            Ch8 => {
                sct0.matchrel8().write(|w|
                    // SAFETY: safe as both L and H are used
                unsafe { w.bits(scaled) });
            }
            Ch9 => {
                sct0.matchrel9().write(|w|
                    // SAFETY: safe as both L and H are used
                unsafe { w.bits(scaled) });
            }
        }
    }

    fn set_period<P>(&mut self, period: P)
    where
        P: Into<Self::Time>,
    {
        let clock_rate = T::get_clock_rate(self.clock);
        let requested_pwm_rate: Hertz = period.into().into();

        // period cannot be faster than supplied PWM clock source
        assert!(requested_pwm_rate.0 > 0);
        assert!(requested_pwm_rate.0 <= clock_rate.0 / 10_000);

        // record current duty cycles
        let duty_cycles = CHANNELS.map(|ch| self.get_duty(ch));

        // update scale factor
        self.count_max = clock_rate.0 / requested_pwm_rate.0;

        // set limit register accordingly
        T::configure(self.count_max);

        // update duty cycle match registers according to new scale factor
        for i in 0..CHANNELS.len() {
            self.set_duty(CHANNELS[i], duty_cycles[i]);
        }
    }
}
