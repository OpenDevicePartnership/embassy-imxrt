//! Timer module for the NXP RT6xx family of microcontrollers
use core::future::poll_fn;
use core::marker::PhantomData;
use core::task::Poll;

use embassy_hal_internal::interrupt::InterruptExt;
use embassy_sync::waitqueue::AtomicWaker;
use paste::paste;

use crate::clocks::{enable_and_reset, ClockConfig, ConfigurableClock};
use crate::iopctl::{DriveMode, DriveStrength, Inverter, IopctlPin as Pin, Pull, SlewRate};
use crate::pac::clkctl1::ct32bitfclksel::Sel;
use crate::pac::Clkctl1;
use crate::pwm::{CentiPercent, Hertz, MicroSeconds};
use crate::{interrupt, peripherals, Peri, PeripheralType};

const COUNT_CHANNEL: usize = 20;
const CAPTURE_CHANNEL: usize = 20;
const TOTAL_CHANNELS: usize = COUNT_CHANNEL + CAPTURE_CHANNEL;
const CHANNEL_PER_MODULE: usize = 4;
const PWM_PRECISION_CLK_TICKS_PER_PERIOD: u32 = 500;

/// Enum representing timer channels
#[derive(Copy, Clone, Debug)]
pub enum TimerChannelNum {
    /// Timer channel 0
    Channel0,
    /// Timer channel 1
    Channel1,
    /// Timer channel 2
    Channel2,
    /// Timer channel 3
    Channel3,
}

/// Timer Errors
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum Error {
    /// PWM cannot be enabled with provided period
    InvalidPwmPeriod,

    /// PWM output with min precision cannot enabled with provided period and clock rate
    PwmPrecisionNotSupported,

    /// Pwm length channel and output channel does not belong to same CTimer
    PwmChannelMismatch,
}

/// Enum representing the logical capture channel input.
pub enum TriggerInput {
    /// Capture input 0
    TrigIn0,
    /// Capture input 1
    TrigIn1,
    /// Capture input 2
    TrigIn2,
    /// Capture input 3
    TrigIn3,
    /// Capture input 4
    TrigIn4,
    /// Capture input 5
    TrigIn5,
    /// Capture input 6
    TrigIn6,
    /// Capture input 7
    TrigIn7,
    /// Capture input 8
    TrigIn8,
    /// Capture input 9
    TrigIn9,
    /// Capture input 10
    TrigIn10,
    /// Capture input 11
    TrigIn11,
    /// Capture input 12
    TrigIn12,
    /// Capture input 13
    TrigIn13,
    /// Capture input 14
    TrigIn14,
    /// Capture input 15
    TrigIn15,
    /// Capture input 16
    TrigIn16,
    /// Capture input 17
    TrigIn17,
    /// Capture input 18
    TrigIn18,
    /// Capture input 19
    TrigIn19,
    /// Capture input 20
    TrigIn20,
    /// Capture input 21
    TrigIn21,
    /// Capture input 22
    TrigIn22,
    /// Capture input 23
    TrigIn23,
    /// Capture input 24
    TrigIn24,
}

const TIMER_CHANNELS_ARR: [TimerChannelNum; CHANNEL_PER_MODULE] = [
    TimerChannelNum::Channel0,
    TimerChannelNum::Channel1,
    TimerChannelNum::Channel2,
    TimerChannelNum::Channel3,
];

static WAKERS: [AtomicWaker; TOTAL_CHANNELS] = [const { AtomicWaker::new() }; TOTAL_CHANNELS];

#[derive(PartialEq, Clone, Copy)]
/// Enum representing the edge type for capture channels.
pub enum CaptureChEdge {
    /// Rising edge
    Rising,
    /// Falling edge
    Falling,
}

mod sealed {
    /// simply seal a trait
    pub trait Sealed {}
}

/// Driver mode.
#[allow(private_bounds)]
pub trait Mode: sealed::Sealed {}

/// Blocking mode.
pub struct Blocking;
impl sealed::Sealed for Blocking {}
impl Mode for Blocking {}

/// Async mode.
pub struct Async;
impl sealed::Sealed for Async {}
impl Mode for Async {}

/// A timer that captures events based on a specified edge and calls a user-defined callback.
pub struct CaptureTimer<'p, M: Mode, P: CaptureEvent> {
    id: usize,
    event_clock_counts: u32,
    clk_freq: u32,
    _phantom: core::marker::PhantomData<M>,
    info: Info,
    event_pin: Peri<'p, P>,
}

/// A timer that counts down to zero and calls a user-defined callback.
pub struct CountingTimer<M: Mode> {
    id: usize,
    clk_freq: u32,
    timeout: u32,
    _phantom: core::marker::PhantomData<M>,
    info: Info,
}

struct Info {
    regs: &'static crate::pac::ctimer0::RegisterBlock,
    inputmux: &'static crate::pac::inputmux::RegisterBlock,
    module: usize,
    channel: usize,
}

trait SealedInstance {
    fn info() -> Info;
}
trait InterruptHandler {
    fn interrupt_enable();
}
/// shared functions between Controller and Target operation
#[allow(private_bounds)]
pub trait Instance: SealedInstance + PeripheralType + 'static + Send + InterruptHandler {
    /// Interrupt for this SPI instance.
    type Interrupt: interrupt::typelevel::Interrupt;
}

/// Interrupt handler for the CTimer modules.
pub struct CtimerInterruptHandler<T: Instance> {
    _phantom: core::marker::PhantomData<T>,
}

impl Info {
    fn cap_timer_interrupt_enable(&self) {
        let reg = self.regs;
        let channel = self.channel;
        match TIMER_CHANNELS_ARR[channel] {
            TimerChannelNum::Channel0 => {
                reg.ccr().modify(|_, w| w.cap0i().set_bit());
            }
            TimerChannelNum::Channel1 => {
                reg.ccr().modify(|_, w| w.cap1i().set_bit());
            }
            TimerChannelNum::Channel2 => {
                reg.ccr().modify(|_, w| w.cap2i().set_bit());
            }
            TimerChannelNum::Channel3 => {
                reg.ccr().modify(|_, w| w.cap3i().set_bit());
            }
        }
    }
    fn input_event_captured(&self) -> bool {
        let reg = self.regs;
        let channel = self.channel;
        match TIMER_CHANNELS_ARR[channel] {
            TimerChannelNum::Channel0 => reg.ccr().read().cap0i().bit_is_clear(),
            TimerChannelNum::Channel1 => reg.ccr().read().cap1i().bit_is_clear(),
            TimerChannelNum::Channel2 => reg.ccr().read().cap2i().bit_is_clear(),
            TimerChannelNum::Channel3 => reg.ccr().read().cap3i().bit_is_clear(),
        }
    }

    fn cap_timer_interrupt_disable(&self) {
        let reg = self.regs;
        let channel = self.channel;
        match TIMER_CHANNELS_ARR[channel] {
            TimerChannelNum::Channel0 => {
                reg.ccr().modify(|_, w| w.cap0i().clear_bit());
            }
            TimerChannelNum::Channel1 => {
                reg.ccr().modify(|_, w| w.cap1i().clear_bit());
            }
            TimerChannelNum::Channel2 => {
                reg.ccr().modify(|_, w| w.cap2i().clear_bit());
            }
            TimerChannelNum::Channel3 => {
                reg.ccr().modify(|_, w| w.cap3i().clear_bit());
            }
        }
    }
    fn cap_timer_enable_rising_edge_event(&self) {
        let reg = self.regs;
        let channel = self.channel;
        match TIMER_CHANNELS_ARR[channel] {
            TimerChannelNum::Channel0 => {
                reg.ccr().modify(|_, w| w.cap0re().set_bit());
            }
            TimerChannelNum::Channel1 => {
                reg.ccr().modify(|_, w| w.cap1re().set_bit());
            }
            TimerChannelNum::Channel2 => {
                reg.ccr().modify(|_, w| w.cap2re().set_bit());
            }
            TimerChannelNum::Channel3 => {
                reg.ccr().modify(|_, w| w.cap3re().set_bit());
            }
        }
    }
    fn cap_timer_enable_falling_edge_event(&self) {
        let reg = self.regs;
        let channel = self.channel;
        match TIMER_CHANNELS_ARR[channel] {
            TimerChannelNum::Channel0 => {
                reg.ccr().modify(|_, w| w.cap0fe().set_bit());
            }
            TimerChannelNum::Channel1 => {
                reg.ccr().modify(|_, w| w.cap1fe().set_bit());
            }
            TimerChannelNum::Channel2 => {
                reg.ccr().modify(|_, w| w.cap2fe().set_bit());
            }
            TimerChannelNum::Channel3 => {
                reg.ccr().modify(|_, w| w.cap3fe().set_bit());
            }
        }
    }
    fn cap_timer_disable_rising_edge_event(&self) {
        let reg = self.regs;
        let channel = self.channel;
        match TIMER_CHANNELS_ARR[channel] {
            TimerChannelNum::Channel0 => {
                reg.ccr().modify(|_, w| w.cap0re().clear_bit());
            }
            TimerChannelNum::Channel1 => {
                reg.ccr().modify(|_, w| w.cap1re().clear_bit());
            }
            TimerChannelNum::Channel2 => {
                reg.ccr().modify(|_, w| w.cap2re().clear_bit());
            }
            TimerChannelNum::Channel3 => {
                reg.ccr().modify(|_, w| w.cap3re().clear_bit());
            }
        }
    }
    fn cap_timer_disable_falling_edge_event(&self) {
        let reg = self.regs;
        let channel = self.channel;
        match TIMER_CHANNELS_ARR[channel] {
            TimerChannelNum::Channel0 => {
                reg.ccr().modify(|_, w| w.cap0fe().clear_bit());
            }
            TimerChannelNum::Channel1 => {
                reg.ccr().modify(|_, w| w.cap1fe().clear_bit());
            }
            TimerChannelNum::Channel2 => {
                reg.ccr().modify(|_, w| w.cap2fe().clear_bit());
            }
            TimerChannelNum::Channel3 => {
                reg.ccr().modify(|_, w| w.cap3fe().clear_bit());
            }
        }
    }
    fn count_timer_enable_interrupt(&self) {
        let reg = self.regs;
        let channel = self.channel;
        match TIMER_CHANNELS_ARR[channel] {
            TimerChannelNum::Channel0 => {
                reg.mcr().modify(|_, w| w.mr0i().set_bit());
            }
            TimerChannelNum::Channel1 => {
                reg.mcr().modify(|_, w| w.mr1i().set_bit());
            }
            TimerChannelNum::Channel2 => {
                reg.mcr().modify(|_, w| w.mr2i().set_bit());
            }
            TimerChannelNum::Channel3 => {
                reg.mcr().modify(|_, w| w.mr3i().set_bit());
            }
        }
    }
    fn count_timer_disable_interrupt(&self) {
        let reg = self.regs;
        let channel = self.channel;
        match TIMER_CHANNELS_ARR[channel] {
            TimerChannelNum::Channel0 => {
                reg.mcr().modify(|_, w| w.mr0i().clear_bit());
            }
            TimerChannelNum::Channel1 => {
                reg.mcr().modify(|_, w| w.mr1i().clear_bit());
            }
            TimerChannelNum::Channel2 => {
                reg.mcr().modify(|_, w| w.mr2i().clear_bit());
            }
            TimerChannelNum::Channel3 => {
                reg.mcr().modify(|_, w| w.mr3i().clear_bit());
            }
        }
    }

    fn has_count_timer_expired(&self) -> bool {
        let reg = self.regs;
        let channel = self.channel;

        match TIMER_CHANNELS_ARR[channel] {
            TimerChannelNum::Channel0 => reg.mcr().read().mr0i().bit_is_clear(),
            TimerChannelNum::Channel1 => reg.mcr().read().mr1i().bit_is_clear(),
            TimerChannelNum::Channel2 => reg.mcr().read().mr2i().bit_is_clear(),
            TimerChannelNum::Channel3 => reg.mcr().read().mr3i().bit_is_clear(),
        }
    }

    fn pwm_get_clock_freq(&self) -> u32 {
        // SAFETY: This has no safety impact as we are getting a singleton register instance here and its dropped it the end of the function
        let reg = unsafe { Clkctl1::steal() };

        let clksel = reg.ct32bitfclksel(self.channel).read().sel().variant();
        let mut freq: u32 = 0;

        if let Some(clk) = clksel {
            match clk {
                Sel::MainClk => {
                    freq = ClockConfig::crystal().main_clk.get_clock_rate().unwrap();
                }
                Sel::SfroClk => {
                    freq = ClockConfig::crystal().sfro.get_clock_rate().unwrap();
                }
                Sel::FfroClk => {
                    freq = ClockConfig::crystal().ffro.get_clock_rate().unwrap();
                }
                Sel::Lposc => {
                    freq = ClockConfig::crystal().lposc.get_clock_rate().unwrap();
                }
                //TODO: Add get clock frequency for clock sources audio pll, mclk_in
                _ => {
                    freq = 0;
                }
            }
        }
        freq
    }

    fn pwm_configure(&self, period: u32) {
        let reg = self.regs;
        let len_channel = self.channel;

        // Use length channel to set PWM cycle length
        reg.mr(len_channel).write(|w|
            //SAFETY: No safety impact as we are writing match register here
            unsafe { w.match_().bits(period) });

        // Set MRnR bit to enable timer reset for register setting PWM length
        match TIMER_CHANNELS_ARR[len_channel] {
            TimerChannelNum::Channel0 => {
                reg.mcr().modify(|_, w| w.mr0r().set_bit());
            }
            TimerChannelNum::Channel1 => {
                reg.mcr().modify(|_, w| w.mr1r().set_bit());
            }
            TimerChannelNum::Channel2 => {
                reg.mcr().modify(|_, w| w.mr2r().set_bit());
            }
            TimerChannelNum::Channel3 => {
                reg.mcr().modify(|_, w| w.mr3r().set_bit());
            }
        }
    }
}

macro_rules! impl_instance {
    ($n:expr, $channel:expr) => {
        paste! {
            impl SealedInstance for crate::peripherals::[<CTIMER $n _ COUNT _ CHANNEL $channel>] {
                fn info() -> Info {
                    //SAFETY - This code is safe as we are getting register block pointer to do configuration
                    Info {
                        regs: unsafe { &*crate::pac::[<Ctimer $n>]::ptr() },
                        inputmux: unsafe { &*crate::pac::Inputmux::ptr() },
                        module: $n,
                        channel: $channel,
                    }
                }
            }
            impl SealedInstance for crate::peripherals::[<CTIMER $n _ CAPTURE _ CHANNEL $channel>] {
                fn info() -> Info {
                    Info {
                        regs: unsafe { &*crate::pac::[<Ctimer $n>]::ptr() },
                        inputmux: unsafe { &*crate::pac::Inputmux::ptr() },
                        module: $n,
                        channel: $channel,
                    }
                }
            }
            impl Instance for crate::peripherals::[<CTIMER $n _ COUNT _ CHANNEL $channel>] {
                type Interrupt = crate::interrupt::typelevel::[<CTIMER $n>];
            }
            impl Instance for crate::peripherals::[<CTIMER $n _ CAPTURE _ CHANNEL $channel>] {
                type Interrupt = crate::interrupt::typelevel::[<CTIMER $n>];
            }

            impl InterruptHandler for  crate::peripherals::[<CTIMER $n _ COUNT _ CHANNEL $channel>] {
                fn interrupt_enable() {
                    unsafe {
                        interrupt::[<CTIMER $n>].unpend();
                        interrupt::[<CTIMER $n>].enable();
                    }
                }
            }

            impl InterruptHandler for  crate::peripherals::[<CTIMER $n _ CAPTURE _ CHANNEL $channel>] {
                fn interrupt_enable() {
                    unsafe {
                        interrupt::[<CTIMER $n>].unpend();
                        interrupt::[<CTIMER $n>].enable();
                    }
                }
            }
        }
    };
}

impl_instance!(0, 0); // CTIMER0 Channel 0
impl_instance!(0, 1); // CTIMER0 Channel 1
impl_instance!(0, 2); // CTIMER0 Channel 2
impl_instance!(0, 3); // CTIMER0 Channel 3

impl_instance!(1, 0); // CTIMER1 Channel 0
impl_instance!(1, 1); // CTIMER1 Channel 1
impl_instance!(1, 2); // CTIMER1 Channel 2
impl_instance!(1, 3); // CTIMER1 Channel 3

impl_instance!(2, 0); // CTIMER2 Channel 0
impl_instance!(2, 1); // CTIMER2 Channel 1
impl_instance!(2, 2); // CTIMER2 Channel 2
impl_instance!(2, 3); // CTIMER2 Channel 3

impl_instance!(3, 0); // CTIMER3 Channel 0
impl_instance!(3, 1); // CTIMER3 Channel 1
impl_instance!(3, 2); // CTIMER3 Channel 2
impl_instance!(3, 3); // CTIMER3 Channel 3

impl_instance!(4, 0); // CTIMER4 Channel 0
impl_instance!(4, 1); // CTIMER4 Channel 1
impl_instance!(4, 2); // CTIMER4 Channel 2
impl_instance!(4, 3); // CTIMER4 Channel 3

impl From<TriggerInput> for crate::pac::inputmux::ct32bit_cap::ct32bit_cap_sel::CapnSel {
    fn from(input: TriggerInput) -> Self {
        match input {
            TriggerInput::TrigIn0 => Self::CtInp0,
            TriggerInput::TrigIn1 => Self::CtInp1,
            TriggerInput::TrigIn2 => Self::CtInp2,
            TriggerInput::TrigIn3 => Self::CtInp4,
            TriggerInput::TrigIn5 => Self::CtInp5,
            TriggerInput::TrigIn6 => Self::CtInp6,
            TriggerInput::TrigIn7 => Self::CtInp7,
            TriggerInput::TrigIn8 => Self::CtInp8,
            TriggerInput::TrigIn9 => Self::CtInp9,
            TriggerInput::TrigIn10 => Self::CtInp10,
            TriggerInput::TrigIn11 => Self::CtInp11,
            TriggerInput::TrigIn12 => Self::CtInp12,
            TriggerInput::TrigIn13 => Self::CtInp13,
            TriggerInput::TrigIn14 => Self::CtInp14,
            TriggerInput::TrigIn15 => Self::CtInp15,
            TriggerInput::TrigIn16 => Self::SharedI2s0Ws,
            TriggerInput::TrigIn17 => Self::SharedI2s1Ws,
            TriggerInput::TrigIn18 => Self::Usb1FrameToggle,
            _ => panic!("Invalid input event for capture timer"),
        }
    }
}

impl<'p, M: Mode, P: CaptureEvent> CaptureTimer<'p, M, P> {
    /// Returns the captured clock count
    /// Captured clock = (Capture value - previous counter value)
    fn get_event_capture_time_us(&self) -> u32 {
        let time_float = (self.event_clock_counts as f32 / self.clk_freq as f32) * 1000000.0;
        let integer_part = time_float as u32;
        integer_part
    }

    fn reset_and_enable(&self) {
        let reg = self.info.regs;
        if reg.tcr().read().cen().is_disabled() {
            reg.tcr().write(|w| w.crst().enabled());
            reg.tcr().write(|w| w.crst().disabled());
            reg.tcr().write(|w| w.cen().enabled());
        }
    }

    /// Start the capture timer
    fn start(&mut self, edge: CaptureChEdge) {
        let module = self.info.module;
        let channel = self.info.channel;

        self.capture_timer_setup(edge);

        let inputmux = self.info.inputmux;

        self.event_pin.configure_for_event_capture();

        self.info.cap_timer_interrupt_enable();

        inputmux
            .ct32bit_cap(module)
            .ct32bit_cap_sel(channel)
            .modify(|_, w| w.capn_sel().variant(self.event_pin.get_trigger_input().into()));

        self.reset_and_enable();
    }

    fn capture_timer_setup(&self, edge: CaptureChEdge) {
        match edge {
            CaptureChEdge::Rising => {
                self.info.cap_timer_enable_rising_edge_event();
            }
            CaptureChEdge::Falling => {
                self.info.cap_timer_enable_falling_edge_event();
            }
        }
    }
}

impl<'p, P: CaptureEvent> CaptureTimer<'p, Async, P> {
    /// Creates a new `CaptureTimer` in asynchronous mode.
    pub fn new_async<T: Instance>(_inst: Peri<'p, T>, pin: Peri<'p, P>, clk: impl ConfigurableClock) -> Self {
        let info = T::info();
        let module = info.module;
        T::interrupt_enable();
        Self {
            id: COUNT_CHANNEL + module * CHANNEL_PER_MODULE + info.channel,
            event_clock_counts: 0,
            clk_freq: clk.get_clock_rate().unwrap(),
            _phantom: core::marker::PhantomData,
            info,
            event_pin: pin,
        }
    }

    /// Waits asynchronously for the capture timer to record an event timestamp.
    /// This API can capture time till the counter has not crossed the original position after rollover
    /// Once the counter crosses the original position, the captured time is not accurate
    pub async fn capture_event_time_us(&mut self, edge: CaptureChEdge) -> u32 {
        let reg = self.info.regs;
        self.start(edge);

        self.event_clock_counts = reg.tc().read().bits(); // Take the initial count

        // Implementation of waiting for the interrupt
        poll_fn(|cx| {
            WAKERS[self.id].register(cx.waker());

            if self.info.input_event_captured() {
                let curr_event_clock_count = reg.cr(self.info.channel).read().bits();
                let prev_event_clock_count = self.event_clock_counts;
                if curr_event_clock_count < prev_event_clock_count {
                    self.event_clock_counts = (u32::MAX - prev_event_clock_count) + curr_event_clock_count + 1_u32;
                } else {
                    self.event_clock_counts = curr_event_clock_count - prev_event_clock_count;
                }
                Poll::Ready(self.get_event_capture_time_us())
            } else {
                Poll::Pending
            }
        })
        .await
    }

    /// Trigger capture twice, return time us between these two capture
    /// TODO: https://github.com/OpenDevicePartnership/embassy-imxrt/issues/229
    pub async fn capture_cycle_time_us(&mut self, edge: CaptureChEdge) -> u32 {
        let reg = self.info.regs;
        self.start(edge);
        let mut timer_hist = 0;
        let mut first_captured = false;

        // Implementation of waiting for the interrupt
        poll_fn(|cx| {
            WAKERS[self.id].register(cx.waker());

            if self.info.input_event_captured() {
                // First time capture, store data into timer hist and reenable interrupt
                if first_captured == false {
                    timer_hist = reg.cr(self.info.channel).read().bits();
                    first_captured = true;
                    self.info.cap_timer_interrupt_enable();
                    Poll::Pending
                } else {
                    // Second time capture, and minus timer hist to calculate event_clock_counts
                    let curr_event_clock_count = reg.cr(self.info.channel).read().bits();
                    if curr_event_clock_count < timer_hist {
                        self.event_clock_counts = (u32::MAX - timer_hist) + curr_event_clock_count + 1_u32;
                    } else {
                        self.event_clock_counts = curr_event_clock_count - timer_hist;
                    }
                    self.info.cap_timer_interrupt_disable();
                    Poll::Ready(self.get_event_capture_time_us())
                }
            } else {
                Poll::Pending
            }
        })
        .await
    }
}

impl<'p, P: CaptureEvent> CaptureTimer<'p, Blocking, P> {
    /// Creates a new `CaptureTimer` in blocking mode.
    pub fn new_blocking<T: Instance>(_inst: Peri<'p, T>, pin: Peri<'p, P>, clk: impl ConfigurableClock) -> Self {
        let info = T::info();
        let module = info.module;
        T::interrupt_enable();
        Self {
            id: COUNT_CHANNEL + module * CHANNEL_PER_MODULE + info.channel,
            event_clock_counts: 0,
            clk_freq: clk.get_clock_rate().unwrap(),
            _phantom: core::marker::PhantomData,
            info,
            event_pin: pin,
        }
    }
    /// Waits synchronously for the capture timer
    /// This API can capture time till the counter has not crossed the original position after rollover
    /// Once the counter crosses the original position, the captured time is not accurate
    pub fn capture_event_time_us(&mut self, edge: CaptureChEdge) -> u32 {
        let reg = self.info.regs;
        self.start(edge);

        self.event_clock_counts = reg.tc().read().bits(); // Take the initial count

        loop {
            if self.info.input_event_captured() {
                let curr_event_clock_count = reg.cr(self.info.channel).read().bits();
                let prev_event_clock_count = self.event_clock_counts;
                if curr_event_clock_count < prev_event_clock_count {
                    self.event_clock_counts = (u32::MAX - prev_event_clock_count) + curr_event_clock_count + 1_u32;
                } else {
                    self.event_clock_counts = curr_event_clock_count - prev_event_clock_count;
                }
                return self.get_event_capture_time_us();
            }
        }
    }
    /// Trigger capture twice, return time us between these two capture
    pub fn capture_cycle_time_us(&mut self, edge: CaptureChEdge) -> u32 {
        let reg = self.info.regs;
        self.start(edge);
        let mut timer_hist = 0;
        let mut first_captured = false;

        loop {
            if self.info.input_event_captured() {
                // First time capture, store data into timer hist and reenable interrupt
                if first_captured == false {
                    timer_hist = reg.cr(self.info.channel).read().bits();
                    first_captured = true;
                    self.info.cap_timer_interrupt_enable();
                } else {
                    // Second time capture, and minus timer hist to calculate event_clock_counts
                    let curr_event_clock_count = reg.cr(self.info.channel).read().bits();
                    if curr_event_clock_count < timer_hist {
                        self.event_clock_counts = (u32::MAX - timer_hist) + curr_event_clock_count + 1_u32;
                    } else {
                        self.event_clock_counts = curr_event_clock_count - timer_hist;
                    }
                    self.info.cap_timer_interrupt_disable();
                    return self.get_event_capture_time_us();
                }
            }
        }
    }
}

impl<M: Mode> CountingTimer<M> {
    fn reset_and_enable(&self) {
        let reg = self.info.regs;
        if reg.tcr().read().cen().is_disabled() {
            reg.tcr().write(|w| w.crst().enabled());
            reg.tcr().write(|w| w.crst().disabled());
            reg.tcr().write(|w| w.cen().enabled());
        }
    }

    fn start(&mut self, count_us: u32) {
        let info = &self.info;
        let dur = (count_us as u64 * self.clk_freq as u64) / 1000000;
        let cycles = dur as u32;
        let reg = self.info.regs;
        let channel = self.info.channel;
        let curr_time = reg.tc().read().bits();
        if dur > (u32::MAX) as u64 {
            panic!("Count value is too large");
        }

        self.timeout = cycles;

        if curr_time as u64 + cycles as u64 > u32::MAX as u64 {
            let leftover = (curr_time as u64 + cycles as u64) - u32::MAX as u64;
            let cycles = leftover as u32;
            unsafe {
                // SAFETY: It has no safety impact as we are writing new value to match register here
                reg.mr(channel).write(|w| w.match_().bits(cycles));
            }
        } else {
            unsafe {
                //SAFETY: It has no safety impact as we are writing new value to match register here
                reg.mr(channel).write(|w| w.match_().bits(curr_time + cycles));
            }
        }

        info.count_timer_enable_interrupt();

        self.reset_and_enable();
    }
}

impl<'p> CountingTimer<Async> {
    /// Creates a new `CountingTimer` in asynchronous mode.
    pub fn new_async<T: Instance>(_inst: Peri<'p, T>, clk: impl ConfigurableClock) -> Self {
        let info = T::info();
        T::interrupt_enable();
        Self {
            id: info.module * CHANNEL_PER_MODULE + info.channel,
            clk_freq: clk.get_clock_rate().unwrap(),
            timeout: 0,
            _phantom: core::marker::PhantomData,
            info,
        }
    }
    /// Waits asynchronously for the countdown timer to complete.
    pub async fn wait_us(&mut self, count_us: u32) {
        self.start(count_us);

        // Implementation of waiting for the interrupt
        poll_fn(|cx| {
            // Register the waker
            WAKERS[self.id].register(cx.waker());

            if self.info.has_count_timer_expired() {
                return Poll::Ready(());
            }
            Poll::Pending
        })
        .await;
    }
}

impl<'p> CountingTimer<Blocking> {
    /// Creates a new `CountingTimer` in blocking mode.
    pub fn new_blocking<T: Instance>(_inst: Peri<'p, T>, clk: impl ConfigurableClock) -> Self {
        let info = T::info();
        T::interrupt_enable();
        Self {
            id: info.module * CHANNEL_PER_MODULE + info.channel,
            clk_freq: clk.get_clock_rate().unwrap(),
            timeout: 0,
            _phantom: core::marker::PhantomData,
            info,
        }
    }

    /// Waits synchronously for the countdown timer to complete.
    pub fn wait_us(&mut self, count_us: u32) {
        self.start(count_us);

        loop {
            if self.info.has_count_timer_expired() {
                break;
            }
        }
    }
}

impl<M: Mode> Drop for CountingTimer<M> {
    fn drop(&mut self) {
        self.info.count_timer_disable_interrupt();
        self.info.regs.mr(self.info.channel).write(|w| unsafe {
            // SAFETY: It has no safety impact as we are clearing match register here
            w.match_().bits(0)
        });
    }
}

impl<'p, M: Mode, P: CaptureEvent> Drop for CaptureTimer<'p, M, P> {
    fn drop(&mut self) {
        self.info.cap_timer_interrupt_disable();
        self.info.cap_timer_disable_falling_edge_event();
        self.info.cap_timer_disable_rising_edge_event();
    }
}

/// Basic PWM Object, Consumes `CTimer` peripheral hardware instances for match channel and PWM length channel on construction
pub struct CTimerPwm<'p> {
    _lifetime: PhantomData<&'p ()>,
    _periodchannel: &'p CTimerPwmPeriodChannel<'p>,
    period: MicroSeconds,
    count_max: u32,
    info: Info,
}

/// Basic PWM Length channel Object, Consumes `CTimer` peripheral hardware instances for match channel and PWM length channel on construction
pub struct CTimerPwmPeriodChannel<'p> {
    _lifetime: PhantomData<&'p ()>,
    period: MicroSeconds,
    count_max: u32,
    info: Info,
}

impl embedded_hal_02::Pwm for CTimerPwm<'_> {
    type Channel = ();
    type Time = MicroSeconds;
    type Duty = CentiPercent;

    fn disable(&mut self, _: ()) {
        // To disable PWM:
        // Clear PWM enable bit in PWM control register

        let reg = self.info.regs;
        match TIMER_CHANNELS_ARR[self.info.channel] {
            TimerChannelNum::Channel0 => {
                reg.pwmc().modify(|_, w| w.pwmen0().match_());
            }
            TimerChannelNum::Channel1 => {
                reg.pwmc().modify(|_, w| w.pwmen1().match_());
            }
            TimerChannelNum::Channel2 => {
                reg.pwmc().modify(|_, w| w.pwmen2().match_());
            }
            TimerChannelNum::Channel3 => {
                reg.pwmc().modify(|_, w| w.pwmen3().match_());
            }
        }
    }

    fn enable(&mut self, _: ()) {
        let reg = self.info.regs;

        // Set duty cycle to 0
        self.set_duty((), CentiPercent(0, 0));

        // To enable PWM output for a channel:
        // 1. Disable stop and reset when match register matches the value in TC
        // 2. Enable interrupt generation when match register matches the value in TC
        // 3. Clear external match bit in match control register
        // 4. Write 2 to external match control bit to set match output bit/pin when match register matches the value in TC
        // 5. Clear interrupt flag
        // 6. Set PWM enable bit in PWM control register

        match TIMER_CHANNELS_ARR[self.info.channel] {
            TimerChannelNum::Channel0 => {
                reg.mcr().modify(|_, w| w.mr0r().clear_bit());
                reg.mcr().modify(|_, w| w.mr0s().clear_bit());
                reg.mcr().modify(|_, w| w.mr0i().set_bit());

                reg.emr().modify(|_, w| w.em0().clear_bit());
                reg.emr().modify(|_, w| w.emc0().set_());

                reg.ir().modify(|_, w| w.mr0int().clear_bit_by_one());

                reg.pwmc().modify(|_, w| w.pwmen0().pwm());
            }
            TimerChannelNum::Channel1 => {
                reg.mcr().modify(|_, w| w.mr1r().clear_bit());
                reg.mcr().modify(|_, w| w.mr1s().clear_bit());
                reg.mcr().modify(|_, w| w.mr1i().set_bit());

                reg.emr().modify(|_, w| w.em1().clear_bit());
                reg.emr().modify(|_, w| w.emc1().set_());

                // Write 1 to IR bit to clear interrupt
                reg.ir().modify(|_, w| w.mr1int().clear_bit_by_one());

                reg.pwmc().modify(|_, w| w.pwmen1().pwm());
            }
            TimerChannelNum::Channel2 => {
                reg.mcr().modify(|_, w| w.mr2r().clear_bit());
                reg.mcr().modify(|_, w| w.mr2s().clear_bit());
                reg.mcr().modify(|_, w| w.mr2i().set_bit());

                reg.emr().modify(|_, w| w.em2().clear_bit());
                reg.emr().modify(|_, w| w.emc2().set_());

                reg.ir().modify(|_, w| w.mr2int().clear_bit_by_one());

                reg.pwmc().modify(|_, w| w.pwmen2().pwm());
            }
            TimerChannelNum::Channel3 => {
                reg.mcr().modify(|_, w| w.mr3r().clear_bit());
                reg.mcr().modify(|_, w| w.mr3s().clear_bit());
                reg.mcr().modify(|_, w| w.mr3i().set_bit());

                reg.emr().modify(|_, w| w.em3().clear_bit());
                reg.emr().modify(|_, w| w.emc3().set_());

                reg.ir().modify(|_, w| w.mr3int().clear_bit_by_one());

                reg.pwmc().modify(|_, w| w.pwmen3().pwm());
            }
        }

        // Reset and enable timer
        if reg.tcr().read().cen().is_disabled() {
            reg.tcr().write(|w| w.crst().set_bit());
            reg.tcr().write(|w| w.crst().clear_bit());
            reg.tcr().write(|w| w.cen().set_bit());
        }
    }

    fn get_period(&self) -> Self::Time {
        self.period
    }

    fn get_duty(&self, _: ()) -> Self::Duty {
        let reg = self.info.regs;
        let scaled = reg.mr(self.info.channel).read().bits();

        CentiPercent::from_scaled(self.count_max - scaled, self.count_max)
    }

    fn get_max_duty(&self) -> Self::Duty {
        CentiPercent::MAX
    }

    fn set_duty(&mut self, _: (), duty: Self::Duty) {
        let scaled = duty.as_scaled(self.count_max);
        let reg = self.info.regs;

        // PWM output is low at the beginning of PWM cycle
        // PWM output is set to high when timer count reaches match register value
        // For active high PWM, set match register such that output is high for PWM cycle length*dutycycle
        reg.mr(self.info.channel).write(|w|
            // SAFETY: No safety impact as we are writing match register here
            // FieldWriter::bits will clear field first, than write new value, cause PWM stay low for a period,
            // match_ is bits[0..31], so we can use REG::bits to workaround the problem. 
            unsafe { w.bits(self.count_max - scaled)});
    }

    fn set_period<P>(&mut self, period: P)
    where
        P: Into<Self::Time>,
    {
        // Updating period for one channel will impact all channels configured for PWM on the same timer
        // Period update also updates duty cycle which can cause an out of spec pulse in PWM output(output could stay low for a PWM period
        // before new duty cycle is updated)
        let clock_rate = Hertz(self.info.pwm_get_clock_freq());

        let requested_pwm_rate: Hertz = period.into().into();

        // period cannot be faster than supplied PWM clock source
        assert!(requested_pwm_rate.0 > 0);
        assert!(requested_pwm_rate.0 <= clock_rate.0 / PWM_PRECISION_CLK_TICKS_PER_PERIOD);

        // Update PWM period length in clock ticks
        self.count_max = clock_rate.0 / requested_pwm_rate.0;

        // Set period through match register
        let periodchannel = &self._periodchannel.info;
        periodchannel.pwm_configure(self.count_max);

        let reg = self.info.regs;
        (0..TIMER_CHANNELS_ARR.len()).for_each(|i| {
            // record current duty cycles
            let mut scaled = reg.mr(i).read().bits();

            // update duty cycle match registers according to new scale factor
            let duty_cycle = CentiPercent::from_scaled(self.count_max - scaled, self.count_max);

            scaled = duty_cycle.as_scaled(self.count_max);

            reg.mr(i).write(|w|
            //SAFETY: No safety impact as we are writing match register here
            unsafe { w.match_().bits(self.count_max - scaled)});
        });
    }
}

/// shorthand for -> Result<T>
pub type Result<T> = core::result::Result<T, Error>;

impl<'p> CTimerPwm<'p> {
    /// Take the `CTimer` instance supplied and use it as a simple PWM driver. Function returns constructed Pwm instance.
    pub fn new<T: Instance>(
        _match_channel: Peri<'p, T>,
        period_channel: &'p CTimerPwmPeriodChannel,
        matchoutput_pin: Peri<'p, impl CTimerMatchOutput>,
    ) -> Result<Self> {
        let channel_info = T::info();

        // Assert if length channel and PWM channel does not belong to same CTimer
        if channel_info.module != period_channel.info.module {
            return Err(Error::PwmChannelMismatch);
        }

        // Configure match output pin
        matchoutput_pin.configure_for_ctimer_match_output();

        Ok(Self {
            _lifetime: PhantomData,
            _periodchannel: period_channel,
            period: period_channel.period,
            count_max: period_channel.count_max,
            info: channel_info,
        })
    }
}

impl<'p> CTimerPwmPeriodChannel<'p> {
    /// Take the `CTimer` instance supplied and use it as a simple PWM driver. Function returns constructed Pwm instance.
    pub fn new<T: Instance>(_length_channel: Peri<'p, T>, period: MicroSeconds) -> Result<Self> {
        let channel_info = T::info();

        let clock_rate = Hertz(channel_info.pwm_get_clock_freq());

        let requested_pwm_rate: Hertz = period.into();

        // we cannot clock faster than the supplied clock rate
        if period.0 == 0 {
            return Err(Error::InvalidPwmPeriod);
        }
        // assure precision is possible (PWM_PRECISION_CLK_TICKS_PER_PERIOD ticks within PWM minimum)
        if requested_pwm_rate.0 > clock_rate.0 / PWM_PRECISION_CLK_TICKS_PER_PERIOD {
            return Err(Error::PwmPrecisionNotSupported);
        }

        // Calculate clock ticks per PWM period
        let period_clock_ticks = clock_rate.0 / requested_pwm_rate.0;

        // Set PWM period
        channel_info.pwm_configure(period_clock_ticks);

        Ok(Self {
            _lifetime: PhantomData,
            period,
            count_max: period_clock_ticks,
            info: channel_info,
        })
    }
}

/// Initializes the timer modules and returns a `CTimerManager` in the initialized state.
pub fn init() {
    // SAFETY: This has no safety impact as we are getting a singleton register instance here and its dropped it the end of the function
    let reg = unsafe { Clkctl1::steal() };

    // Initialization steps from NXP TRM
    //
    // • Enable the clock to the CTIMER in the CLKCTL1_PSCCTL2 register
    //          This enables the register interface and the peripheral function clock.
    // • Clear the CTIMER peripheral reset in the RSTCTL1_PRSTCTL2 register
    // (Section 4.5.4.4) by writing to the RSTCTL1_PRSTCTL2_CLR register (Section 4.5.4.10).
    enable_and_reset::<peripherals::CTIMER0_COUNT_CHANNEL0>();
    enable_and_reset::<peripherals::CTIMER1_COUNT_CHANNEL0>();
    enable_and_reset::<peripherals::CTIMER2_COUNT_CHANNEL0>();
    enable_and_reset::<peripherals::CTIMER3_COUNT_CHANNEL0>();
    enable_and_reset::<peripherals::CTIMER4_COUNT_CHANNEL0>();
    enable_and_reset::<peripherals::PIMCTL>();

    // • Select a clock source for the CTIMER using the appropriate CT32BIT0FCLKSEL
    // register (see Section 4.5.2.55 through Section 4.5.2.59).
    reg.ct32bitfclksel(0).write(|w| w.sel().sfro_clk());
    reg.ct32bitfclksel(1).write(|w| w.sel().sfro_clk());
    reg.ct32bitfclksel(2).write(|w| w.sel().sfro_clk());
    reg.ct32bitfclksel(3).write(|w| w.sel().sfro_clk());
    reg.ct32bitfclksel(4).write(|w| w.sel().sfro_clk());
}

impl<T: Instance> interrupt::typelevel::Handler<T::Interrupt> for CtimerInterruptHandler<T> {
    unsafe fn on_interrupt() {
        let module = T::info().module;
        let reg = T::info().regs;

        let ir = reg.ir().read();

        if ir.mr0int().bit_is_set() {
            reg.mcr().modify(|_, w| w.mr0i().clear_bit());
            reg.ir().modify(|_, w| w.mr0int().clear_bit_by_one());
            reg.mr(0).write(|w| unsafe {
                // SAFETY: It has no safety impact as we are clearing match register here
                w.match_().bits(0)
            });
            WAKERS[module * CHANNEL_PER_MODULE].wake();
        }
        if ir.mr1int().bit_is_set() {
            reg.mcr().modify(|_, w| w.mr1i().clear_bit());
            reg.ir().modify(|_, w| w.mr1int().clear_bit_by_one());
            reg.mr(1).write(|w| unsafe {
                // SAFETY: It has no safety impact as we are clearing match register here
                w.match_().bits(0)
            });
            WAKERS[module * CHANNEL_PER_MODULE + 1].wake();
        }
        if ir.mr2int().bit_is_set() {
            reg.mcr().modify(|_, w| w.mr2i().clear_bit());
            reg.ir().modify(|_, w| w.mr2int().clear_bit_by_one());
            reg.mr(2).write(|w| unsafe {
                // SAFETY: It has no safety impact as we are clearing match register here
                w.match_().bits(0)
            });
            WAKERS[module * CHANNEL_PER_MODULE + 2].wake();
        }
        if ir.mr3int().bit_is_set() {
            reg.mcr().modify(|_, w| w.mr3i().clear_bit());
            reg.ir().modify(|_, w| w.mr3int().clear_bit_by_one());
            reg.mr(3).write(|w| unsafe {
                // SAFETY: It has no safety impact as we are clearing match register here
                w.match_().bits(0)
            });
            WAKERS[module * CHANNEL_PER_MODULE + 3].wake();
        }
        if ir.cr0int().bit_is_set() {
            reg.ccr().modify(|_, w| w.cap0i().clear_bit());
            reg.ir().modify(|_, w| w.cr0int().clear_bit_by_one());
            WAKERS[module * CHANNEL_PER_MODULE + COUNT_CHANNEL].wake();
        }
        if ir.cr1int().bit_is_set() {
            reg.ccr().modify(|_, w| w.cap1i().clear_bit());
            reg.ir().modify(|_, w| w.cr1int().clear_bit_by_one());
            WAKERS[module * CHANNEL_PER_MODULE + COUNT_CHANNEL + 1].wake();
        }
        if ir.cr2int().bit_is_set() {
            reg.ccr().modify(|_, w| w.cap2i().clear_bit());
            reg.ir().modify(|_, w| w.cr2int().clear_bit_by_one());
            WAKERS[module * CHANNEL_PER_MODULE + COUNT_CHANNEL + 2].wake();
        }
        if ir.cr3int().bit_is_set() {
            reg.ccr().modify(|_, w| w.cap3i().clear_bit());
            reg.ir().modify(|_, w| w.cr3int().clear_bit_by_one());
            WAKERS[module * CHANNEL_PER_MODULE + COUNT_CHANNEL + 3].wake();
        }
    }
}

/// A trait for pins that can be used as capture event inputs.
pub trait CaptureEvent: Pin + crate::PeripheralType {
    /// Configures the pin as a capture event input.
    fn configure_for_event_capture(&self);
    /// Get trigger input of event pin
    fn get_trigger_input(&self) -> TriggerInput;
}
macro_rules! impl_pin {
    ($piom_n:ident, $fn:ident, $invert:ident, $trig:ident) => {
        impl CaptureEvent for crate::peripherals::$piom_n {
            fn configure_for_event_capture(&self) {
                self.set_function(crate::iopctl::Function::$fn);
                self.set_drive_mode(DriveMode::PushPull);
                self.set_pull(Pull::None);
                self.set_slew_rate(SlewRate::Slow);
                self.set_drive_strength(DriveStrength::Normal);
                self.disable_analog_multiplex();
                self.enable_input_buffer();
                self.set_input_inverter(Inverter::$invert);
            }

            fn get_trigger_input(&self) -> TriggerInput {
                TriggerInput::$trig
            }
        }
    };
}

// Capture event pins
// We can add all the GPIO pins here which can be used as capture event inputs
// NXP user manual section 8.6.8 and Pin Function Table in section 7.5.3
impl_pin!(PIO0_4, F4, Enabled, TrigIn0);
impl_pin!(PIO0_5, F4, Enabled, TrigIn1);
impl_pin!(PIO0_11, F4, Enabled, TrigIn2);
impl_pin!(PIO0_12, F4, Enabled, TrigIn3);
impl_pin!(PIO0_18, F4, Enabled, TrigIn4);
impl_pin!(PIO0_19, F4, Enabled, TrigIn5);
impl_pin!(PIO0_20, F5, Enabled, TrigIn11);
impl_pin!(PIO0_25, F4, Enabled, TrigIn6);
impl_pin!(PIO0_26, F4, Enabled, TrigIn7);
impl_pin!(PIO1_0, F4, Enabled, TrigIn8);
impl_pin!(PIO1_7, F4, Enabled, TrigIn9);
impl_pin!(PIO1_8, F3, Enabled, TrigIn12);
impl_pin!(PIO1_10, F4, Enabled, TrigIn10);
impl_pin!(PIO1_23, F4, Enabled, TrigIn8);
impl_pin!(PIO1_29, F4, Enabled, TrigIn13);
impl_pin!(PIO2_14, F4, Enabled, TrigIn1);
impl_pin!(PIO2_21, F4, Enabled, TrigIn14);
impl_pin!(PIO2_31, F4, Enabled, TrigIn15);
impl_pin!(PIO3_12, F4, Enabled, TrigIn0);
impl_pin!(PIO3_13, F4, Enabled, TrigIn1);

/// A trait for pins that can be used as CTimer match outputs
pub trait CTimerMatchOutput: Pin + crate::PeripheralType {
    /// Configures the pin as CTimer match output.
    fn configure_for_ctimer_match_output(&self);
}
macro_rules! impl_pin {
    ($piom_n:ident, $fn:ident) => {
        impl CTimerMatchOutput for crate::peripherals::$piom_n {
            fn configure_for_ctimer_match_output(&self) {
                self.set_function(crate::iopctl::Function::$fn);
                self.set_drive_mode(DriveMode::PushPull);
                self.set_pull(Pull::None);
                self.set_slew_rate(SlewRate::Standard);
                self.set_drive_strength(DriveStrength::Normal);
                self.disable_analog_multiplex();
                self.enable_input_buffer();
                self.set_input_inverter(Inverter::Disabled);
            }
        }
    };
}

// CTimer Match output pins
// We can add all the GPIO pins here which can be used as CTimer Match output pins
impl_pin!(PIO0_31, F4);
impl_pin!(PIO2_6, F4);
impl_pin!(PIO2_8, F4);
impl_pin!(PIO3_8, F4);
impl_pin!(PIO3_9, F4);
impl_pin!(PIO3_10, F4);
