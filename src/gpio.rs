//! GPIO

use core::convert::Infallible;
use core::future::Future;
use core::pin::Pin as FuturePin;
use core::task::{Context, Poll};

use crate::interrupt;
use crate::iopctl::IopctlPin;
pub use crate::iopctl::{AnyPin, DriveMode, DriveStrength, Function, Polarity, Pull, SlewRate};
use crate::{into_ref, Peripheral, PeripheralRef};

use embassy_hal_internal::interrupt::InterruptExt;
use embassy_sync::waitqueue::AtomicWaker;

#[allow(clippy::declare_interior_mutable_const)]
const GPIO_WAKER: AtomicWaker = AtomicWaker::new();

// This should be unique per IMXRT package
const PORT_PIN_COUNT: usize = 32;
const PORT_COUNT: usize = 8;

// One waker per pin, this is more than all possible pins as some ports
// have less than 32 pins.
static GPIO_WAKERS: [AtomicWaker; PORT_PIN_COUNT * PORT_COUNT] = [GPIO_WAKER; PORT_PIN_COUNT * PORT_COUNT];

/// Digital input or output level.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum Level {
    /// Logic Low
    Low,
    /// Logic High
    High,
}

impl From<bool> for Level {
    fn from(val: bool) -> Self {
        match val {
            true => Self::High,
            false => Self::Low,
        }
    }
}

impl From<Level> for bool {
    fn from(level: Level) -> bool {
        match level {
            Level::Low => false,
            Level::High => true,
        }
    }
}

/// Interrupt trigger levels.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum InterruptType {
    /// Trigger on level.
    Level,
    /// Trigger on edge.
    Edge,
}

#[cfg(feature = "rt")]
#[interrupt]
#[allow(non_snake_case)]
fn GPIO_INTA() {
    irq_handler(&GPIO_WAKERS);
}

struct BitIter(u32);

impl Iterator for BitIter {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        match self.0.trailing_zeros() {
            32 => None,
            b => {
                self.0 &= !(1 << b);
                Some(b)
            }
        }
    }
}

#[cfg(feature = "rt")]
fn irq_handler<const N: usize>(wakers: &[AtomicWaker; N]) {
    let reg = unsafe { crate::pac::Gpio::steal() };

    for port in 0..PORT_COUNT {
        let stat = reg.intstata(port).read().bits();

        for pin in BitIter(stat) {
            // Clear the interrupt from this pin
            reg.intstata(port).write(|w| unsafe { w.status().bits(1 << pin) });
            // Disable interrupt from this pin
            reg.intena(port)
                .modify(|r, w| unsafe { w.int_en().bits(r.int_en().bits() & !(1 << pin)) });

            wakers[port * 32 + pin as usize].wake();
        }
    }
}

/// Initialize clocks.
/// TODO: Refactor after clocks mod done.
/// This just enables all GPIO port clocks for now.
/// # Safety
///
/// This function enables GPIO INT A interrupt. It should not be called
/// until you are ready to handle the interrupt
pub unsafe fn init() {
    let clkctl1 = crate::pac::Clkctl1::steal();

    let rstctl1 = crate::pac::Rstctl1::steal();

    // Port 0
    clkctl1.pscctl1_set().write(|w| w.hsgpio0_clk_set().set_clock());
    rstctl1.prstctl1_clr().write(|w| w.hsgpio0_rst_clr().clr_reset());

    // Port 1
    clkctl1.pscctl1_set().write(|w| w.hsgpio1_clk_set().set_clock());
    rstctl1.prstctl1_clr().write(|w| w.hsgpio1_rst_clr().clr_reset());

    // Port 2
    clkctl1.pscctl1_set().write(|w| w.hsgpio2_clk_set().set_clock());
    rstctl1.prstctl1_clr().write(|w| w.hsgpio2_rst_clr().clr_reset());

    // Port 3
    clkctl1.pscctl1_set().write(|w| w.hsgpio3_clk_set().set_clock());
    rstctl1.prstctl1_clr().write(|w| w.hsgpio3_rst_clr().clr_reset());

    // Port 4
    clkctl1.pscctl1_set().write(|w| w.hsgpio4_clk_set().set_clock());
    rstctl1.prstctl1_clr().write(|w| w.hsgpio4_rst_clr().clr_reset());

    // Port 5
    clkctl1.pscctl1_set().write(|w| w.hsgpio5_clk_set().set_clock());
    rstctl1.prstctl1_clr().write(|w| w.hsgpio5_rst_clr().clr_reset());

    // Port 6
    clkctl1.pscctl1_set().write(|w| w.hsgpio6_clk_set().set_clock());
    rstctl1.prstctl1_clr().write(|w| w.hsgpio6_rst_clr().clr_reset());

    // Port 7
    clkctl1.pscctl1_set().write(|w| w.hsgpio7_clk_set().set_clock());
    rstctl1.prstctl1_clr().write(|w| w.hsgpio7_rst_clr().clr_reset());

    interrupt::GPIO_INTA.unpend();
    interrupt::GPIO_INTA.enable();
}

/// Flex pin.
///
/// This pin can be either an input or output pin. The output level register bit will
/// remain set while not in output mode, so the pin's level will be 'remembered' when it is not in
/// output mode.
pub struct Flex<'d> {
    pin: PeripheralRef<'d, AnyPin>,
}

impl<'d> Flex<'d> {
    /// New flex pin.
    pub fn new(pin: impl Peripheral<P = impl GpioPin> + 'd) -> Self {
        into_ref!(pin);

        pin.set_function(Function::F0)
            .disable_analog_multiplex()
            .enable_input_buffer();

        Self { pin: pin.map_into() }
    }

    /// Converts pin to input pin
    pub fn set_as_input(&mut self, pull: Pull, polarity: Polarity) {
        self.pin.set_pull(pull).set_input_polarity(polarity);

        self.pin.block().dirclr(self.pin.port()).write(|w|
                // SAFETY: Writing a 0 to bits in this register has no effect,
                // however PAC has it marked unsafe due to using the bits() method.
                // There is not currently a "safe" method for setting a single-bit.
                unsafe { w.dirclrp().bits(1 << self.pin.pin()) });
    }

    /// Converts pin to output pin
    ///
    /// The pin level will be whatever was set before (or low by default). If you want it to begin
    /// at a specific level, call `set_high`/`set_low` on the pin first.
    pub fn set_as_output(&mut self, mode: DriveMode, strength: DriveStrength, slew_rate: SlewRate) {
        self.pin
            .set_pull(Pull::None)
            .set_drive_mode(mode)
            .set_drive_strength(strength)
            .set_slew_rate(slew_rate);

        self.pin.block().dirset(self.pin.port()).write(|w|
                // SAFETY: Writing a 0 to bits in this register has no effect,
                // however PAC has it marked unsafe due to using the bits() method.
                // There is not currently a "safe" method for setting a single-bit.
                unsafe { w.dirsetp().bits(1 << self.pin.pin()) });
    }

    /// Is high?
    pub fn is_high(&self) -> bool {
        !self.is_low()
    }

    /// Is low?
    pub fn is_low(&self) -> bool {
        self.pin.block().b(self.pin.port()).b_(self.pin.pin()).read() == 0
    }

    /// Current level
    pub fn get_level(&self) -> Level {
        self.is_high().into()
    }

    /// Set high
    pub fn set_high(&mut self) {
        self.pin.block().set(self.pin.port()).write(|w|
            // SAFETY: Writing a 0 to bits in this register has no effect,
            // however PAC has it marked unsafe due to using the bits() method.
            // There is not currently a "safe" method for setting a single-bit.
            unsafe { w.setp().bits(1 << self.pin.pin()) });
    }

    /// Set low
    pub fn set_low(&mut self) {
        self.pin.block().clr(self.pin.port()).write(|w|
            // SAFETY: Writing a 0 to bits in this register has no effect,
            // however PAC has it marked unsafe due to using the bits() method.
            // There is not currently a "safe" method for setting a single-bit.
            unsafe { w.clrp().bits(1 << self.pin.pin()) });
    }

    /// Set level
    pub fn set_level(&mut self, level: Level) {
        match level {
            Level::High => self.set_high(),
            Level::Low => self.set_low(),
        }
    }

    /// Is the output level high?
    pub fn is_set_high(&self) -> bool {
        !self.is_set_low()
    }

    /// Is the output level low?
    pub fn is_set_low(&self) -> bool {
        (self.pin.block().set(self.pin.port()).read().setp().bits() & (1 << self.pin.pin())) == 0
    }

    /// Toggle
    pub fn toggle(&mut self) {
        self.pin.block().not(self.pin.port()).write(|w|
            // SAFETY: Writing a 0 to bits in this register has no effect,
            // however PAC has it marked unsafe due to using the bits() method.
            // There is not currently a "safe" method for setting a single-bit.
            unsafe { w.notp().bits(1 << self.pin.pin()) });
    }

    /// Wait until the pin is high. If it is already high, return immediately.
    #[inline]
    pub async fn wait_for_high(&mut self) {
        InputFuture::new(self.pin.reborrow(), InterruptType::Level, Level::High).await;
    }

    /// Wait until the pin is low. If it is already low, return immediately.
    #[inline]
    pub async fn wait_for_low(&mut self) {
        InputFuture::new(self.pin.reborrow(), InterruptType::Level, Level::Low).await;
    }

    /// Wait for the pin to undergo a transition from low to high.
    #[inline]
    pub async fn wait_for_rising_edge(&mut self) {
        InputFuture::new(self.pin.reborrow(), InterruptType::Edge, Level::High).await;
    }

    /// Wait for the pin to undergo a transition from high to low.
    #[inline]
    pub async fn wait_for_falling_edge(&mut self) {
        InputFuture::new(self.pin.reborrow(), InterruptType::Edge, Level::Low).await;
    }

    /// Wait for the pin to undergo any transition, i.e low to high OR high to low.
    #[inline]
    pub async fn wait_for_any_edge(&mut self) {
        if self.is_high() {
            InputFuture::new(self.pin.reborrow(), InterruptType::Edge, Level::Low).await;
        } else {
            InputFuture::new(self.pin.reborrow(), InterruptType::Edge, Level::High).await;
        }
    }
}

impl<'d> Drop for Flex<'d> {
    fn drop(&mut self) {
        self.pin.reset();
        // TODO: Disable clock for pin's port (assuming ref counted)?
    }
}

/// Input pin
pub struct Input<'d> {
    pin: Flex<'d>,
}

impl<'d> Input<'d> {
    /// New input pin
    pub fn new(pin: impl Peripheral<P = impl GpioPin> + 'd, pull: Pull, polarity: Polarity) -> Self {
        let mut pin = Flex::new(pin);
        pin.set_as_input(pull, polarity);
        Self { pin }
    }

    /// Is high?
    pub fn is_high(&self) -> bool {
        self.pin.is_high()
    }

    /// Is low?
    pub fn is_low(&self) -> bool {
        self.pin.is_low()
    }

    /// Input level
    pub fn get_level(&self) -> Level {
        self.pin.get_level()
    }

    /// Wait until the pin is high. If it is already high, return immediately.
    #[inline]
    pub async fn wait_for_high(&mut self) {
        self.pin.wait_for_high().await;
    }

    /// Wait until the pin is low. If it is already low, return immediately.
    #[inline]
    pub async fn wait_for_low(&mut self) {
        self.pin.wait_for_low().await;
    }

    /// Wait for the pin to undergo a transition from low to high.
    #[inline]
    pub async fn wait_for_rising_edge(&mut self) {
        self.pin.wait_for_rising_edge().await;
    }

    /// Wait for the pin to undergo a transition from high to low.
    #[inline]
    pub async fn wait_for_falling_edge(&mut self) {
        self.pin.wait_for_falling_edge().await;
    }

    /// Wait for the pin to undergo any transition, i.e low to high OR high to low.
    #[inline]
    pub async fn wait_for_any_edge(&mut self) {
        self.pin.wait_for_any_edge().await;
    }
}

#[must_use = "futures do nothing unless you `.await` or poll them"]
struct InputFuture<'d> {
    pin: PeripheralRef<'d, AnyPin>,
}

impl<'d> InputFuture<'d> {
    fn new(pin: impl Peripheral<P = impl GpioPin> + 'd, int_type: InterruptType, level: Level) -> Self {
        into_ref!(pin);

        // Clear any existing pending interrupt on this pin
        pin.block()
            .intstata(pin.port())
            .write(|w| unsafe { w.status().bits(1 << pin.pin()) });

        /* Pin interrupt configuration */
        pin.block().intedg(pin.port()).modify(|r, w| match int_type {
            InterruptType::Edge => unsafe { w.bits(r.bits() | (1 << pin.pin())) },
            InterruptType::Level => unsafe { w.bits(r.bits() & !(1 << pin.pin())) },
        });

        pin.block().intpol(pin.port()).modify(|r, w| match level {
            Level::High => unsafe { w.bits(r.bits() & !(1 << pin.pin())) },
            Level::Low => unsafe { w.bits(r.bits() | (1 << pin.pin())) },
        });

        // Enable pin interrupt on GPIO INT A
        pin.block()
            .intena(pin.port())
            .modify(|r, w| unsafe { w.int_en().bits(r.int_en().bits() | (1 << pin.pin())) });

        Self { pin: pin.map_into() }
    }
}

impl<'d> Future for InputFuture<'d> {
    type Output = ();

    fn poll(self: FuturePin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // We need to register/re-register the waker for each poll because any
        // calls to wake will deregister the waker.
        let waker = &GPIO_WAKERS[self.pin.pin_port()];
        waker.register(cx.waker());

        // Double check that the pin interrut has been disabled by IRQ handler
        if self.pin.block().intena(self.pin.port()).read().bits() & (1 << self.pin.pin()) == 0 {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    }
}

/// Output pin
pub struct Output<'d> {
    pin: Flex<'d>,
}

impl<'d> Output<'d> {
    /// New output pin
    pub fn new(
        pin: impl Peripheral<P = impl GpioPin> + 'd,
        initial_output: Level,
        mode: DriveMode,
        strength: DriveStrength,
        slew_rate: SlewRate,
    ) -> Self {
        let mut pin = Flex::new(pin);
        pin.set_level(initial_output);
        pin.set_as_output(mode, strength, slew_rate);

        Self { pin }
    }

    /// Set high
    pub fn set_high(&mut self) {
        self.pin.set_high();
    }

    /// Set low
    pub fn set_low(&mut self) {
        self.pin.set_low();
    }

    /// Toggle
    pub fn toggle(&mut self) {
        self.pin.toggle();
    }

    /// Set level
    pub fn set_level(&mut self, level: Level) {
        self.pin.set_level(level);
    }

    /// Is set high?
    pub fn is_set_high(&self) -> bool {
        self.pin.is_set_high()
    }

    /// Is set low?
    pub fn is_set_low(&self) -> bool {
        self.pin.is_set_low()
    }

    /// Get output level
    pub fn get_output_level(&self) -> Level {
        self.pin.get_level()
    }
}

trait SealedPin: IopctlPin {
    fn pin_port(&self) -> usize;

    fn port(&self) -> usize {
        self.pin_port() / 32
    }

    fn pin(&self) -> usize {
        self.pin_port() % 32
    }

    fn block(&self) -> crate::pac::Gpio {
        // SAFETY: Assuming GPIO pin specific registers are only accessed through this HAL,
        // this is safe because the HAL ensures ownership or exclusive mutable references
        // to pins.
        unsafe { crate::pac::Gpio::steal() }
    }
}

/// GPIO pin trait.
#[allow(private_bounds)]
pub trait GpioPin: SealedPin + Sized + Into<AnyPin> + 'static {
    /// Type-erase the pin.
    fn degrade(self) -> AnyPin {
        // SAFETY: This is only called within the GpioPin trait, which is only
        // implemented within this module on valid pin peripherals and thus
        // has been verified to be correct.
        unsafe { AnyPin::new(self.port() as u8, self.pin() as u8) }
    }
}

impl SealedPin for AnyPin {
    fn pin_port(&self) -> usize {
        self.pin_port()
    }
}
impl GpioPin for AnyPin {}

macro_rules! impl_pin {
    ($pin_periph:ident, $pin_port:expr, $pin_no:expr) => {
        impl SealedPin for crate::peripherals::$pin_periph {
            fn pin_port(&self) -> usize {
                $pin_port * 32 + $pin_no
            }
        }
        impl GpioPin for crate::peripherals::$pin_periph {}
        impl From<crate::peripherals::$pin_periph> for AnyPin {
            fn from(value: crate::peripherals::$pin_periph) -> Self {
                value.degrade()
            }
        }
    };
}

// GPIO port 0
impl_pin!(PIO0_0, 0, 0);
impl_pin!(PIO0_1, 0, 1);
impl_pin!(PIO0_2, 0, 2);
impl_pin!(PIO0_3, 0, 3);
impl_pin!(PIO0_4, 0, 4);
impl_pin!(PIO0_5, 0, 5);
impl_pin!(PIO0_6, 0, 6);
impl_pin!(PIO0_7, 0, 7);
impl_pin!(PIO0_8, 0, 8);
impl_pin!(PIO0_9, 0, 9);
impl_pin!(PIO0_10, 0, 10);
impl_pin!(PIO0_11, 0, 11);
impl_pin!(PIO0_12, 0, 12);
impl_pin!(PIO0_13, 0, 13);
impl_pin!(PIO0_14, 0, 14);
impl_pin!(PIO0_15, 0, 15);
impl_pin!(PIO0_16, 0, 16);
impl_pin!(PIO0_17, 0, 17);
impl_pin!(PIO0_18, 0, 18);
impl_pin!(PIO0_19, 0, 19);
impl_pin!(PIO0_20, 0, 20);
impl_pin!(PIO0_21, 0, 21);
impl_pin!(PIO0_22, 0, 22);
impl_pin!(PIO0_23, 0, 23);
impl_pin!(PIO0_24, 0, 24);
impl_pin!(PIO0_25, 0, 25);
impl_pin!(PIO0_26, 0, 26);
impl_pin!(PIO0_27, 0, 27);
impl_pin!(PIO0_28, 0, 28);
impl_pin!(PIO0_29, 0, 29);
impl_pin!(PIO0_30, 0, 30);
impl_pin!(PIO0_31, 0, 31);

// GPIO port 1
impl_pin!(PIO1_0, 1, 0);
impl_pin!(PIO1_1, 1, 1);
impl_pin!(PIO1_2, 1, 2);
impl_pin!(PIO1_3, 1, 3);
impl_pin!(PIO1_4, 1, 4);
impl_pin!(PIO1_5, 1, 5);
impl_pin!(PIO1_6, 1, 6);
impl_pin!(PIO1_7, 1, 7);
impl_pin!(PIO1_8, 1, 8);
impl_pin!(PIO1_9, 1, 9);
impl_pin!(PIO1_10, 1, 10);
impl_pin!(PIO1_11, 1, 11);
impl_pin!(PIO1_12, 1, 12);
impl_pin!(PIO1_13, 1, 13);
impl_pin!(PIO1_14, 1, 14);
impl_pin!(PIO1_15, 1, 15);
impl_pin!(PIO1_16, 1, 16);
impl_pin!(PIO1_17, 1, 17);
impl_pin!(PIO1_18, 1, 18);
impl_pin!(PIO1_19, 1, 19);
impl_pin!(PIO1_20, 1, 20);
impl_pin!(PIO1_21, 1, 21);
impl_pin!(PIO1_22, 1, 22);
impl_pin!(PIO1_23, 1, 23);
impl_pin!(PIO1_24, 1, 24);
impl_pin!(PIO1_25, 1, 25);
impl_pin!(PIO1_26, 1, 26);
impl_pin!(PIO1_27, 1, 27);
impl_pin!(PIO1_28, 1, 28);
impl_pin!(PIO1_29, 1, 29);
impl_pin!(PIO1_30, 1, 30);
impl_pin!(PIO1_31, 1, 31);

// GPIO port 2
impl_pin!(PIO2_0, 2, 0);
impl_pin!(PIO2_1, 2, 1);
impl_pin!(PIO2_2, 2, 2);
impl_pin!(PIO2_3, 2, 3);
impl_pin!(PIO2_4, 2, 4);
impl_pin!(PIO2_5, 2, 5);
impl_pin!(PIO2_6, 2, 6);
impl_pin!(PIO2_7, 2, 7);
impl_pin!(PIO2_8, 2, 8);
impl_pin!(PIO2_9, 2, 9);
impl_pin!(PIO2_10, 2, 10);
impl_pin!(PIO2_11, 2, 11);
impl_pin!(PIO2_12, 2, 12);
impl_pin!(PIO2_13, 2, 13);
impl_pin!(PIO2_14, 2, 14);
impl_pin!(PIO2_15, 2, 15);
impl_pin!(PIO2_16, 2, 16);
impl_pin!(PIO2_17, 2, 17);
impl_pin!(PIO2_18, 2, 18);
impl_pin!(PIO2_19, 2, 19);
impl_pin!(PIO2_20, 2, 20);
impl_pin!(PIO2_21, 2, 21);
impl_pin!(PIO2_22, 2, 22);
impl_pin!(PIO2_23, 2, 23);
impl_pin!(PIO2_24, 2, 24);
impl_pin!(PIO2_25, 2, 25);
impl_pin!(PIO2_26, 2, 26);
impl_pin!(PIO2_27, 2, 27);
impl_pin!(PIO2_28, 2, 28);
impl_pin!(PIO2_29, 2, 29);
impl_pin!(PIO2_30, 2, 30);
impl_pin!(PIO2_31, 2, 31);

// GPIO port 3
impl_pin!(PIO3_0, 3, 0);
impl_pin!(PIO3_1, 3, 1);
impl_pin!(PIO3_2, 3, 2);
impl_pin!(PIO3_3, 3, 3);
impl_pin!(PIO3_4, 3, 4);
impl_pin!(PIO3_5, 3, 5);
impl_pin!(PIO3_6, 3, 6);
impl_pin!(PIO3_7, 3, 7);
impl_pin!(PIO3_8, 3, 8);
impl_pin!(PIO3_9, 3, 9);
impl_pin!(PIO3_10, 3, 10);
impl_pin!(PIO3_11, 3, 11);
impl_pin!(PIO3_12, 3, 12);
impl_pin!(PIO3_13, 3, 13);
impl_pin!(PIO3_14, 3, 14);
impl_pin!(PIO3_15, 3, 15);
impl_pin!(PIO3_16, 3, 16);
impl_pin!(PIO3_17, 3, 17);
impl_pin!(PIO3_18, 3, 18);
impl_pin!(PIO3_19, 3, 19);
impl_pin!(PIO3_20, 3, 20);
impl_pin!(PIO3_21, 3, 21);
impl_pin!(PIO3_22, 3, 22);
impl_pin!(PIO3_23, 3, 23);
impl_pin!(PIO3_24, 3, 24);
impl_pin!(PIO3_25, 3, 25);
impl_pin!(PIO3_26, 3, 26);
impl_pin!(PIO3_27, 3, 27);
impl_pin!(PIO3_28, 3, 28);
impl_pin!(PIO3_29, 3, 29);
impl_pin!(PIO3_30, 3, 30);
impl_pin!(PIO3_31, 3, 31);

// GPIO port 4
impl_pin!(PIO4_0, 4, 0);
impl_pin!(PIO4_1, 4, 1);
impl_pin!(PIO4_2, 4, 2);
impl_pin!(PIO4_3, 4, 3);
impl_pin!(PIO4_4, 4, 4);
impl_pin!(PIO4_5, 4, 5);
impl_pin!(PIO4_6, 4, 6);
impl_pin!(PIO4_7, 4, 7);
impl_pin!(PIO4_8, 4, 8);
impl_pin!(PIO4_9, 4, 9);
impl_pin!(PIO4_10, 4, 10);

// GPIO port 7
impl_pin!(PIO7_24, 7, 24);
impl_pin!(PIO7_25, 7, 25);
impl_pin!(PIO7_26, 7, 26);
impl_pin!(PIO7_27, 7, 27);
impl_pin!(PIO7_28, 7, 28);
impl_pin!(PIO7_29, 7, 29);
impl_pin!(PIO7_30, 7, 30);
impl_pin!(PIO7_31, 7, 31);

impl<'d> embedded_hal_02::digital::v2::InputPin for Flex<'d> {
    type Error = Infallible;

    #[inline]
    fn is_high(&self) -> Result<bool, Self::Error> {
        Ok(self.is_high())
    }

    #[inline]
    fn is_low(&self) -> Result<bool, Self::Error> {
        Ok(self.is_low())
    }
}

impl<'d> embedded_hal_02::digital::v2::OutputPin for Flex<'d> {
    type Error = Infallible;

    #[inline]
    fn set_high(&mut self) -> Result<(), Self::Error> {
        self.set_high();
        Ok(())
    }

    #[inline]
    fn set_low(&mut self) -> Result<(), Self::Error> {
        self.set_low();
        Ok(())
    }
}

impl<'d> embedded_hal_02::digital::v2::StatefulOutputPin for Flex<'d> {
    #[inline]
    fn is_set_high(&self) -> Result<bool, Self::Error> {
        Ok(self.is_set_high())
    }

    #[inline]
    fn is_set_low(&self) -> Result<bool, Self::Error> {
        Ok(self.is_set_low())
    }
}

impl<'d> embedded_hal_02::digital::v2::ToggleableOutputPin for Flex<'d> {
    type Error = Infallible;

    #[inline]
    fn toggle(&mut self) -> Result<(), Self::Error> {
        self.toggle();
        Ok(())
    }
}

impl<'d> embedded_hal_02::digital::v2::InputPin for Input<'d> {
    type Error = Infallible;

    #[inline]
    fn is_high(&self) -> Result<bool, Self::Error> {
        Ok(self.is_high())
    }

    #[inline]
    fn is_low(&self) -> Result<bool, Self::Error> {
        Ok(self.is_low())
    }
}

impl<'d> embedded_hal_02::digital::v2::OutputPin for Output<'d> {
    type Error = Infallible;

    #[inline]
    fn set_high(&mut self) -> Result<(), Self::Error> {
        self.set_high();
        Ok(())
    }

    #[inline]
    fn set_low(&mut self) -> Result<(), Self::Error> {
        self.set_low();
        Ok(())
    }
}

impl<'d> embedded_hal_02::digital::v2::StatefulOutputPin for Output<'d> {
    #[inline]
    fn is_set_high(&self) -> Result<bool, Self::Error> {
        Ok(self.is_set_high())
    }

    #[inline]
    fn is_set_low(&self) -> Result<bool, Self::Error> {
        Ok(self.is_set_low())
    }
}

impl<'d> embedded_hal_02::digital::v2::ToggleableOutputPin for Output<'d> {
    type Error = Infallible;

    #[inline]
    fn toggle(&mut self) -> Result<(), Self::Error> {
        self.toggle();
        Ok(())
    }
}

impl<'d> embedded_hal_1::digital::ErrorType for Flex<'d> {
    type Error = Infallible;
}

impl<'d> embedded_hal_1::digital::InputPin for Flex<'d> {
    #[inline]
    fn is_high(&mut self) -> Result<bool, Self::Error> {
        // Dereference of self is used here and a few other places to
        // access the correct method (since different types/traits
        // share method names)
        Ok((*self).is_high())
    }

    #[inline]
    fn is_low(&mut self) -> Result<bool, Self::Error> {
        Ok((*self).is_low())
    }
}

impl<'d> embedded_hal_1::digital::OutputPin for Flex<'d> {
    #[inline]
    fn set_high(&mut self) -> Result<(), Self::Error> {
        self.set_high();
        Ok(())
    }

    #[inline]
    fn set_low(&mut self) -> Result<(), Self::Error> {
        self.set_low();
        Ok(())
    }
}

impl<'d> embedded_hal_1::digital::StatefulOutputPin for Flex<'d> {
    #[inline]
    fn is_set_high(&mut self) -> Result<bool, Self::Error> {
        Ok((*self).is_high())
    }

    #[inline]
    fn is_set_low(&mut self) -> Result<bool, Self::Error> {
        Ok((*self).is_low())
    }
}

impl<'d> embedded_hal_async::digital::Wait for Flex<'d> {
    #[inline]
    async fn wait_for_high(&mut self) -> Result<(), Self::Error> {
        self.wait_for_high().await;
        Ok(())
    }

    #[inline]
    async fn wait_for_low(&mut self) -> Result<(), Self::Error> {
        self.wait_for_low().await;
        Ok(())
    }

    #[inline]
    async fn wait_for_rising_edge(&mut self) -> Result<(), Self::Error> {
        self.wait_for_rising_edge().await;
        Ok(())
    }

    #[inline]
    async fn wait_for_falling_edge(&mut self) -> Result<(), Self::Error> {
        self.wait_for_falling_edge().await;
        Ok(())
    }

    #[inline]
    async fn wait_for_any_edge(&mut self) -> Result<(), Self::Error> {
        self.wait_for_any_edge().await;
        Ok(())
    }
}

impl<'d> embedded_hal_1::digital::ErrorType for Input<'d> {
    type Error = Infallible;
}

impl<'d> embedded_hal_1::digital::InputPin for Input<'d> {
    #[inline]
    fn is_high(&mut self) -> Result<bool, Self::Error> {
        Ok((*self).is_high())
    }

    #[inline]
    fn is_low(&mut self) -> Result<bool, Self::Error> {
        Ok((*self).is_low())
    }
}

impl<'d> embedded_hal_async::digital::Wait for Input<'d> {
    #[inline]
    async fn wait_for_high(&mut self) -> Result<(), Self::Error> {
        self.wait_for_high().await;
        Ok(())
    }

    #[inline]
    async fn wait_for_low(&mut self) -> Result<(), Self::Error> {
        self.wait_for_low().await;
        Ok(())
    }

    #[inline]
    async fn wait_for_rising_edge(&mut self) -> Result<(), Self::Error> {
        self.wait_for_rising_edge().await;
        Ok(())
    }

    #[inline]
    async fn wait_for_falling_edge(&mut self) -> Result<(), Self::Error> {
        self.wait_for_falling_edge().await;
        Ok(())
    }

    #[inline]
    async fn wait_for_any_edge(&mut self) -> Result<(), Self::Error> {
        self.wait_for_any_edge().await;
        Ok(())
    }
}

impl<'d> embedded_hal_1::digital::ErrorType for Output<'d> {
    type Error = Infallible;
}

impl<'d> embedded_hal_1::digital::OutputPin for Output<'d> {
    #[inline]
    fn set_high(&mut self) -> Result<(), Self::Error> {
        self.set_high();
        Ok(())
    }

    #[inline]
    fn set_low(&mut self) -> Result<(), Self::Error> {
        self.set_low();
        Ok(())
    }
}

impl<'d> embedded_hal_1::digital::StatefulOutputPin for Output<'d> {
    #[inline]
    fn is_set_high(&mut self) -> Result<bool, Self::Error> {
        Ok((*self).is_set_high())
    }

    #[inline]
    fn is_set_low(&mut self) -> Result<bool, Self::Error> {
        Ok((*self).is_set_low())
    }
}
