//! Implements I2C function support over flexcomm + gpios

use core::future::{Future, poll_fn};
use core::marker::PhantomData;
use core::sync::atomic::{AtomicU8, Ordering};
use core::task::Poll;

use embassy_sync::waitqueue::AtomicWaker;
use paste::paste;
use sealed::Sealed;

use crate::iopctl::IopctlPin as Pin;
use crate::{PeripheralType, dma, interrupt};

/// I2C Master Driver
pub mod master;

/// I2C Slave Driver
pub mod slave;

/// shorthand for -> `Result<T>`
pub type Result<T> = core::result::Result<T, Error>;

/// specific information regarding transfer errors
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum TransferError {
    /// Timeout error
    Timeout,
    /// Reading from i2c failed
    ReadFail,
    /// Writing to i2c failed
    WriteFail,
    /// I2C Address not ACK'd
    AddressNack,
    /// Bus level arbitration loss
    ArbitrationLoss,
    /// Address + Start/Stop error
    StartStopError,
    /// state mismatch or other internal register unexpected state
    OtherBusError,
}

/// Error information type
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum Error {
    /// configuration requested is not supported
    UnsupportedConfiguration,

    /// transaction failure types
    Transfer(TransferError),
}

impl From<TransferError> for Error {
    fn from(value: TransferError) -> Self {
        Error::Transfer(value)
    }
}

mod sealed {
    /// simply seal a trait
    pub trait Sealed {}
}

impl<T: Pin> sealed::Sealed for T {}

#[derive(Clone, Copy)]
struct Info {
    regs: &'static crate::pac::i2c0::RegisterBlock,
    waker: &'static AtomicWaker,
    remediation: &'static AtomicU8,
}

// SAFETY: safety for Send here is the same as the other accessors to unsafe blocks: it must be done from a single executor context.
//         This is a temporary workaround -- a better solution might be to refactor Info to no longer maintain a reference to regs,
//         but instead look up the correct register set and then perform operations within an unsafe block as we do for other peripherals
unsafe impl Send for Info {}

trait SealedInstance {
    fn info() -> Info;
    fn waker() -> &'static AtomicWaker;
    fn remediation() -> &'static AtomicU8;
}

/// shared functions between master and slave operation
#[allow(private_bounds)]
pub trait Instance: crate::flexcomm::IntoI2c + SealedInstance + PeripheralType + 'static + Send {
    /// Interrupt for this I2C instance.
    type Interrupt: interrupt::typelevel::Interrupt;
}

macro_rules! impl_instance {
    ($($n:expr),*) => {
        $(
            paste!{
                impl SealedInstance for crate::peripherals::[<FLEXCOMM $n>] {
                    fn info() -> Info {
                        Info {
                            regs: unsafe { &*crate::pac::[<I2c $n>]::ptr() },
                            waker: Self::waker(),
                            remediation: Self::remediation(),
                        }
                    }

                    #[inline]
                    fn waker() -> &'static AtomicWaker {
                        static WAKER: AtomicWaker = AtomicWaker::new();
                        &WAKER
                    }

                    #[inline]
                    fn remediation() -> &'static AtomicU8 {
                        // Used in cases where there was a cancellation that needs to be cleaned up on the next
                        // interrupt
                        static REMEDIATION: AtomicU8 = AtomicU8::new(0);
                        &REMEDIATION
                    }
                }

                impl Instance for crate::peripherals::[<FLEXCOMM $n>] {
                    type Interrupt = crate::interrupt::typelevel::[<FLEXCOMM $n>];
                }
            }
        )*
    };
}

impl_instance!(0, 1, 2, 3, 4, 5, 6, 7, 15);

const REMEDIATON_NONE: u8 = 0b0000_0000;
const REMEDIATON_MASTER_STOP: u8 = 0b0000_0001;
const REMEDIATON_SLAVE_NAK: u8 = 0b0000_0010;

/// Force the remediation state to NONE. To be used when first initializing
/// a peripheral. This is meant to cover the extremely esoteric state where:
///
/// 1. We start an async operation that sends a START
/// 2. We cancel that operation, without sending STOP, so a remediation is requested
/// 3. BEFORE the remediation completes, we create a blocking peripheral
fn force_clear_remediation(info: &Info) {
    info.remediation.store(REMEDIATON_NONE, Ordering::Release);
}

/// Await the remediation step being completed by the interrupt, after
/// a previous cancellation
fn wait_remediation_complete(info: &Info) -> impl Future<Output = ()> {
    poll_fn(move |cx| {
        info.waker.register(cx.waker());
        let rem = info.remediation.load(Ordering::Acquire);
        if rem == REMEDIATON_NONE {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    })
}

/// Ten bit addresses start with first byte 0b11110XXX
pub const TEN_BIT_PREFIX: u8 = 0b11110 << 3;

/// I2C interrupt handler.
pub struct InterruptHandler<T: Instance> {
    _phantom: PhantomData<T>,
}

impl<T: Instance> interrupt::typelevel::Handler<T::Interrupt> for InterruptHandler<T> {
    unsafe fn on_interrupt() {
        let i2c = T::info().regs;

        if i2c.intstat().read().mstpending().bit_is_set() {
            // Retrieve and mask off the remediation flags
            let rem = T::remediation().fetch_and(!REMEDIATON_MASTER_STOP, Ordering::AcqRel);

            if (rem & REMEDIATON_MASTER_STOP) != 0 {
                i2c.mstctl().write(|w| w.mststop().set_bit());
            }

            i2c.intenclr().write(|w| w.mstpendingclr().set_bit());
        }

        if i2c.intstat().read().mstarbloss().bit_is_set() {
            i2c.intenclr().write(|w| w.mstarblossclr().set_bit());
        }

        if i2c.intstat().read().mstststperr().bit_is_set() {
            i2c.intenclr().write(|w| w.mstststperrclr().set_bit());
        }

        if i2c.intstat().read().slvpending().bit_is_set() {
            // Retrieve and mask off the remediation flags
            let rem = T::remediation().fetch_and(!REMEDIATON_SLAVE_NAK, Ordering::AcqRel);

            if (rem & REMEDIATON_SLAVE_NAK) != 0 {
                i2c.slvctl().write(|w| w.slvnack().set_bit());
            }
            i2c.intenclr().write(|w| w.slvpendingclr().set_bit());
        }

        if i2c.intstat().read().slvdesel().bit_is_set() {
            i2c.intenclr().write(|w| w.slvdeselclr().set_bit());
        }

        T::waker().wake();
    }
}

/// io configuration trait for easier configuration
pub trait SclPin<Instance>: Pin + sealed::Sealed + PeripheralType {
    /// convert the pin to appropriate function for SCL usage
    fn as_scl(&self);
}

/// io configuration trait for easier configuration
pub trait SdaPin<Instance>: Pin + sealed::Sealed + PeripheralType {
    /// convert the pin to appropriate function for SDA usage
    fn as_sda(&self);
}

/// Driver mode.
#[allow(private_bounds)]
pub trait Mode: Sealed {}

/// Blocking mode.
pub struct Blocking;
impl Sealed for Blocking {}
impl Mode for Blocking {}

/// Async mode.
pub struct Async;
impl Sealed for Async {}
impl Mode for Async {}

// flexcomm <-> Pin function map
macro_rules! impl_scl {
    ($piom_n:ident, $fn:ident, $fcn:ident) => {
        impl SclPin<crate::peripherals::$fcn> for crate::peripherals::$piom_n {
            fn as_scl(&self) {
                // UM11147 table 556 pg 550
                self.set_function(crate::iopctl::Function::$fn)
                    .set_pull(crate::iopctl::Pull::None)
                    .enable_input_buffer()
                    .set_slew_rate(crate::gpio::SlewRate::Slow)
                    .set_drive_strength(crate::gpio::DriveStrength::Normal)
                    .disable_analog_multiplex()
                    .set_drive_mode(crate::gpio::DriveMode::OpenDrain)
                    .set_input_inverter(crate::gpio::Inverter::Disabled);
            }
        }
    };
}
macro_rules! impl_sda {
    ($piom_n:ident, $fn:ident, $fcn:ident) => {
        impl SdaPin<crate::peripherals::$fcn> for crate::peripherals::$piom_n {
            fn as_sda(&self) {
                // UM11147 table 556 pg 550
                self.set_function(crate::iopctl::Function::$fn)
                    .set_pull(crate::iopctl::Pull::None)
                    .enable_input_buffer()
                    .set_slew_rate(crate::gpio::SlewRate::Slow)
                    .set_drive_strength(crate::gpio::DriveStrength::Normal)
                    .disable_analog_multiplex()
                    .set_drive_mode(crate::gpio::DriveMode::OpenDrain)
                    .set_input_inverter(crate::gpio::Inverter::Disabled);
            }
        }
    };
}

// Flexcomm0 GPIOs -
impl_scl!(PIO0_1, F1, FLEXCOMM0);
impl_sda!(PIO0_2, F1, FLEXCOMM0);

impl_scl!(PIO3_1, F5, FLEXCOMM0);
impl_sda!(PIO3_2, F5, FLEXCOMM0);
impl_sda!(PIO3_3, F5, FLEXCOMM0);
impl_scl!(PIO3_4, F5, FLEXCOMM0);

// Flexcomm1 GPIOs -
impl_scl!(PIO0_8, F1, FLEXCOMM1);
impl_sda!(PIO0_9, F1, FLEXCOMM1);
impl_sda!(PIO0_10, F1, FLEXCOMM1);
impl_scl!(PIO0_11, F1, FLEXCOMM1);

impl_scl!(PIO7_26, F1, FLEXCOMM1);
impl_sda!(PIO7_27, F1, FLEXCOMM1);
impl_sda!(PIO7_28, F1, FLEXCOMM1);
impl_scl!(PIO7_29, F1, FLEXCOMM1);

// Flexcomm2 GPIOs -
impl_scl!(PIO0_15, F1, FLEXCOMM2);
impl_sda!(PIO0_16, F1, FLEXCOMM2);
impl_sda!(PIO0_17, F1, FLEXCOMM2);
impl_scl!(PIO0_18, F1, FLEXCOMM2);

impl_sda!(PIO4_8, F5, FLEXCOMM2);

impl_scl!(PIO7_30, F5, FLEXCOMM2);
impl_sda!(PIO7_31, F5, FLEXCOMM2);

// Flexcomm3 GPIOs -
impl_scl!(PIO0_22, F1, FLEXCOMM3);
impl_sda!(PIO0_23, F1, FLEXCOMM3);
impl_sda!(PIO0_24, F1, FLEXCOMM3);
impl_scl!(PIO0_25, F1, FLEXCOMM3);

// Flexcomm4 GPIOs -
impl_scl!(PIO0_29, F1, FLEXCOMM4);
impl_sda!(PIO0_30, F1, FLEXCOMM4);
impl_sda!(PIO0_31, F1, FLEXCOMM4);
impl_scl!(PIO1_0, F1, FLEXCOMM4);

// Flexcomm5 GPIOs -
impl_scl!(PIO1_4, F1, FLEXCOMM5);
impl_sda!(PIO1_5, F1, FLEXCOMM5);
impl_sda!(PIO1_6, F1, FLEXCOMM5);
impl_scl!(PIO1_7, F1, FLEXCOMM5);

impl_scl!(PIO3_16, F5, FLEXCOMM5);
impl_sda!(PIO3_17, F5, FLEXCOMM5);
impl_sda!(PIO3_18, F5, FLEXCOMM5);
impl_scl!(PIO3_22, F5, FLEXCOMM5);

// Flexcomm6 GPIOs -
impl_scl!(PIO3_26, F1, FLEXCOMM6);
impl_sda!(PIO3_27, F1, FLEXCOMM6);
impl_sda!(PIO3_28, F1, FLEXCOMM6);
impl_scl!(PIO3_29, F1, FLEXCOMM6);

// Flexcomm7 GPIOs -
impl_scl!(PIO4_1, F1, FLEXCOMM7);
impl_sda!(PIO4_2, F1, FLEXCOMM7);
impl_sda!(PIO4_3, F1, FLEXCOMM7);
impl_scl!(PIO4_4, F1, FLEXCOMM7);

// Flexcomm15 GPIOs
// Function configuration is not needed for FC15
// Implementing SCL/SDA traits to use the I2C APIs
impl_scl!(PIOFC15_SCL, F1, FLEXCOMM15);
impl_sda!(PIOFC15_SDA, F1, FLEXCOMM15);

/// I2C Master DMA trait.
#[allow(private_bounds)]
pub trait MasterDma<T: Instance>: dma::Instance {}

/// I2C Slave DMA trait.
#[allow(private_bounds)]
pub trait SlaveDma<T: Instance>: dma::Instance {}

macro_rules! impl_dma {
    ($fcn:ident, $mode:ident, $dma:ident) => {
        paste! {
            impl [<$mode Dma>]<crate::peripherals::$fcn> for crate::peripherals::$dma {}
        }
    };
}

impl_dma!(FLEXCOMM0, Slave, DMA0_CH0);
impl_dma!(FLEXCOMM0, Master, DMA0_CH1);

impl_dma!(FLEXCOMM1, Slave, DMA0_CH2);
impl_dma!(FLEXCOMM1, Master, DMA0_CH3);

impl_dma!(FLEXCOMM2, Slave, DMA0_CH4);
impl_dma!(FLEXCOMM2, Master, DMA0_CH5);

impl_dma!(FLEXCOMM3, Slave, DMA0_CH6);
impl_dma!(FLEXCOMM3, Master, DMA0_CH7);

impl_dma!(FLEXCOMM4, Slave, DMA0_CH8);
impl_dma!(FLEXCOMM4, Master, DMA0_CH9);

impl_dma!(FLEXCOMM5, Slave, DMA0_CH10);
impl_dma!(FLEXCOMM5, Master, DMA0_CH11);

impl_dma!(FLEXCOMM6, Slave, DMA0_CH12);
impl_dma!(FLEXCOMM6, Master, DMA0_CH13);

impl_dma!(FLEXCOMM7, Slave, DMA0_CH14);
impl_dma!(FLEXCOMM7, Master, DMA0_CH15);

macro_rules! impl_nodma {
    ($fcn:ident, $mode:ident) => {
        paste! {
            impl [<$mode Dma>]<crate::peripherals::$fcn> for crate::dma::NoDma {}
        }
    };
}

impl_nodma!(FLEXCOMM0, Master);
impl_nodma!(FLEXCOMM1, Master);
impl_nodma!(FLEXCOMM2, Master);
impl_nodma!(FLEXCOMM3, Master);
impl_nodma!(FLEXCOMM4, Master);
impl_nodma!(FLEXCOMM5, Master);
impl_nodma!(FLEXCOMM6, Master);
impl_nodma!(FLEXCOMM7, Master);
impl_nodma!(FLEXCOMM15, Master);
