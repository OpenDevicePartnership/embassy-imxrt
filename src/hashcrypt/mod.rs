//! Hashcrypt
use core::marker::PhantomData;

use embassy_hal_internal::PeripheralType;
use embassy_sync::waitqueue::AtomicWaker;
use hasher::Hasher;

use crate::clocks::enable_and_reset;
use crate::peripherals::{DMA0_CH30, HASHCRYPT};
use crate::{Peri, dma, interrupt, pac};

/// Hasher module
pub mod hasher;

trait Sealed {}

/// Asynchronous or blocking mode
#[allow(private_bounds)]
pub trait Mode: Sealed {}

/// Blocking mode
pub struct Blocking {}
impl Sealed for Blocking {}
impl Mode for Blocking {}

/// Asynchronous mode
pub struct Async {}
impl Sealed for Async {}
impl Mode for Async {}

/// Trait for compatible DMA channels
#[allow(private_bounds)]
pub trait HashcryptDma: Sealed + dma::Instance {}
impl Sealed for DMA0_CH30 {}
impl HashcryptDma for DMA0_CH30 {}

/// Hashcrypt driver
pub struct Hashcrypt<'d, M: Mode> {
    hashcrypt: pac::Hashcrypt,
    dma_ch: Option<dma::channel::Channel<'d>>,
    _mode: PhantomData<M>,
    _ownership: PhantomData<&'d ()>,
}

static WAKER: AtomicWaker = AtomicWaker::new();

/// Hashcrypt interrupt handler.
pub struct InterruptHandler<T: Instance> {
    _phantom: PhantomData<T>,
}

impl<T: Instance> interrupt::typelevel::Handler<T::Interrupt> for InterruptHandler<T> {
    unsafe fn on_interrupt() {
        let reg = unsafe { crate::pac::Hashcrypt::steal() };

        if reg.status().read().error().is_error() {
            reg.intenclr().write(|w| w.error().clear_bit_by_one());
            WAKER.wake();
        }

        if reg.status().read().digest().is_ready() {
            reg.intenclr().write(|w| w.digest().clear_bit_by_one());
            WAKER.wake();
        }
    }
}

trait SealedInstance {}

/// Hashcrypt instance trait
#[allow(private_bounds)]
pub trait Instance: SealedInstance + PeripheralType {
    /// Interrupt for this Hashcrypt.
    type Interrupt: interrupt::typelevel::Interrupt;
}

impl SealedInstance for crate::peripherals::HASHCRYPT {}

impl Instance for crate::peripherals::HASHCRYPT {
    type Interrupt = crate::interrupt::typelevel::HASHCRYPT;
}

/// Hashcrypt mode
#[derive(Debug, Copy, Clone)]
#[non_exhaustive]
enum Algorithm {
    /// SHA256
    SHA256,
}

impl From<Algorithm> for u8 {
    fn from(value: Algorithm) -> Self {
        match value {
            Algorithm::SHA256 => 0x2,
        }
    }
}

impl<'d, M: Mode> Hashcrypt<'d, M> {
    /// Instantiate new Hashcrypt peripheral
    fn new_inner<T: Instance>(_peripheral: Peri<'d, T>, dma_ch: Option<dma::channel::Channel<'d>>) -> Self {
        enable_and_reset::<HASHCRYPT>();

        Self {
            _ownership: PhantomData,
            _mode: PhantomData,
            dma_ch,
            hashcrypt: unsafe { pac::Hashcrypt::steal() },
        }
    }

    // Safety: unsafe for writing algorithm type to register
    fn start_algorithm(&mut self, algorithm: Algorithm, dma: bool) {
        self.hashcrypt.ctrl().write(|w| w.mode().disabled().new_hash().start());
        self.hashcrypt.ctrl().write(|w| {
            unsafe { w.mode().bits(algorithm.into()) }.new_hash().start();
            if dma {
                w.dma_i().set_bit();
            }
            w
        });
    }
}

impl<'d> Hashcrypt<'d, Blocking> {
    /// Create a new instance
    pub fn new_blocking<T: Instance>(peripheral: Peri<'d, T>) -> Self {
        Self::new_inner(peripheral, None)
    }

    /// Start a new SHA256 hash
    pub fn new_sha256<'a>(&'a mut self) -> Hasher<'d, 'a, Blocking> {
        self.start_algorithm(Algorithm::SHA256, false);
        Hasher::new_blocking(self)
    }
}

impl<'d> Hashcrypt<'d, Async> {
    /// Create a new instance
    pub fn new_async<T: Instance>(
        peripheral: Peri<'d, T>,
        _irq: impl interrupt::typelevel::Binding<T::Interrupt, InterruptHandler<T>> + 'd,
        dma_ch: Peri<'d, impl HashcryptDma>,
    ) -> Self {
        Self::new_inner(peripheral, dma::Dma::reserve_channel(dma_ch))
    }

    /// Start a new SHA256 hash
    pub fn new_sha256<'a>(&'a mut self) -> Hasher<'d, 'a, Async> {
        self.start_algorithm(Algorithm::SHA256, true);
        Hasher::new_async(self)
    }
}
