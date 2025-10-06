//! True Random Number Generator (TRNG)

use core::future::poll_fn;
use core::marker::PhantomData;
use core::task::Poll;

use embassy_futures::block_on;
use embassy_sync::waitqueue::AtomicWaker;
use rand_core::{CryptoRng, RngCore};

use crate::clocks::{SysconPeripheral, enable_and_reset};
use crate::interrupt::typelevel::Interrupt;
use crate::{Peri, PeripheralType, interrupt, peripherals};

static RNG_WAKER: AtomicWaker = AtomicWaker::new();

// The values are based on the NIST SP 800-90B recommendations for entropy source testing
//   with α = 2 ^(-20), H = 0.8 (NXP recommendation, though questionable), W = 512 samples
const REPETITION_THRESHOLD: usize = 26; // 1 + (-log2(α) / H)
const ADAPTIVE_PROPORTION_THRESHOLD: usize = 348; // 1 + CRITBINOM(W, power(2, ( −H)), 1 − α).
const ADAPTIVE_PROPORTION_WINDOW_SIZE: usize = 512;

/// RNG error
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum Error {
    /// Seed error.
    SeedError,

    /// HW Error.
    HwError,

    /// Frequency Count Fail
    FreqCountFail,
}

/// RNG interrupt handler.
pub struct InterruptHandler<T: Instance> {
    _phantom: PhantomData<T>,
}

impl<T: Instance> interrupt::typelevel::Handler<T::Interrupt> for InterruptHandler<T> {
    unsafe fn on_interrupt() {
        let regs = T::info().regs;
        let int_status = regs.int_status().read();

        if int_status.ent_val().bit_is_set()
            || int_status.hw_err().bit_is_set()
            || int_status.frq_ct_fail().bit_is_set()
        {
            regs.int_ctrl().modify(|_, w| {
                w.ent_val()
                    .ent_val_0()
                    .hw_err()
                    .hw_err_0()
                    .frq_ct_fail()
                    .frq_ct_fail_0()
            });
            RNG_WAKER.wake();
        }
    }
}

/// RNG driver.
pub struct Rng<'d> {
    info: Info,
    _lifetime: PhantomData<&'d ()>,
}

fn sw_entropy_test(entropy: &[u32]) -> Result<(), Error> {
    let mut repetition_count = 0;
    let mut adaptive_proportion_count = 0;

    let mut repetition_bit = 0;

    for item in entropy.iter() {
        for i in 0..(size_of_val(item) * 8) {
            let bit = (*item >> i) & 0x1;

            adaptive_proportion_count += bit;

            if bit == repetition_bit {
                repetition_count += 1;

                if repetition_count >= REPETITION_THRESHOLD {
                    error!("Repetition count exceeded threshold: {}", repetition_count);
                    return Err(Error::SeedError);
                }
            } else {
                repetition_count = 1;
                repetition_bit = bit;
            }
        }
    }

    if adaptive_proportion_count as usize >= ADAPTIVE_PROPORTION_THRESHOLD
        || (ADAPTIVE_PROPORTION_WINDOW_SIZE - adaptive_proportion_count as usize) >= ADAPTIVE_PROPORTION_THRESHOLD
    {
        error!(
            "Adaptive proportion count exceeded threshold: {}",
            adaptive_proportion_count
        );
        return Err(Error::SeedError);
    }

    Ok(())
}

impl<'d> Rng<'d> {
    /// Create a new RNG driver.
    pub fn new<T: Instance>(
        _inner: Peri<'d, T>,
        _irq: impl interrupt::typelevel::Binding<T::Interrupt, InterruptHandler<T>> + 'd,
    ) -> Self {
        enable_and_reset::<T>();

        let mut random = Self {
            info: T::info(),
            _lifetime: PhantomData,
        };
        random.init();

        T::Interrupt::unpend();
        unsafe { T::Interrupt::enable() };

        random
    }

    /// Reset the RNG.
    pub fn reset(&mut self) {
        self.info.regs.mctl().write(|w| w.rst_def().set_bit().prgm().set_bit());
    }

    /// Fill the given slice with random values.
    pub async fn async_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        // We have a total of 16 words (512 bits) of entropy at our
        // disposal. The idea here is to read all bits and copy the
        // necessary bytes to the slice.
        for chunk in dest.chunks_mut(64) {
            self.async_fill_chunk(chunk).await?;
        }

        Ok(())
    }

    async fn async_fill_chunk(&mut self, chunk: &mut [u8]) -> Result<(), Error> {
        // wait for interrupt
        let res = poll_fn(|cx| {
            // Check if already ready.
            // TODO: Is this necessary? Could we just check once after
            // the waker has been registered?
            if self.info.regs.int_status().read().ent_val().bit_is_set() {
                return Poll::Ready(Ok(()));
            }

            RNG_WAKER.register(cx.waker());

            self.unmask_interrupts();

            let mctl = self.info.regs.mctl().read();

            // Check again if interrupt fired
            if mctl.ent_val().bit_is_set() {
                Poll::Ready(Ok(()))
            } else if mctl.err().bit_is_set() {
                Poll::Ready(Err(Error::HwError))
            } else if mctl.fct_fail().bit_is_set() {
                Poll::Ready(Err(Error::FreqCountFail))
            } else {
                Poll::Pending
            }
        })
        .await;

        // Exit early if we got an error
        if res.is_err() {
            // Clear HW error
            self.info.regs.mctl().modify(|_, w| w.err().clear_bit_by_one());

            // Reading the last element restarts the generation
            if let Some(ent) = self.info.regs.ent_iter().last() {
                ent.read().bits();
            }
            return res;
        }

        let bits = self.info.regs.mctl().read();

        if bits.ent_val().bit_is_set() {
            let mut entropy = [0; 16];

            for (i, item) in entropy.iter_mut().enumerate() {
                *item = self.info.regs.ent(i).read().bits();
            }

            if entropy.contains(&0) {
                return Err(Error::SeedError);
            }

            sw_entropy_test(&entropy)?;

            // SAFETY: entropy is the same for input and output types in
            // native endianness.
            let entropy: [u8; 64] = unsafe { core::mem::transmute(entropy) };

            // write bytes to chunk
            chunk.copy_from_slice(&entropy[..chunk.len()]);
        }

        res
    }

    fn mask_interrupts(&mut self) {
        self.info.regs.int_mask().write(|w| {
            w.ent_val()
                .ent_val_0()
                .hw_err()
                .hw_err_0()
                .frq_ct_fail()
                .frq_ct_fail_0()
        });
    }

    fn unmask_interrupts(&mut self) {
        self.info.regs.int_mask().modify(|_, w| {
            w.ent_val()
                .ent_val_1()
                .hw_err()
                .hw_err_1()
                .frq_ct_fail()
                .frq_ct_fail_1()
        });
    }

    fn enable_interrupts(&mut self) {
        self.info.regs.int_ctrl().write(|w| {
            w.ent_val()
                .ent_val_1()
                .hw_err()
                .hw_err_1()
                .frq_ct_fail()
                .frq_ct_fail_1()
        });
    }

    fn init(&mut self) {
        self.mask_interrupts();

        // Switch TRNG to programming mode
        self.info.regs.mctl().write(|w| w.prgm().set_bit().trng_acc().set_bit());

        // Disable HW entropy check due to HW issue when main clock is running at a high rate
        self.info.regs.frqmin().write(|w| unsafe { w.frq_min().bits(0x0) });
        self.info
            .regs
            .frqmax()
            .write(|w| unsafe { w.frq_max().bits(0x3F_FFFF) });
        self.info
            .regs
            .pkrmax()
            .write(|w| unsafe { w.pkr_max().bits(0x0000_FFFE) });
        self.info
            .regs
            .pkrrng()
            .write(|w| unsafe { w.pkr_rng().bits(0x0000_FFFF) });
        self.info
            .regs
            .scml()
            .write(|w| unsafe { w.mono_max().bits(0xFFFE).mono_rng().bits(0xFFFF) });
        self.info
            .regs
            .scr1l()
            .write(|w| unsafe { w.run1_max().bits(0x7FFE).run1_rng().bits(0x7FFF) });
        self.info
            .regs
            .scr2l()
            .write(|w| unsafe { w.run2_max().bits(0x3FFE).run2_rng().bits(0x3FFF) });
        self.info
            .regs
            .scr3l()
            .write(|w| unsafe { w.run3_max().bits(0x1FFE).run3_rng().bits(0x1FFF) });
        self.info
            .regs
            .scr4l()
            .write(|w| unsafe { w.run4_max().bits(0x0FFE).run4_rng().bits(0x0FFF) });
        self.info
            .regs
            .scr5l()
            .write(|w| unsafe { w.run5_max().bits(0x07FE).run5_rng().bits(0x07FF) });
        self.info
            .regs
            .scr6pl()
            .write(|w| unsafe { w.run6p_max().bits(0x07FE).run6p_rng().bits(0x07FF) });
        self.info.regs.scmisc().write(|w| unsafe { w.lrun_max().bits(0xFF) });

        // This register does not reset to power-on reset value documented in the manual
        // so we always set it to the recommended value from NXP SDK
        self.info
            .regs
            .sdctl()
            .write(|w| unsafe { w.ent_dly().bits(0xc80).samp_size().bits(0x200) });

        self.enable_interrupts();

        // Switch TRNG to Run Mode
        self.info
            .regs
            .mctl()
            .modify(|_, w| w.trng_acc().set_bit().prgm().clear_bit());
    }
}

impl RngCore for Rng<'_> {
    fn next_u32(&mut self) -> u32 {
        let mut bytes = [0u8; 4];
        block_on(self.async_fill_bytes(&mut bytes)).unwrap();
        u32::from_ne_bytes(bytes)
    }

    fn next_u64(&mut self) -> u64 {
        let mut bytes = [0u8; 8];
        block_on(self.async_fill_bytes(&mut bytes)).unwrap();
        u64::from_ne_bytes(bytes)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        block_on(self.async_fill_bytes(dest)).unwrap();
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl CryptoRng for Rng<'_> {}

struct Info {
    regs: crate::pac::Trng,
}

trait SealedInstance {
    fn info() -> Info;
}

/// RNG instance trait.
#[allow(private_bounds)]
pub trait Instance: SealedInstance + PeripheralType + SysconPeripheral + 'static + Send {
    /// Interrupt for this RNG instance.
    type Interrupt: interrupt::typelevel::Interrupt;
}

impl Instance for peripherals::RNG {
    type Interrupt = crate::interrupt::typelevel::RNG;
}

impl SealedInstance for peripherals::RNG {
    fn info() -> Info {
        // SAFETY: safe from single executor
        Info {
            regs: unsafe { crate::pac::Trng::steal() },
        }
    }
}
