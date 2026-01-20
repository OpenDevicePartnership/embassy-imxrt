//! Universal Asynchronous Receiver Transmitter (UART) driver.

use core::future::{Future, poll_fn};
use core::marker::PhantomData;
use core::task::Poll;

use embassy_futures::select::{Either, select};
use embassy_hal_internal::drop::OnDrop;
use embassy_hal_internal::{Peri, PeripheralType};
use embassy_sync::waitqueue::AtomicWaker;
use paste::paste;

use crate::dma::channel::Channel;
use crate::dma::transfer::Transfer;
use crate::flexcomm::{Clock, FlexcommRef};
use crate::gpio::{AnyPin, GpioPin as Pin};
use crate::interrupt::typelevel::Interrupt;
use crate::iopctl::{DriveMode, DriveStrength, Inverter, IopctlPin, Pull, SlewRate};
use crate::pac::usart0::cfg::{Clkpol, Datalen, Loop, Paritysel as Parity, Stoplen, Syncen, Syncmst};
use crate::pac::usart0::ctl::Cc;
use crate::{dma, interrupt};

/// Driver move trait.
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

/// Uart driver.
pub struct Uart<'a, M: Mode> {
    info: Info,
    tx: UartTx<'a, M>,
    rx: UartRx<'a, M>,
}

/// Uart TX driver.
pub struct UartTx<'a, M: Mode> {
    info: Info,
    _flexcomm: FlexcommRef,
    _tx_dma: Option<Channel<'a>>,
    _phantom: PhantomData<(&'a (), M)>,
}

/// Uart RX driver.
pub struct UartRx<'a, M: Mode> {
    info: Info,
    _flexcomm: FlexcommRef,
    _buffer_config: Option<BufferConfig>,
    _rx_dma: Option<Channel<'a>>,
    _phantom: PhantomData<(&'a (), M)>,
}

/// UART config
#[derive(Clone, Copy)]
pub struct Config {
    /// Baudrate of the Uart
    pub baudrate: u32,
    /// data length
    pub data_bits: Datalen,
    /// Parity
    pub parity: Parity,
    /// Stop bits
    pub stop_bits: Stoplen,
    /// Polarity of the clock
    pub clock_polarity: Clkpol,
    /// Sync/ Async operation selection
    pub operation: Syncen,
    /// Sync master/slave mode selection (only applicable in sync mode)
    pub sync_mode_master_select: Syncmst,
    /// USART continuous Clock generation enable in synchronous master mode.
    pub continuous_clock: Cc,
    /// Normal/ loopback mode
    pub loopback_mode: Loop,
    /// Clock type
    pub clock: Clock,
}

impl Default for Config {
    /// Default configuration for single channel sampling.
    fn default() -> Self {
        Self {
            baudrate: 115_200,
            data_bits: Datalen::Bit8,
            parity: Parity::NoParity,
            stop_bits: Stoplen::Bit1,
            clock_polarity: Clkpol::FallingEdge,
            operation: Syncen::AsynchronousMode,
            sync_mode_master_select: Syncmst::Slave,
            continuous_clock: Cc::ClockOnCharacter,
            loopback_mode: Loop::Normal,
            clock: crate::flexcomm::Clock::Sfro,
        }
    }
}

/// Uart Errors
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum Error {
    /// Read error
    Read,

    /// Buffer overflow
    Overrun,

    /// Noise error
    Noise,

    /// Framing error
    Framing,

    /// Parity error
    Parity,

    /// Failure
    Fail,

    /// Invalid argument
    InvalidArgument,

    /// Uart baud rate cannot be supported with the given clock
    UnsupportedBaudrate,

    /// RX FIFO Empty
    RxFifoEmpty,

    /// TX FIFO Full
    TxFifoFull,

    /// TX Busy
    TxBusy,
}
/// shorthand for -> `Result<T>`
pub type Result<T> = core::result::Result<T, Error>;

impl<'a, M: Mode> UartTx<'a, M> {
    fn new_inner<T: Instance>(_flexcomm: FlexcommRef, _tx_dma: Option<Channel<'a>>) -> Self {
        Self {
            info: T::info(),
            _flexcomm,
            _tx_dma,
            _phantom: PhantomData,
        }
    }
}

impl<'a> UartTx<'a, Blocking> {
    /// Create a new UART which can only send data
    /// Unidirectional Uart - Tx only
    pub fn new_blocking<T: Instance>(_inner: Peri<'a, T>, tx: Peri<'a, impl TxPin<T>>, config: Config) -> Result<Self> {
        tx.as_tx();

        let flexcomm = Uart::<Blocking>::init::<T>(Some(tx.into().reborrow()), None, None, None, config)?;

        Ok(Self::new_inner::<T>(flexcomm, None))
    }

    fn write_byte_internal(&mut self, byte: u8) -> Result<()> {
        // SAFETY: unsafe only used for .bits()
        self.info
            .regs
            .fifowr()
            .write(|w| unsafe { w.txdata().bits(u16::from(byte)) });

        Ok(())
    }

    fn blocking_write_byte(&mut self, byte: u8) -> Result<()> {
        while self.info.regs.fifostat().read().txnotfull().bit_is_clear() {}
        self.write_byte_internal(byte)
    }

    fn write_byte(&mut self, byte: u8) -> Result<()> {
        if self.info.regs.fifostat().read().txnotfull().bit_is_clear() {
            Err(Error::TxFifoFull)
        } else {
            self.write_byte_internal(byte)
        }
    }

    /// Transmit the provided buffer blocking execution until done.
    pub fn blocking_write(&mut self, buf: &[u8]) -> Result<()> {
        for x in buf {
            self.blocking_write_byte(*x)?;
        }

        Ok(())
    }

    /// Transmit the provided buffer.
    pub fn write(&mut self, buf: &[u8]) -> Result<()> {
        for x in buf {
            self.write_byte(*x)?;
        }

        Ok(())
    }

    /// Flush UART TX blocking execution until done.
    pub fn blocking_flush(&mut self) -> Result<()> {
        while self.info.regs.stat().read().txidle().bit_is_clear() {}
        Ok(())
    }

    /// Flush UART TX.
    pub fn flush(&mut self) -> Result<()> {
        if self.info.regs.stat().read().txidle().bit_is_clear() {
            Err(Error::TxBusy)
        } else {
            Ok(())
        }
    }
}

struct BufferConfig {
    #[cfg(feature = "time")]
    buffer_a: &'static mut [u8],
    #[cfg(feature = "time")]
    buffer_b: &'static mut [u8],
    #[cfg(feature = "time")]
    read_off: usize,
    #[cfg(feature = "time")]
    polling_rate: u64,
    #[cfg(feature = "time")]
    consumer_buf: dma::PingPongSelector,
}

impl<'a, M: Mode> UartRx<'a, M> {
    fn new_inner<T: Instance>(
        _flexcomm: FlexcommRef,
        _rx_dma: Option<Channel<'a>>,
        _buffer_config: Option<BufferConfig>,
    ) -> Self {
        Self {
            info: T::info(),
            _flexcomm,
            _buffer_config,
            _rx_dma,
            _phantom: PhantomData,
        }
    }
}

impl<'a> UartRx<'a, Blocking> {
    /// Create a new blocking UART which can only receive data
    pub fn new_blocking<T: Instance>(_inner: Peri<'a, T>, rx: Peri<'a, impl RxPin<T>>, config: Config) -> Result<Self> {
        rx.as_rx();

        let flexcomm = Uart::<Blocking>::init::<T>(None, Some(rx.into().reborrow()), None, None, config)?;

        Ok(Self::new_inner::<T>(flexcomm, None, None))
    }
}

impl UartRx<'_, Blocking> {
    fn read_byte_internal(&mut self) -> Result<u8> {
        if self.info.regs.fifostat().read().rxerr().bit_is_set() {
            self.info.regs.fifocfg().modify(|_, w| w.emptyrx().set_bit());
            self.info.regs.fifostat().modify(|_, w| w.rxerr().set_bit());
            Err(Error::Read)
        } else if self.info.regs.stat().read().parityerrint().bit_is_set() {
            self.info.regs.stat().modify(|_, w| w.parityerrint().clear_bit_by_one());
            Err(Error::Parity)
        } else if self.info.regs.stat().read().framerrint().bit_is_set() {
            self.info.regs.stat().modify(|_, w| w.framerrint().clear_bit_by_one());
            Err(Error::Framing)
        } else if self.info.regs.stat().read().rxnoiseint().bit_is_set() {
            self.info.regs.stat().modify(|_, w| w.rxnoiseint().clear_bit_by_one());
            Err(Error::Noise)
        } else {
            let byte = self.info.regs.fiford().read().rxdata().bits() as u8;
            Ok(byte)
        }
    }

    fn read_byte(&mut self) -> Result<u8> {
        if self.info.regs.fifostat().read().rxnotempty().bit_is_clear() {
            Err(Error::RxFifoEmpty)
        } else {
            self.read_byte_internal()
        }
    }

    fn blocking_read_byte(&mut self) -> Result<u8> {
        while self.info.regs.fifostat().read().rxnotempty().bit_is_clear() {}
        self.read_byte_internal()
    }

    /// Read from UART RX.
    pub fn read(&mut self, buf: &mut [u8]) -> Result<()> {
        for b in buf.iter_mut() {
            *b = self.read_byte()?;
        }

        Ok(())
    }

    /// Read from UART RX blocking execution until done.
    pub fn blocking_read(&mut self, buf: &mut [u8]) -> Result<()> {
        for b in buf.iter_mut() {
            *b = self.blocking_read_byte()?;
        }

        Ok(())
    }
}

impl<'a, M: Mode> Uart<'a, M> {
    fn init<T: Instance>(
        tx: Option<Peri<'a, AnyPin>>,
        rx: Option<Peri<'a, AnyPin>>,
        rts: Option<Peri<'a, AnyPin>>,
        cts: Option<Peri<'a, AnyPin>>,
        config: Config,
    ) -> Result<FlexcommRef> {
        let flexcomm = T::enable(config.clock);
        T::into_usart();

        let regs = T::info().regs;

        if tx.is_some() {
            regs.fifocfg().modify(|_, w| w.emptytx().set_bit().enabletx().enabled());

            // clear FIFO error
            regs.fifostat().write(|w| w.txerr().set_bit());
        }

        if rx.is_some() {
            regs.fifocfg()
                .modify(|_, w| w.emptyrx().set_bit().enablerx().enabled().wakerx().enabled());

            regs.fifotrig()
                .modify(|_, w| unsafe { w.rxlvl().bits(0) }.rxlvlena().set_bit());

            // clear FIFO error
            regs.fifostat().write(|w| w.rxerr().set_bit());
        }

        if rts.is_some() && cts.is_some() {
            regs.cfg().modify(|_, w| w.ctsen().enabled());
        }

        Self::set_baudrate_inner::<T>(config.baudrate, config.clock)?;
        Self::set_uart_config::<T>(config);

        Ok(flexcomm)
    }

    fn get_fc_freq(clock: Clock) -> Result<u32> {
        match clock {
            Clock::Sfro => Ok(16_000_000),
            Clock::Ffro => Ok(48_000_000),
            // We only support Sfro and Ffro now.
            _ => Err(Error::InvalidArgument),
        }
    }

    fn set_baudrate_inner<T: Instance>(baudrate: u32, clock: Clock) -> Result<()> {
        // Get source clock frequency according to clock type.
        let source_clock_hz = Self::get_fc_freq(clock)?;

        if baudrate == 0 {
            return Err(Error::InvalidArgument);
        }

        let regs = T::info().regs;

        // If synchronous master mode is enabled, only configure the BRG value.
        if regs.cfg().read().syncen().is_synchronous_mode() {
            // Master
            if regs.cfg().read().syncmst().is_master() {
                // Calculate the BRG value
                let brgval = (source_clock_hz / baudrate) - 1;

                // SAFETY: unsafe only used for .bits()
                regs.brg().write(|w| unsafe { w.brgval().bits(brgval as u16) });
            }
        } else {
            // Smaller values of OSR can make the sampling position within a
            // data bit less accurate and may potentially cause more noise
            // errors or incorrect data.
            let (_, osr, brg) = (8..16).rev().fold(
                (u32::MAX, u32::MAX, u32::MAX),
                |(best_diff, best_osr, best_brg), osrval| {
                    // Compare source_clock_hz agaist with ((osrval + 1) * baudrate) to make sure
                    // (source_clock_hz / ((osrval + 1) * baudrate)) is not less than 0.
                    if source_clock_hz < ((osrval + 1) * baudrate) {
                        (best_diff, best_osr, best_brg)
                    } else {
                        let brgval = (source_clock_hz / ((osrval + 1) * baudrate)) - 1;
                        // We know brgval will not be less than 0 now, it should have already been a valid u32 value,
                        // then compare it agaist with 65535.
                        if brgval > 65535 {
                            (best_diff, best_osr, best_brg)
                        } else {
                            // Calculate the baud rate based on the BRG value
                            let candidate = source_clock_hz / ((osrval + 1) * (brgval + 1));

                            // Calculate the difference between the
                            // current baud rate and the desired baud rate
                            let diff = (candidate as i32 - baudrate as i32).unsigned_abs();

                            // Check if the current calculated difference is the best so far
                            if diff < best_diff {
                                (diff, osrval, brgval)
                            } else {
                                (best_diff, best_osr, best_brg)
                            }
                        }
                    }
                },
            );

            // Value over range
            if brg > 65535 {
                return Err(Error::UnsupportedBaudrate);
            }

            // SAFETY: unsafe only used for .bits()
            regs.osr().write(|w| unsafe { w.osrval().bits(osr as u8) });

            // SAFETY: unsafe only used for .bits()
            regs.brg().write(|w| unsafe { w.brgval().bits(brg as u16) });
        }

        Ok(())
    }

    fn set_uart_config<T: Instance>(config: Config) {
        let regs = T::info().regs;

        regs.cfg().modify(|_, w| w.enable().disabled());

        regs.cfg().modify(|_, w| {
            w.datalen()
                .variant(config.data_bits)
                .stoplen()
                .variant(config.stop_bits)
                .paritysel()
                .variant(config.parity)
                .loop_()
                .variant(config.loopback_mode)
                .syncen()
                .variant(config.operation)
                .clkpol()
                .variant(config.clock_polarity)
        });

        regs.cfg().modify(|_, w| w.enable().enabled());
    }

    /// Deinitializes a USART instance.
    pub fn deinit(&self) -> Result<()> {
        // This function waits for TX complete, disables TX and RX, and disables the USART clock
        while self.info.regs.stat().read().txidle().bit_is_clear() {
            // When 0, indicates that the transmitter is currently in the process of sending data.
        }

        // Disable interrupts
        self.info.regs.fifointenclr().modify(|_, w| {
            w.txerr()
                .set_bit()
                .rxerr()
                .set_bit()
                .txlvl()
                .set_bit()
                .rxlvl()
                .set_bit()
        });

        // Disable dma requests
        self.info
            .regs
            .fifocfg()
            .modify(|_, w| w.dmatx().clear_bit().dmarx().clear_bit());

        // Disable peripheral
        self.info.regs.cfg().modify(|_, w| w.enable().disabled());

        Ok(())
    }

    /// Split the Uart into a transmitter and receiver, which is particularly
    /// useful when having two tasks correlating to transmitting and receiving.
    pub fn split(self) -> (UartTx<'a, M>, UartRx<'a, M>) {
        (self.tx, self.rx)
    }

    /// Split the Uart into a transmitter and receiver by mutable reference,
    /// which is particularly useful when having two tasks correlating to
    /// transmitting and receiving.
    pub fn split_ref(&mut self) -> (&mut UartTx<'a, M>, &mut UartRx<'a, M>) {
        (&mut self.tx, &mut self.rx)
    }
}

impl<'a> Uart<'a, Blocking> {
    /// Create a new blocking UART
    pub fn new_blocking<T: Instance>(
        _inner: Peri<'a, T>,
        tx: Peri<'a, impl TxPin<T>>,
        rx: Peri<'a, impl RxPin<T>>,
        config: Config,
    ) -> Result<Self> {
        tx.as_tx();
        rx.as_rx();

        let flexcomm = Self::init::<T>(Some(tx.into()), Some(rx.into()), None, None, config)?;

        Ok(Self {
            info: T::info(),
            tx: UartTx::new_inner::<T>(flexcomm.clone(), None),
            rx: UartRx::new_inner::<T>(flexcomm, None, None),
        })
    }

    /// Read from UART RX blocking execution until done.
    pub fn blocking_read(&mut self, buf: &mut [u8]) -> Result<()> {
        self.rx.blocking_read(buf)
    }

    /// Read from UART Rx.
    pub fn read(&mut self, buf: &mut [u8]) -> Result<()> {
        self.rx.read(buf)
    }

    /// Transmit the provided buffer blocking execution until done.
    pub fn blocking_write(&mut self, buf: &[u8]) -> Result<()> {
        self.tx.blocking_write(buf)
    }

    /// Transmit the provided buffer.
    pub fn write(&mut self, buf: &[u8]) -> Result<()> {
        self.tx.write(buf)
    }

    /// Flush UART TX blocking execution until done.
    pub fn blocking_flush(&mut self) -> Result<()> {
        self.tx.blocking_flush()
    }

    /// Flush UART TX.
    pub fn flush(&mut self) -> Result<()> {
        self.tx.flush()
    }
}

impl<'a> UartTx<'a, Async> {
    /// Create a new DMA enabled UART which can only send data
    pub fn new_async<T: Instance>(
        _inner: Peri<'a, T>,
        tx: Peri<'a, impl TxPin<T>>,
        _irq: impl interrupt::typelevel::Binding<T::Interrupt, InterruptHandler<T>> + 'a,
        tx_dma: Peri<'a, impl TxDma<T>>,
        config: Config,
    ) -> Result<Self> {
        tx.as_tx();

        let flexcomm = Uart::<Async>::init::<T>(Some(tx.into()), None, None, None, config)?;

        T::Interrupt::unpend();
        unsafe { T::Interrupt::enable() };

        let tx_dma = dma::Dma::reserve_channel(tx_dma);

        Ok(Self::new_inner::<T>(flexcomm, tx_dma))
    }

    /// Transmit the provided buffer asynchronously.
    pub async fn write(&mut self, buf: &[u8]) -> Result<()> {
        let regs = self.info.regs;

        // Disable DMA on completion/cancellation
        let _dma_guard = OnDrop::new(|| {
            regs.fifocfg().modify(|_, w| w.dmatx().disabled());
        });

        for chunk in buf.chunks(1024) {
            regs.fifocfg().modify(|_, w| w.dmatx().enabled());

            let transfer = Transfer::new_write(
                // an async UART instance cannot be created without a dma channel
                self._tx_dma.as_ref().ok_or(Error::Fail)?,
                chunk,
                regs.fifowr().as_ptr() as *mut u8,
                Default::default(),
            );

            let res = select(
                transfer,
                poll_fn(|cx| {
                    self.info.tx_waker.register(cx.waker());

                    self.info.regs.fifointenset().write(|w| w.txerr().set_bit());

                    let fifointstat = self.info.regs.fifointstat().read();

                    self.info.regs.fifostat().write(|w| w.txerr().set_bit());

                    if fifointstat.txerr().bit_is_set() {
                        Poll::Ready(Err(Error::Overrun))
                    } else {
                        Poll::Pending
                    }
                }),
            )
            .await;

            match res {
                Either::First(()) | Either::Second(Ok(())) => (),
                Either::Second(e) => return e,
            }
        }

        Ok(())
    }

    /// Flush UART TX asynchronously.
    pub fn flush(&mut self) -> impl Future<Output = Result<()>> + use<'_, 'a> {
        poll_fn(|cx| {
            self.info.tx_waker.register(cx.waker());

            self.info.regs.intenset().write(|w| w.txidleen().set_bit());
            self.info.regs.fifointenset().write(|w| w.txerr().set_bit());

            let fifointstat = self.info.regs.fifointstat().read();

            self.info.regs.fifostat().write(|w| w.txerr().set_bit());

            if self.info.regs.stat().read().txidle().bit_is_set() {
                Poll::Ready(Ok(()))
            } else if fifointstat.txerr().bit_is_set() {
                Poll::Ready(Err(Error::Overrun))
            } else {
                Poll::Pending
            }
        })
    }
}

impl<'a> UartRx<'a, Async> {
    /// Create a new DMA enabled UART which can only receive data
    pub fn new_async<T: Instance>(
        _inner: Peri<'a, T>,
        rx: Peri<'a, impl RxPin<T>>,
        _irq: impl interrupt::typelevel::Binding<T::Interrupt, InterruptHandler<T>> + 'a,
        rx_dma: Peri<'a, impl RxDma<T>>,
        config: Config,
    ) -> Result<Self> {
        rx.as_rx();

        let flexcomm = Uart::<Async>::init::<T>(None, Some(rx.into()), None, None, config)?;

        T::Interrupt::unpend();
        unsafe { T::Interrupt::enable() };

        let rx_dma = dma::Dma::reserve_channel(rx_dma);

        Ok(Self::new_inner::<T>(flexcomm, rx_dma, None))
    }

    /// Create a new DMA enabled UART which can only receive data, using a ping-pong buffer to enable continuous DMA reception.
    /// This uses dual buffers (buffer A and buffer B) that alternate, preventing data loss that would otherwise occur
    /// Note: requires time-driver due to hardware constraint requiring a polled interface (no UART Idle bus indicator).
    ///       Alternative approaches are possible; this was done to maintain similarity between buffered and unbuffered read interfaces.
    #[cfg(feature = "time")]
    pub fn new_async_with_buffer<T: Instance>(
        _inner: Peri<'a, T>,
        rx: Peri<'a, impl RxPin<T>>,
        _irq: impl interrupt::typelevel::Binding<T::Interrupt, InterruptHandler<T>> + 'a,
        rx_dma: Peri<'a, impl RxDma<T>>,
        config: Config,
        buffer: &'static mut [u8],
        polling_rate_us: u64,
    ) -> Result<Self> {
        rx.as_rx();

        let mut rx = rx.into();
        let flexcomm = Uart::<Async>::init::<T>(None, Some(rx.reborrow()), None, None, config)?;

        T::Interrupt::unpend();
        unsafe { T::Interrupt::enable() };

        let rx_dma = dma::Dma::reserve_channel(rx_dma).ok_or(Error::Fail)?;

        if !buffer.len().is_multiple_of(2) {
            return Err(Error::InvalidArgument);
        }

        let (buffer_a, buffer_b) = buffer.split_at_mut(buffer.len() / 2);
        T::info().regs.fifocfg().modify(|_, w| w.dmarx().enabled());
        // immediately configure and enable channel for ping-pong (double-buffered) reception
        rx_dma.configure_channel_ping_pong(
            dma::transfer::Direction::PeripheralToMemory,
            T::info().regs.fiford().as_ptr() as *const u8 as *const u32,
            buffer_a.as_mut_ptr() as *mut u32,
            buffer_b.as_mut_ptr() as *mut u32,
            buffer_a.len(),
            dma::transfer::TransferOptions {
                width: dma::transfer::Width::Bit8,
                priority: dma::transfer::Priority::Priority0,
            },
        );
        rx_dma.enable_channel();
        rx_dma.trigger_channel();

        Ok(Self::new_inner::<T>(
            flexcomm,
            Some(rx_dma),
            Some(BufferConfig {
                buffer_a,
                buffer_b,
                read_off: 0,
                polling_rate: polling_rate_us,
                consumer_buf: dma::PingPongSelector::BufferA,
            }),
        ))
    }

    /// Read from UART RX asynchronously.
    pub async fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        #[cfg(feature = "time")]
        {
            if self._buffer_config.is_some() {
                self.read_buffered(buf).await
            } else {
                self.read_unbuffered(buf).await
            }
        }

        #[cfg(not(feature = "time"))]
        {
            self.read_unbuffered(buf).await
        }
    }

    async fn read_unbuffered(&mut self, buf: &mut [u8]) -> Result<usize> {
        let regs = self.info.regs;

        for chunk in buf.chunks_mut(1024) {
            regs.fifocfg().modify(|_, w| w.dmarx().enabled());

            let transfer = Transfer::new_read(
                self._rx_dma.as_ref().ok_or(Error::Fail)?,
                regs.fiford().as_ptr() as *mut u8,
                chunk,
                Default::default(),
            );

            // Disable DMA on completion/cancellation
            let _dma_guard = OnDrop::new(|| {
                regs.fifocfg().modify(|_, w| w.dmarx().disabled());
            });

            let res = select(
                transfer,
                poll_fn(|cx| {
                    self.info.rx_waker.register(cx.waker());

                    self.info
                        .regs
                        .intenset()
                        .write(|w| w.framerren().set_bit().parityerren().set_bit().rxnoiseen().set_bit());

                    self.info.regs.fifointenset().write(|w| w.rxerr().set_bit());

                    let stat = self.info.regs.stat().read();
                    let fifointstat = self.info.regs.fifointstat().read();

                    self.info.regs.stat().write(|w| {
                        w.framerrint()
                            .clear_bit_by_one()
                            .parityerrint()
                            .clear_bit_by_one()
                            .rxnoiseint()
                            .clear_bit_by_one()
                    });

                    self.info.regs.fifostat().write(|w| w.rxerr().set_bit());

                    if stat.framerrint().bit_is_set() {
                        Poll::Ready(Err(Error::Framing))
                    } else if stat.parityerrint().bit_is_set() {
                        Poll::Ready(Err(Error::Parity))
                    } else if stat.rxnoiseint().bit_is_set() {
                        Poll::Ready(Err(Error::Noise))
                    } else if fifointstat.rxerr().bit_is_set() {
                        Poll::Ready(Err(Error::Overrun))
                    } else {
                        Poll::Pending
                    }
                }),
            )
            .await;

            match res {
                Either::First(()) | Either::Second(Ok(())) => (),
                Either::Second(Err(e)) => return Err(e),
            }
        }

        Ok(buf.len())
    }

    #[cfg(feature = "time")]
    async fn read_buffered(&mut self, buf: &mut [u8]) -> Result<usize> {
        let rx_dma = self._rx_dma.as_ref().ok_or(Error::Fail)?;
        let buffer_config = self._buffer_config.as_mut().ok_or(Error::Fail)?;
        // Check for ping-pong buffer overrun error from DMA
        if rx_dma.check_and_clear_overrun_error() {
            return Err(Error::Overrun);
        }

        let half_size = buffer_config.buffer_a.len();

        // Total bytes read into user buffer
        let mut bytes_read = 0;

        // As the Rx Idle interrupt is not present for this processor, we must poll to see if new data is available
        while bytes_read < buf.len() {
            // Check for ping-pong buffer overrun error from DMA
            if rx_dma.check_and_clear_overrun_error() {
                return Err(Error::Overrun);
            }

            // Check for UART RX FIFO overrun error
            if self.info.regs.fifostat().read().rxerr().bit_is_set() {
                self.info.regs.fifostat().modify(|_, w| w.rxerr().set_bit());
                return Err(Error::Overrun);
            }

            // Check if current buffer has been granted (filled by DMA)
            let cur_buf = buffer_config.consumer_buf;
            // Current DMA buffer status
            let buffer_status = rx_dma.buffer_status(cur_buf);

            let mut available = 0usize;

            if buffer_status == dma::BufferStatus::Granted {
                // Current buffer is equal to the granted buffer
                // The entire buffer is available to read
                available = half_size - buffer_config.read_off;
            } else {
                // Buffer not yet granted - check if DMA is writing to it
                // We can try to read partial data using xfercount
                let dma_current_buffer = rx_dma.current_buffer();
                if dma_current_buffer == cur_buf {
                    // DMA is writing to the current buffer, allow to use xfer count to determine available data
                    let xfercount = rx_dma.get_xfer_count();

                    // xfercount counts down to 0x3FF at the end of transfer
                    // But if it is 0x3FF and buffer is not granted, this can mean we just finished transfer after
                    //   our grant check - so we skip this case to avoid overflowing written calculation below
                    if xfercount == 0x3FF {
                        available = 0;
                    } else {
                        let remaining = xfercount as usize + 1;

                        let written = half_size - remaining;
                        if written > buffer_config.read_off {
                            available = written - buffer_config.read_off;
                        }
                    }
                }
                // If DMA is writing to the other buffer, no new data is available
            }

            if available > 0 {
                let want_to_read = buf.len() - bytes_read;
                let to_read = want_to_read.min(available);

                // Read data from the appropriate buffer
                match cur_buf {
                    dma::PingPongSelector::BufferA => {
                        let src_slice_opt = buffer_config
                            .buffer_a
                            .get(buffer_config.read_off..buffer_config.read_off + to_read)
                            .ok_or(Error::Read)?;
                        let dst_slice_opt = buf.get_mut(bytes_read..bytes_read + to_read).ok_or(Error::Read)?;
                        dst_slice_opt.copy_from_slice(src_slice_opt);
                    }
                    dma::PingPongSelector::BufferB => {
                        let src_slice_opt = buffer_config
                            .buffer_b
                            .get(buffer_config.read_off..buffer_config.read_off + to_read)
                            .ok_or(Error::Read)?;
                        let dst_slice_opt = buf.get_mut(bytes_read..bytes_read + to_read).ok_or(Error::Read)?;
                        dst_slice_opt.copy_from_slice(src_slice_opt);
                    }
                }

                // Update counters
                bytes_read += to_read;
                buffer_config.read_off += to_read;

                // The whole half buffer has been read, switch to next buffer
                if buffer_config.read_off == half_size {
                    buffer_config.read_off = 0;
                    unsafe { rx_dma.commit_buffer(cur_buf) };

                    buffer_config.consumer_buf = match cur_buf {
                        dma::PingPongSelector::BufferA => dma::PingPongSelector::BufferB,
                        dma::PingPongSelector::BufferB => dma::PingPongSelector::BufferA,
                    };
                }

                embassy_time::Timer::after_micros(buffer_config.polling_rate).await;
            } else {
                poll_fn(|cx| {
                    self.info.rx_waker.register(cx.waker());

                    self.info.regs.intenset().write(|w| {
                        w.framerren()
                            .set_bit()
                            .parityerren()
                            .set_bit()
                            .rxnoiseen()
                            .set_bit()
                            .starten()
                            .set_bit()
                    });

                    self.info.regs.fifointenset().write(|w| w.rxerr().set_bit());

                    let stat = self.info.regs.stat().read();
                    let fifointstat = self.info.regs.fifointstat().read();

                    self.info.regs.stat().write(|w| {
                        w.framerrint()
                            .clear_bit_by_one()
                            .parityerrint()
                            .clear_bit_by_one()
                            .rxnoiseint()
                            .clear_bit_by_one()
                            .start()
                            .clear_bit_by_one()
                    });

                    self.info
                        .regs
                        .fifotrig()
                        .modify(|_, w| unsafe { w.rxlvlena().set_bit().rxlvl().bits(0) });
                    self.info.regs.fifointenset().write(|w| w.rxlvl().set_bit());

                    if stat.framerrint().bit_is_set() {
                        Poll::Ready(Err(Error::Framing))
                    } else if stat.parityerrint().bit_is_set() {
                        Poll::Ready(Err(Error::Parity))
                    } else if stat.rxnoiseint().bit_is_set() {
                        Poll::Ready(Err(Error::Noise))
                    } else if fifointstat.rxerr().bit_is_set() {
                        Poll::Ready(Err(Error::Overrun))
                    } else if stat.rxidle().bit_is_clear() {
                        Poll::Ready(Ok(()))
                    } else if stat.start().bit_is_set() {
                        Poll::Ready(Ok(()))
                    } else {
                        Poll::Pending
                    }
                })
                .await?;
            }
        }
        Ok(bytes_read)
    }
}

impl<'a> Uart<'a, Async> {
    /// Create a new DMA enabled UART
    pub fn new_async<T: Instance>(
        _inner: Peri<'a, T>,
        tx: Peri<'a, impl TxPin<T>>,
        rx: Peri<'a, impl RxPin<T>>,
        _irq: impl interrupt::typelevel::Binding<T::Interrupt, InterruptHandler<T>> + 'a,
        tx_dma: Peri<'a, impl TxDma<T>>,
        rx_dma: Peri<'a, impl RxDma<T>>,
        config: Config,
    ) -> Result<Self> {
        tx.as_tx();
        rx.as_rx();

        let tx = tx.into();
        let rx = rx.into();

        T::Interrupt::unpend();
        unsafe { T::Interrupt::enable() };

        let tx_dma = dma::Dma::reserve_channel(tx_dma);
        let rx_dma = dma::Dma::reserve_channel(rx_dma);

        let flexcomm = Self::init::<T>(Some(tx.into()), Some(rx.into()), None, None, config)?;

        Ok(Self {
            info: T::info(),
            tx: UartTx::new_inner::<T>(flexcomm.clone(), tx_dma),
            rx: UartRx::new_inner::<T>(flexcomm, rx_dma, None),
        })
    }

    /// Create a new DMA enabled UART with Rx buffering enabled
    #[cfg(feature = "time")]
    pub fn new_async_with_buffer<T: Instance>(
        _inner: Peri<'a, T>,
        tx: Peri<'a, impl TxPin<T>>,
        rx: Peri<'a, impl RxPin<T>>,
        _irq: impl interrupt::typelevel::Binding<T::Interrupt, InterruptHandler<T>> + 'a,
        tx_dma: Peri<'a, impl TxDma<T>>,
        rx_dma: Peri<'a, impl RxDma<T>>,
        config: Config,
        buffer: &'static mut [u8],
        polling_rate_us: u64,
    ) -> Result<Self> {
        tx.as_tx();
        rx.as_rx();

        let tx = tx.into();
        let rx = rx.into();

        T::Interrupt::unpend();
        unsafe { T::Interrupt::enable() };

        let tx_dma = dma::Dma::reserve_channel(tx_dma);
        let rx_dma: Channel<'_> = dma::Dma::reserve_channel(rx_dma).ok_or(Error::Fail)?;

        let flexcomm = Self::init::<T>(Some(tx.into()), Some(rx.into()), None, None, config)?;

        if !buffer.len().is_multiple_of(2) {
            return Err(Error::InvalidArgument);
        }

        let (buffer_a, buffer_b) = buffer.split_at_mut(buffer.len() / 2);
        T::info().regs.fifocfg().modify(|_, w| w.dmarx().enabled());
        // immediately configure and enable channel for ping-pong (double-buffered) reception
        rx_dma.configure_channel_ping_pong(
            dma::transfer::Direction::PeripheralToMemory,
            T::info().regs.fiford().as_ptr() as *const u8 as *const u32,
            buffer_a.as_mut_ptr() as *mut u32,
            buffer_b.as_mut_ptr() as *mut u32,
            buffer_a.len(),
            dma::transfer::TransferOptions {
                width: dma::transfer::Width::Bit8,
                priority: dma::transfer::Priority::Priority0,
            },
        );
        rx_dma.enable_channel();
        rx_dma.trigger_channel();

        Ok(Self {
            info: T::info(),
            tx: UartTx::new_inner::<T>(flexcomm.clone(), tx_dma),
            rx: UartRx::new_inner::<T>(
                flexcomm,
                Some(rx_dma),
                Some(BufferConfig {
                    buffer_a,
                    buffer_b,
                    read_off: 0,
                    polling_rate: polling_rate_us,
                    consumer_buf: dma::PingPongSelector::BufferA,
                }),
            ),
        })
    }
    /// Create a new DMA enabled UART with hardware flow control (RTS/CTS)
    pub fn new_with_rtscts<T: Instance>(
        _inner: Peri<'a, T>,
        tx: Peri<'a, impl TxPin<T>>,
        rx: Peri<'a, impl RxPin<T>>,
        rts: Peri<'a, impl RtsPin<T>>,
        cts: Peri<'a, impl CtsPin<T>>,
        _irq: impl interrupt::typelevel::Binding<T::Interrupt, InterruptHandler<T>> + 'a,
        tx_dma: Peri<'a, impl TxDma<T>>,
        rx_dma: Peri<'a, impl RxDma<T>>,
        config: Config,
    ) -> Result<Self> {
        tx.as_tx();
        rx.as_rx();
        rts.as_rts();
        cts.as_cts();

        let tx = tx.into();
        let rx = rx.into();
        let rts = rts.into();
        let cts = cts.into();

        T::Interrupt::unpend();
        unsafe { T::Interrupt::enable() };

        let tx_dma = dma::Dma::reserve_channel(tx_dma);
        let rx_dma = dma::Dma::reserve_channel(rx_dma);

        let flexcomm = Self::init::<T>(
            Some(tx.into()),
            Some(rx.into()),
            Some(rts.into()),
            Some(cts.into()),
            config,
        )?;

        Ok(Self {
            info: T::info(),
            tx: UartTx::new_inner::<T>(flexcomm.clone(), tx_dma),
            rx: UartRx::new_inner::<T>(flexcomm, rx_dma, None),
        })
    }

    /// Create a new DMA enabled UART with hardware flow control (RTS/CTS) and Rx buffering enabled
    #[allow(clippy::too_many_arguments)]
    #[cfg(feature = "time")]
    pub fn new_async_with_rtscts_buffer<T: Instance>(
        _inner: Peri<'a, T>,
        tx: Peri<'a, impl TxPin<T>>,
        rx: Peri<'a, impl RxPin<T>>,
        rts: Peri<'a, impl RtsPin<T>>,
        cts: Peri<'a, impl CtsPin<T>>,
        _irq: impl interrupt::typelevel::Binding<T::Interrupt, InterruptHandler<T>> + 'a,
        tx_dma: Peri<'a, impl TxDma<T>>,
        rx_dma: Peri<'a, impl RxDma<T>>,
        config: Config,
        buffer: &'static mut [u8],
        polling_rate_us: u64,
    ) -> Result<Self> {
        tx.as_tx();
        rx.as_rx();
        rts.as_rts();
        cts.as_cts();

        let tx = tx.into();
        let rx = rx.into();
        let rts = rts.into();
        let cts = cts.into();

        T::Interrupt::unpend();
        unsafe { T::Interrupt::enable() };

        let tx_dma = dma::Dma::reserve_channel(tx_dma);
        let rx_dma = dma::Dma::reserve_channel(rx_dma).ok_or(Error::Fail)?;

        let flexcomm = Self::init::<T>(
            Some(tx.into()),
            Some(rx.into()),
            Some(rts.into()),
            Some(cts.into()),
            config,
        )?;

        if !buffer.len().is_multiple_of(2) {
            return Err(Error::InvalidArgument);
        }

        let (buffer_a, buffer_b) = buffer.split_at_mut(buffer.len() / 2);
        T::info().regs.fifocfg().modify(|_, w| w.dmarx().enabled());
        // immediately configure and enable channel for ping-pong (double-buffered) reception
        rx_dma.configure_channel_ping_pong(
            dma::transfer::Direction::PeripheralToMemory,
            T::info().regs.fiford().as_ptr() as *const u8 as *const u32,
            buffer_a.as_mut_ptr() as *mut u32,
            buffer_b.as_mut_ptr() as *mut u32,
            buffer_a.len(),
            dma::transfer::TransferOptions {
                width: dma::transfer::Width::Bit8,
                priority: dma::transfer::Priority::Priority0,
            },
        );
        rx_dma.enable_channel();
        rx_dma.trigger_channel();

        Ok(Self {
            info: T::info(),
            tx: UartTx::new_inner::<T>(flexcomm.clone(), tx_dma),
            rx: UartRx::new_inner::<T>(
                flexcomm,
                Some(rx_dma),
                Some(BufferConfig {
                    buffer_a,
                    buffer_b,
                    read_off: 0,
                    polling_rate: polling_rate_us,
                    consumer_buf: dma::PingPongSelector::BufferA,
                }),
            ),
        })
    }

    /// Read from UART RX.
    pub fn read<'buf>(&mut self, buf: &'buf mut [u8]) -> impl Future<Output = Result<usize>> + use<'_, 'a, 'buf> {
        self.rx.read(buf)
    }

    /// Transmit the provided buffer.
    pub fn write<'buf>(&mut self, buf: &'buf [u8]) -> impl Future<Output = Result<()>> + use<'_, 'a, 'buf> {
        self.tx.write(buf)
    }

    /// Flush UART TX.
    pub fn flush(&mut self) -> impl Future<Output = Result<()>> + use<'_, 'a> {
        self.tx.flush()
    }
}

impl embedded_hal_02::serial::Read<u8> for UartRx<'_, Blocking> {
    type Error = Error;

    fn read(&mut self) -> core::result::Result<u8, nb::Error<Self::Error>> {
        let mut buf = [0; 1];

        match self.read(&mut buf) {
            Ok(_) => Ok(buf[0]),
            Err(Error::RxFifoEmpty) => Err(nb::Error::WouldBlock),
            Err(e) => Err(nb::Error::Other(e)),
        }
    }
}

impl embedded_hal_02::serial::Write<u8> for UartTx<'_, Blocking> {
    type Error = Error;

    fn write(&mut self, word: u8) -> core::result::Result<(), nb::Error<Self::Error>> {
        match self.write(&[word]) {
            Ok(_) => Ok(()),
            Err(Error::TxFifoFull) => Err(nb::Error::WouldBlock),
            Err(e) => Err(nb::Error::Other(e)),
        }
    }

    fn flush(&mut self) -> core::result::Result<(), nb::Error<Self::Error>> {
        match self.flush() {
            Ok(_) => Ok(()),
            Err(Error::TxBusy) => Err(nb::Error::WouldBlock),
            Err(e) => Err(nb::Error::Other(e)),
        }
    }
}

impl embedded_hal_02::blocking::serial::Write<u8> for UartTx<'_, Blocking> {
    type Error = Error;

    fn bwrite_all(&mut self, buffer: &[u8]) -> core::result::Result<(), Self::Error> {
        self.blocking_write(buffer)
    }

    fn bflush(&mut self) -> core::result::Result<(), Self::Error> {
        self.blocking_flush()
    }
}

impl embedded_hal_02::serial::Read<u8> for Uart<'_, Blocking> {
    type Error = Error;

    fn read(&mut self) -> core::result::Result<u8, nb::Error<Self::Error>> {
        embedded_hal_02::serial::Read::read(&mut self.rx)
    }
}

impl embedded_hal_02::serial::Write<u8> for Uart<'_, Blocking> {
    type Error = Error;

    fn write(&mut self, word: u8) -> core::result::Result<(), nb::Error<Self::Error>> {
        embedded_hal_02::serial::Write::write(&mut self.tx, word)
    }

    fn flush(&mut self) -> core::result::Result<(), nb::Error<Self::Error>> {
        embedded_hal_02::serial::Write::flush(&mut self.tx)
    }
}

impl embedded_hal_02::blocking::serial::Write<u8> for Uart<'_, Blocking> {
    type Error = Error;

    fn bwrite_all(&mut self, buffer: &[u8]) -> core::result::Result<(), Self::Error> {
        self.blocking_write(buffer)
    }

    fn bflush(&mut self) -> core::result::Result<(), Self::Error> {
        self.blocking_flush()
    }
}

impl embedded_hal_nb::serial::Error for Error {
    fn kind(&self) -> embedded_hal_nb::serial::ErrorKind {
        match *self {
            Self::Framing => embedded_hal_nb::serial::ErrorKind::FrameFormat,
            Self::Overrun => embedded_hal_nb::serial::ErrorKind::Overrun,
            Self::Parity => embedded_hal_nb::serial::ErrorKind::Parity,
            Self::Noise => embedded_hal_nb::serial::ErrorKind::Noise,
            _ => embedded_hal_nb::serial::ErrorKind::Other,
        }
    }
}

impl embedded_hal_nb::serial::ErrorType for UartRx<'_, Blocking> {
    type Error = Error;
}

impl embedded_hal_nb::serial::ErrorType for UartTx<'_, Blocking> {
    type Error = Error;
}

impl embedded_hal_nb::serial::ErrorType for Uart<'_, Blocking> {
    type Error = Error;
}

impl embedded_hal_nb::serial::Read for UartRx<'_, Blocking> {
    fn read(&mut self) -> nb::Result<u8, Self::Error> {
        let mut buf = [0; 1];

        match self.read(&mut buf) {
            Ok(_) => Ok(buf[0]),
            Err(Error::RxFifoEmpty) => Err(nb::Error::WouldBlock),
            Err(e) => Err(nb::Error::Other(e)),
        }
    }
}

impl embedded_hal_nb::serial::Write for UartTx<'_, Blocking> {
    fn write(&mut self, word: u8) -> nb::Result<(), Self::Error> {
        match self.write(&[word]) {
            Ok(_) => Ok(()),
            Err(Error::TxFifoFull) => Err(nb::Error::WouldBlock),
            Err(e) => Err(nb::Error::Other(e)),
        }
    }

    fn flush(&mut self) -> nb::Result<(), Self::Error> {
        match self.flush() {
            Ok(_) => Ok(()),
            Err(Error::TxBusy) => Err(nb::Error::WouldBlock),
            Err(e) => Err(nb::Error::Other(e)),
        }
    }
}

impl embedded_hal_nb::serial::Read for Uart<'_, Blocking> {
    fn read(&mut self) -> core::result::Result<u8, nb::Error<Self::Error>> {
        embedded_hal_02::serial::Read::read(&mut self.rx)
    }
}

impl embedded_hal_nb::serial::Write for Uart<'_, Blocking> {
    fn write(&mut self, char: u8) -> nb::Result<(), Self::Error> {
        self.blocking_write(&[char]).map_err(nb::Error::Other)
    }

    fn flush(&mut self) -> nb::Result<(), Self::Error> {
        self.blocking_flush().map_err(nb::Error::Other)
    }
}

impl embedded_io::Error for Error {
    fn kind(&self) -> embedded_io::ErrorKind {
        embedded_io::ErrorKind::Other
    }
}

impl embedded_io::ErrorType for UartRx<'_, Blocking> {
    type Error = Error;
}

impl embedded_io::ErrorType for UartTx<'_, Blocking> {
    type Error = Error;
}

impl embedded_io::ErrorType for Uart<'_, Blocking> {
    type Error = Error;
}

impl embedded_io::Read for UartRx<'_, Blocking> {
    fn read(&mut self, buf: &mut [u8]) -> core::result::Result<usize, Self::Error> {
        self.blocking_read(buf).map(|_| buf.len())
    }
}

impl embedded_io::Write for UartTx<'_, Blocking> {
    fn write(&mut self, buf: &[u8]) -> core::result::Result<usize, Self::Error> {
        self.blocking_write(buf).map(|_| buf.len())
    }

    fn flush(&mut self) -> core::result::Result<(), Self::Error> {
        self.blocking_flush()
    }
}

impl embedded_io::Read for Uart<'_, Blocking> {
    fn read(&mut self, buf: &mut [u8]) -> core::result::Result<usize, Self::Error> {
        embedded_io::Read::read(&mut self.rx, buf)
    }
}

impl embedded_io::Write for Uart<'_, Blocking> {
    fn write(&mut self, buf: &[u8]) -> core::result::Result<usize, Self::Error> {
        embedded_io::Write::write(&mut self.tx, buf)
    }

    fn flush(&mut self) -> core::result::Result<(), Self::Error> {
        embedded_io::Write::flush(&mut self.tx)
    }
}

impl embedded_io_async::ErrorType for UartRx<'_, Async> {
    type Error = Error;
}

impl embedded_io_async::ErrorType for UartTx<'_, Async> {
    type Error = Error;
}

impl embedded_io_async::ErrorType for Uart<'_, Async> {
    type Error = Error;
}

impl embedded_io_async::Read for UartRx<'_, Async> {
    async fn read(&mut self, buf: &mut [u8]) -> core::result::Result<usize, Self::Error> {
        self.read(buf).await
    }
}

impl embedded_io_async::Write for UartTx<'_, Async> {
    async fn write(&mut self, buf: &[u8]) -> core::result::Result<usize, Self::Error> {
        self.write(buf).await.map(|_| buf.len())
    }

    async fn flush(&mut self) -> core::result::Result<(), Self::Error> {
        self.flush().await
    }
}

impl embedded_io_async::Read for Uart<'_, Async> {
    async fn read(&mut self, buf: &mut [u8]) -> core::result::Result<usize, Self::Error> {
        embedded_io_async::Read::read(&mut self.rx, buf).await
    }
}

impl embedded_io_async::Write for Uart<'_, Async> {
    async fn write(&mut self, buf: &[u8]) -> core::result::Result<usize, Self::Error> {
        embedded_io_async::Write::write(&mut self.tx, buf).await
    }

    async fn flush(&mut self) -> core::result::Result<(), Self::Error> {
        embedded_io_async::Write::flush(&mut self.tx).await
    }
}

struct Info {
    regs: &'static crate::pac::usart0::RegisterBlock,
    tx_waker: &'static AtomicWaker,
    rx_waker: &'static AtomicWaker,
}

// SAFETY: safety for Send here is the same as the other accessors to unsafe blocks: it must be done from a single executor context.
//         This is a temporary workaround -- a better solution might be to refactor Info to no longer maintain a reference to regs,
//         but instead look up the correct register set and then perform operations within an unsafe block as we do for other peripherals
unsafe impl Send for Info {}

trait SealedInstance {
    fn info() -> Info;
    fn tx_waker() -> &'static AtomicWaker;
    fn rx_waker() -> &'static AtomicWaker;
}

/// UART interrupt handler.
pub struct InterruptHandler<T: Instance> {
    _phantom: PhantomData<T>,
}

impl<T: Instance> interrupt::typelevel::Handler<T::Interrupt> for InterruptHandler<T> {
    unsafe fn on_interrupt() {
        let regs = T::info().regs;
        let stat = regs.intstat().read();

        if stat.txidle().bit_is_set() {
            regs.intenclr().write(|w| w.txidleclr().set_bit());
            T::tx_waker().wake();
        }

        if stat.framerrint().bit_is_set() || stat.parityerrint().bit_is_set() || stat.rxnoiseint().bit_is_set() {
            regs.intenclr()
                .write(|w| w.framerrclr().set_bit().parityerrclr().set_bit().rxnoiseclr().set_bit());
            T::rx_waker().wake();
        }

        if stat.start().bit_is_set() {
            regs.intenclr().write(|w| w.startclr().set_bit());
            T::rx_waker().wake();
        }

        let fifointstat = regs.fifointstat().read();
        if fifointstat.txerr().bit_is_set() {
            regs.fifointenclr().write(|w| w.txerr().set_bit());
            T::tx_waker().wake();
        }

        if fifointstat.txlvl().bit_is_set() {
            regs.fifointenclr().write(|w| w.txlvl().set_bit());
            T::tx_waker().wake();
        }

        if fifointstat.rxerr().bit_is_set() {
            regs.fifointenclr().write(|w| w.rxerr().set_bit());
            T::rx_waker().wake();
        }

        if fifointstat.rxlvl().bit_is_set() {
            regs.fifointenclr().write(|w| w.rxlvl().set_bit());
            T::rx_waker().wake();
        }
    }
}

/// UART instance trait.
#[allow(private_bounds)]
pub trait Instance: crate::flexcomm::IntoUsart + SealedInstance + PeripheralType + 'static + Send {
    /// Interrupt for this UART instance.
    type Interrupt: interrupt::typelevel::Interrupt;
}

macro_rules! impl_instance {
    ($($n:expr),*) => {
        $(
            paste!{
                impl SealedInstance for crate::peripherals::[<FLEXCOMM $n>] {
                    fn info() -> Info {
                        Info {
                            regs: unsafe { &*crate::pac::[<Usart $n>]::ptr() },
                            tx_waker: Self::tx_waker(),
                            rx_waker: Self::rx_waker(),
                        }
                    }

                    fn tx_waker() -> &'static AtomicWaker {
                        static TX_WAKER: AtomicWaker = AtomicWaker::new();
                        &TX_WAKER
                    }

                    fn rx_waker() -> &'static AtomicWaker {
                        static RX_WAKER: AtomicWaker = AtomicWaker::new();
                        &RX_WAKER
                    }
                }

                impl Instance for crate::peripherals::[<FLEXCOMM $n>] {
                    type Interrupt = crate::interrupt::typelevel::[<FLEXCOMM $n>];
                }
            }
        )*
    };
}

impl_instance!(0, 1, 2, 3, 4, 5, 6, 7);

mod sealed {
    /// simply seal a trait
    pub trait Sealed {}
}

impl<T: Pin> sealed::Sealed for T {}

/// io configuration trait for Uart Tx configuration
pub trait TxPin<T: Instance>: Pin + sealed::Sealed + PeripheralType {
    /// convert the pin to appropriate function for Uart Tx  usage
    fn as_tx(&self);
}

/// io configuration trait for Uart Rx configuration
pub trait RxPin<T: Instance>: Pin + sealed::Sealed + PeripheralType {
    /// convert the pin to appropriate function for Uart Rx  usage
    fn as_rx(&self);
}

/// io configuration trait for Uart Cts
pub trait CtsPin<T: Instance>: Pin + sealed::Sealed + PeripheralType {
    /// convert the pin to appropriate function for Uart Cts usage
    fn as_cts(&self);
}

/// io configuration trait for Uart Rts
pub trait RtsPin<T: Instance>: Pin + sealed::Sealed + PeripheralType {
    /// convert the pin to appropriate function for Uart Rts usage
    fn as_rts(&self);
}

macro_rules! impl_pin_trait {
    ($fcn:ident, $mode:ident, $($pin:ident, $fn:ident),*) => {
        paste! {
            $(
                impl [<$mode:camel Pin>]<crate::peripherals::$fcn> for crate::peripherals::$pin {
                    fn [<as_ $mode>](&self) {
                        // UM11147 table 507 pg 495
                        self.set_function(crate::iopctl::Function::$fn)
                            .set_pull(Pull::None)
                            .enable_input_buffer()
                            .set_slew_rate(SlewRate::Standard)
                            .set_drive_strength(DriveStrength::Normal)
                            .disable_analog_multiplex()
                            .set_drive_mode(DriveMode::PushPull)
                            .set_input_inverter(Inverter::Disabled);
                    }
                }
            )*
        }
    };
}

// FLEXCOMM0
impl_pin_trait!(FLEXCOMM0, tx, PIO0_1, F1, PIO3_1, F5);
impl_pin_trait!(FLEXCOMM0, rx, PIO0_2, F1, PIO3_2, F5);
impl_pin_trait!(FLEXCOMM0, cts, PIO0_3, F1, PIO3_3, F5);
impl_pin_trait!(FLEXCOMM0, rts, PIO0_4, F1, PIO3_4, F5);

// FLEXCOMM1
impl_pin_trait!(FLEXCOMM1, tx, PIO0_8, F1, PIO7_26, F1);
impl_pin_trait!(FLEXCOMM1, rx, PIO0_9, F1, PIO7_27, F1);
impl_pin_trait!(FLEXCOMM1, cts, PIO0_10, F1, PIO7_28, F1);
impl_pin_trait!(FLEXCOMM1, rts, PIO0_11, F1, PIO7_29, F1);

// FLEXCOMM2
impl_pin_trait!(FLEXCOMM2, tx, PIO0_15, F1, PIO7_30, F5);
impl_pin_trait!(FLEXCOMM2, rx, PIO0_16, F1, PIO7_31, F5);
impl_pin_trait!(FLEXCOMM2, cts, PIO0_17, F1, PIO4_8, F5);
impl_pin_trait!(FLEXCOMM2, rts, PIO0_18, F1);

// FLEXCOMM3
impl_pin_trait!(FLEXCOMM3, tx, PIO0_22, F1);
impl_pin_trait!(FLEXCOMM3, rx, PIO0_23, F1);
impl_pin_trait!(FLEXCOMM3, cts, PIO0_24, F1);
impl_pin_trait!(FLEXCOMM3, rts, PIO0_25, F1);

// FLEXCOMM4
impl_pin_trait!(FLEXCOMM4, tx, PIO0_29, F1);
impl_pin_trait!(FLEXCOMM4, rx, PIO0_30, F1);
impl_pin_trait!(FLEXCOMM4, cts, PIO0_31, F1);
impl_pin_trait!(FLEXCOMM4, rts, PIO1_0, F1);

// FLEXCOMM5
impl_pin_trait!(FLEXCOMM5, tx, PIO1_4, F1, PIO3_16, F5);
impl_pin_trait!(FLEXCOMM5, rx, PIO1_5, F1, PIO3_17, F5);
impl_pin_trait!(FLEXCOMM5, cts, PIO1_6, F1, PIO3_18, F5);
impl_pin_trait!(FLEXCOMM5, rts, PIO1_7, F1, PIO3_23, F5);

// FLEXCOMM6
impl_pin_trait!(FLEXCOMM6, tx, PIO3_26, F1);
impl_pin_trait!(FLEXCOMM6, rx, PIO3_27, F1);
impl_pin_trait!(FLEXCOMM6, cts, PIO3_28, F1);
impl_pin_trait!(FLEXCOMM6, rts, PIO3_29, F1);

// FLEXCOMM7
impl_pin_trait!(FLEXCOMM7, tx, PIO4_1, F1);
impl_pin_trait!(FLEXCOMM7, rx, PIO4_2, F1);
impl_pin_trait!(FLEXCOMM7, cts, PIO4_3, F1);
impl_pin_trait!(FLEXCOMM7, rts, PIO4_4, F1);

/// UART Tx DMA trait.
#[allow(private_bounds)]
pub trait TxDma<T: Instance>: dma::Instance {}

/// UART Rx DMA trait.
#[allow(private_bounds)]
pub trait RxDma<T: Instance>: dma::Instance {}

macro_rules! impl_dma {
    ($fcn:ident, $mode:ident, $dma:ident) => {
        paste! {
            impl [<$mode Dma>]<crate::peripherals::$fcn> for crate::peripherals::$dma {}
        }
    };
}

impl_dma!(FLEXCOMM0, Rx, DMA0_CH0);
impl_dma!(FLEXCOMM0, Tx, DMA0_CH1);

impl_dma!(FLEXCOMM1, Rx, DMA0_CH2);
impl_dma!(FLEXCOMM1, Tx, DMA0_CH3);

impl_dma!(FLEXCOMM2, Rx, DMA0_CH4);
impl_dma!(FLEXCOMM2, Tx, DMA0_CH5);

impl_dma!(FLEXCOMM3, Rx, DMA0_CH6);
impl_dma!(FLEXCOMM3, Tx, DMA0_CH7);

impl_dma!(FLEXCOMM4, Rx, DMA0_CH8);
impl_dma!(FLEXCOMM4, Tx, DMA0_CH9);

impl_dma!(FLEXCOMM5, Rx, DMA0_CH10);
impl_dma!(FLEXCOMM5, Tx, DMA0_CH11);

impl_dma!(FLEXCOMM6, Rx, DMA0_CH12);
impl_dma!(FLEXCOMM6, Tx, DMA0_CH13);

impl_dma!(FLEXCOMM7, Rx, DMA0_CH14);
impl_dma!(FLEXCOMM7, Tx, DMA0_CH15);
