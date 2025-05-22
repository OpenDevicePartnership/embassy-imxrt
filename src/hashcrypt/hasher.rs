use core::future::poll_fn;
use core::iter::zip;
use core::marker::PhantomData;
use core::task::Poll;

use embassy_futures::select::select;
use embassy_sync::waitqueue::AtomicWaker;

use super::{Async, Blocking, Hashcrypt, Mode};
use crate::dma::transfer::{Transfer, Width};
use crate::{dma, interrupt};

/// Block length
pub const BLOCK_LEN: usize = 64;
/// Hash length
pub const HASH_LEN: usize = 32;
const END_BYTE: u8 = 0x80;

// 9 from the end byte and the 64-bit length
const LAST_BLOCK_MAX_DATA: usize = BLOCK_LEN - 9;

static WAKER: AtomicWaker = AtomicWaker::new();

#[cfg(feature = "rt")]
#[interrupt]
fn HASHCRYPT() {
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

/// A hasher
pub struct Hasher<'d, 'a, M: Mode> {
    hashcrypt: &'a mut Hashcrypt<'d, M>,
    _mode: PhantomData<M>,
    written: usize,
}

impl<'d, 'a, M: Mode> Hasher<'d, 'a, M> {
    pub(super) fn new_inner(hashcrypt: &'a mut Hashcrypt<'d, M>) -> Self {
        Self {
            hashcrypt,
            _mode: PhantomData,
            written: 0,
        }
    }

    fn init_final_data(&self, data: &[u8], buffer: &mut [u8; BLOCK_LEN]) {
        buffer[..data.len()].copy_from_slice(data);
        buffer[data.len()] = END_BYTE;
    }

    fn init_final_block(&self, data: &[u8], buffer: &mut [u8; BLOCK_LEN]) {
        self.init_final_data(data, buffer);
        self.init_final_len(buffer);
    }

    fn init_final_len(&self, buffer: &mut [u8; BLOCK_LEN]) {
        buffer[BLOCK_LEN - 8..BLOCK_LEN].copy_from_slice(&(8 * self.written as u64).to_be_bytes());
    }

    fn wait_for_digest(&self) {
        while self.hashcrypt.hashcrypt.status().read().digest().is_not_ready() {}
    }

    fn read_hash(&mut self, hash: &mut [u8; HASH_LEN]) {
        for (reg, chunk) in zip(self.hashcrypt.hashcrypt.digest0_iter(), hash.chunks_mut(4)) {
            // Values in digest registers are little-endian, swap to BE to convert to a stream of bytes
            chunk.copy_from_slice(&reg.read().bits().to_be_bytes());
        }
    }
}

impl<'d, 'a> Hasher<'d, 'a, Blocking> {
    /// Create a new hasher instance
    pub fn new_blocking(hashcrypt: &'a mut Hashcrypt<'d, Blocking>) -> Self {
        Self::new_inner(hashcrypt)
    }

    fn transfer_block(&mut self, data: &[u8; BLOCK_LEN]) {
        for word in data.chunks(4) {
            self.hashcrypt
                .hashcrypt
                .indata()
                .write(|w| unsafe { w.data().bits(u32::from_le_bytes([word[0], word[1], word[2], word[3]])) });
        }
        self.wait_for_digest();
    }

    /// Submit one or more blocks of data to the hasher, data must be a multiple of the block length
    pub fn submit_blocks(&mut self, data: &[u8]) {
        if data.is_empty() || data.len() % BLOCK_LEN != 0 {
            panic!("Invalid data length");
        }

        for block in data.chunks(BLOCK_LEN) {
            self.transfer_block(block.try_into().unwrap());
        }
        self.written += data.len();
    }

    /// Submits the final data for hashing
    pub fn finalize(mut self, data: &[u8], hash: &mut [u8; HASH_LEN]) {
        let mut buffer = [0u8; BLOCK_LEN];

        self.written += data.len();
        if data.len() <= LAST_BLOCK_MAX_DATA {
            // Only have one final block
            self.init_final_block(data, &mut buffer);
            self.transfer_block(&buffer);
        } else {
            //End byte and padding won't fit in this block, submit this block and an extra one
            self.init_final_data(data, &mut buffer);
            self.transfer_block(&buffer);

            buffer.fill(0);
            self.init_final_len(&mut buffer);
            self.transfer_block(&buffer);
        }

        self.read_hash(hash);
    }

    /// Computes the hash of the given data
    pub fn hash(mut self, data: &[u8], hash: &mut [u8; HASH_LEN]) {
        let full_blocks = data.len() / BLOCK_LEN;

        if full_blocks > 0 {
            self.submit_blocks(&data[0..full_blocks * BLOCK_LEN]);
        }
        self.finalize(&data[full_blocks * BLOCK_LEN..], hash);
    }
}

impl<'d, 'a> Hasher<'d, 'a, Async> {
    /// Create a new hasher instance
    pub fn new_async(hashcrypt: &'a mut Hashcrypt<'d, Async>) -> Self {
        Self::new_inner(hashcrypt)
    }

    async fn transfer(&mut self, data: &[u8]) {
        if data.is_empty() || data.len() % BLOCK_LEN != 0 {
            panic!("Invalid data length");
        }

        let options = dma::transfer::TransferOptions {
            width: Width::Bit32,
            ..Default::default()
        };

        let transfer = Transfer::new_write(
            self.hashcrypt.dma_ch.as_ref().unwrap(),
            data,
            self.hashcrypt.hashcrypt.indata().as_ptr() as *mut u8,
            options,
        );

        select(
            transfer,
            poll_fn(|cx| {
                // Check if transfer ended with an error
                if self.hashcrypt.hashcrypt.status().read().error().is_error() {
                    return Poll::Ready(());
                }

                WAKER.register(cx.waker());
                self.hashcrypt.hashcrypt.intenset().write(|w| w.error().interrupt());
                Poll::Pending
            }),
        )
        .await;

        poll_fn(|cx| {
            // Check if digest is ready
            if self.hashcrypt.hashcrypt.status().read().digest().is_ready() {
                return Poll::Ready(());
            }

            WAKER.register(cx.waker());
            self.hashcrypt.hashcrypt.intenset().write(|w| w.digest().interrupt());
            Poll::Pending
        })
        .await;
    }

    /// Submit one or more blocks of data to the hasher, data must be a multiple of the block length
    pub async fn submit_blocks(&mut self, data: &[u8]) {
        self.transfer(data).await;
        self.written += data.len();
    }

    /// Submits the final data for hashing
    pub async fn finalize(mut self, data: &[u8], hash: &mut [u8; HASH_LEN]) {
        let mut buffer = [0u8; BLOCK_LEN];

        self.written += data.len();
        if data.len() <= LAST_BLOCK_MAX_DATA {
            // Only have one final block
            self.init_final_block(data, &mut buffer);
            self.transfer(&buffer).await;
        } else {
            //End byte and padding won't fit in this block, submit this block and an extra one
            self.init_final_data(data, &mut buffer);
            self.transfer(&buffer).await;

            buffer.fill(0);
            self.init_final_len(&mut buffer);
            self.transfer(&buffer).await;
        }

        self.read_hash(hash);
    }

    /// Computes the hash of the given data
    pub async fn hash(mut self, data: &[u8], hash: &mut [u8; HASH_LEN]) {
        let full_blocks = data.len() / BLOCK_LEN;

        if full_blocks > 0 {
            self.submit_blocks(&data[0..full_blocks * BLOCK_LEN]).await;
        }
        self.finalize(&data[full_blocks * BLOCK_LEN..], hash).await;
    }
}
