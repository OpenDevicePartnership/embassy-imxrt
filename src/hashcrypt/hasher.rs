use core::future::poll_fn;
use core::iter::zip;
use core::marker::PhantomData;
use core::task::Poll;

use embassy_futures::select::select;

use super::{Async, Blocking, Error, Hashcrypt, Mode};
use crate::dma;
use crate::dma::transfer::{Transfer, Width};

/// Block length
pub const BLOCK_LEN: usize = 64;
/// Hash length
pub const HASH_LEN: usize = 32;
const END_BYTE: u8 = 0x80;

// 9 from the end byte and the 64-bit length
const LAST_BLOCK_MAX_DATA: usize = BLOCK_LEN - 9;

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

    fn init_final_data(&self, data: &[u8], buffer: &mut [u8; BLOCK_LEN]) -> Result<(), Error> {
        buffer
            .get_mut(..data.len())
            .ok_or(Error::UnsupportedConfiguration)?
            .copy_from_slice(data);
        *buffer.get_mut(data.len()).ok_or(Error::UnsupportedConfiguration)? = END_BYTE;
        Ok(())
    }

    fn init_final_block(&self, data: &[u8], buffer: &mut [u8; BLOCK_LEN]) -> Result<(), Error> {
        self.init_final_data(data, buffer)?;
        self.init_final_len(buffer)
    }

    fn init_final_len(&self, buffer: &mut [u8; BLOCK_LEN]) -> Result<(), Error> {
        buffer
            .get_mut(BLOCK_LEN - 8..BLOCK_LEN)
            .ok_or(Error::UnsupportedConfiguration)?
            .copy_from_slice(&(8 * self.written as u64).to_be_bytes());
        Ok(())
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
            self.hashcrypt.hashcrypt.indata().write(|w| unsafe {
                #[allow(clippy::indexing_slicing)]
                // panic safety: word is always 4 bytes and BLOCK_LEN is multiple of 4
                w.data().bits(u32::from_le_bytes([word[0], word[1], word[2], word[3]]))
            });
        }
        self.wait_for_digest();
    }

    /// Submit one or more blocks of data to the hasher, data must be a multiple of the block length
    pub fn submit_blocks(&mut self, data: &[u8]) -> Result<(), Error> {
        if data.is_empty() || !data.len().is_multiple_of(BLOCK_LEN) {
            return Err(Error::UnsupportedConfiguration);
        }

        for block in data.chunks(BLOCK_LEN) {
            #[allow(clippy::unwrap_used)] // panic safety: block is always BLOCK_LEN bytes with check above
            self.transfer_block(block.try_into().unwrap());
        }
        self.written += data.len();
        Ok(())
    }

    /// Submits the final data for hashing
    pub fn finalize(mut self, data: &[u8], hash: &mut [u8; HASH_LEN]) -> Result<(), Error> {
        let mut buffer = [0u8; BLOCK_LEN];

        self.written += data.len();
        if data.len() <= LAST_BLOCK_MAX_DATA {
            // Only have one final block
            self.init_final_block(data, &mut buffer)?;
            self.transfer_block(&buffer);
        } else {
            //End byte and padding won't fit in this block, submit this block and an extra one
            self.init_final_data(data, &mut buffer)?;
            self.transfer_block(&buffer);

            buffer.fill(0);
            self.init_final_len(&mut buffer)?;
            self.transfer_block(&buffer);
        }

        self.read_hash(hash);

        Ok(())
    }

    /// Computes the hash of the given data
    pub fn hash(mut self, data: &[u8], hash: &mut [u8; HASH_LEN]) -> Result<(), Error> {
        let mut iter = data.chunks_exact(BLOCK_LEN);

        for block in &mut iter {
            self.submit_blocks(block)?;
        }

        self.finalize(iter.remainder(), hash)?;

        Ok(())
    }
}

impl<'d, 'a> Hasher<'d, 'a, Async> {
    /// Create a new hasher instance
    pub fn new_async(hashcrypt: &'a mut Hashcrypt<'d, Async>) -> Self {
        Self::new_inner(hashcrypt)
    }

    async fn transfer(&mut self, data: &[u8]) -> Result<(), Error> {
        if data.is_empty() || !data.len().is_multiple_of(BLOCK_LEN) {
            return Err(Error::UnsupportedConfiguration);
        }

        let options = dma::transfer::TransferOptions {
            width: Width::Bit32,
            ..Default::default()
        };

        let transfer = Transfer::new_write(
            self.hashcrypt.dma_ch.as_ref().ok_or(Error::UnsupportedConfiguration)?,
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

                super::WAKER.register(cx.waker());
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

            super::WAKER.register(cx.waker());
            self.hashcrypt.hashcrypt.intenset().write(|w| w.digest().interrupt());
            Poll::Pending
        })
        .await;

        Ok(())
    }

    /// Submit one or more blocks of data to the hasher, data must be a multiple of the block length
    pub async fn submit_blocks(&mut self, data: &[u8]) -> Result<(), Error> {
        self.transfer(data).await?;
        self.written += data.len();
        Ok(())
    }

    /// Submits the final data for hashing
    pub async fn finalize(mut self, data: &[u8], hash: &mut [u8; HASH_LEN]) -> Result<(), Error> {
        let mut buffer = [0u8; BLOCK_LEN];

        self.written += data.len();
        if data.len() <= LAST_BLOCK_MAX_DATA {
            // Only have one final block
            self.init_final_block(data, &mut buffer)?;
            self.transfer(&buffer).await?;
        } else {
            //End byte and padding won't fit in this block, submit this block and an extra one
            self.init_final_data(data, &mut buffer)?;
            self.transfer(&buffer).await?;
            buffer.fill(0);
            self.init_final_len(&mut buffer)?;
            self.transfer(&buffer).await?;
        }

        self.read_hash(hash);
        Ok(())
    }

    /// Computes the hash of the given data
    pub async fn hash(mut self, data: &[u8], hash: &mut [u8; HASH_LEN]) -> Result<(), Error> {
        let mut iter = data.chunks_exact(BLOCK_LEN);

        for block in &mut iter {
            self.submit_blocks(block).await?;
        }

        self.finalize(iter.remainder(), hash).await
    }
}
