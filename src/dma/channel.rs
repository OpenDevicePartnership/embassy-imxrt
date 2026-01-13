//! DMA channel & request

use core::marker::PhantomData;

use embassy_sync::waitqueue::AtomicWaker;

use super::{BufferConsumeStatus, DESCRIPTORS, PING_DESCRIPTORS, PING_PONG_STATUS, PONG_DESCRIPTORS, PingPongSelector};
use crate::dma::DmaInfo;
use crate::dma::transfer::{Direction, Transfer, TransferOptions};

/// DMA channel
pub struct Channel<'d> {
    /// DMA channel peripheral reference
    pub(super) info: DmaInfo,
    /// Keep track of lifetime for Channel within the DMA module
    pub(super) _lifetime: PhantomData<&'d ()>,
}

impl<'d> Channel<'d> {
    /// Reads from a peripheral into a memory buffer
    pub fn read_from_peripheral(
        &'d self,
        peri_addr: *const u8,
        buf: &'d mut [u8],
        options: TransferOptions,
    ) -> Transfer<'d> {
        Transfer::new_read(self, peri_addr, buf, options)
    }

    /// Writes from a memory buffer to a peripheral
    pub fn write_to_peripheral(&'d self, buf: &'d [u8], peri_addr: *mut u8, options: TransferOptions) -> Transfer<'d> {
        Transfer::new_write(self, buf, peri_addr, options)
    }

    /// Writes from a memory buffer to another memory buffer
    pub fn write_to_memory(
        &'d self,
        src_buf: &'d [u8],
        dst_buf: &'d mut [u8],
        options: TransferOptions,
    ) -> Transfer<'d> {
        Transfer::new_write_mem(self, src_buf, dst_buf, options)
    }

    /// Return a reference to the channel's waker
    pub fn get_waker(&self) -> &'d AtomicWaker {
        self.info.waker
    }

    /// Return the channel number
    pub fn get_channel_number(&self) -> usize {
        self.info.ch_num
    }

    /// Check whether DMA is active
    pub fn is_active(&self) -> bool {
        let channel = self.info.ch_num;
        self.info.regs.active0().read().act().bits() & (1 << channel) != 0
    }

    /// Check whether DMA is busy
    pub fn is_busy(&self) -> bool {
        let channel = self.info.ch_num;
        self.info.regs.busy0().read().bsy().bits() & (1 << channel) != 0
    }

    /// Return DMA remaining transfer count
    /// To get number of bytes, do `(XFERCOUNT + 1) x data width`
    pub fn get_xfer_count(&self) -> u16 {
        let channel = self.info.ch_num;
        self.info.regs.channel(channel).xfercfg().read().xfercount().bits()
    }

    /// Abort DMA operation
    pub fn abort(&self) {
        let channel = self.info.ch_num;
        self.disable_channel();
        while self.is_busy() {}
        self.info.regs.abort0().write(|w|
            // SAFETY: unsafe due to .bits usage
            unsafe { w.bits(1 << channel) });
    }

    /// Prepare the DMA channel for the transfer
    ///
    /// # Note
    ///
    /// `mem_len` should be a multiple of the transfer width, otherwise transfer count will be rounded down
    pub fn configure_channel(
        &self,
        dir: Direction,
        srcbase: *const u32,
        dstbase: *mut u32,
        mem_len: usize,
        options: TransferOptions,
    ) {
        debug_assert!(mem_len.is_multiple_of(options.width.byte_width()));

        let xferwidth: usize = options.width.byte_width();
        let xfercount = (mem_len / xferwidth) - 1;
        let channel = self.info.ch_num;

        // Panic safety: `info()` would have returned None if our channel number was out of bounds and thus would never get here
        // SAFETY: unsafe due to use of a mutable static (DESCRIPTORS.list)
        #[allow(clippy::indexing_slicing)]
        let descriptor = unsafe { &mut DESCRIPTORS.list[channel] };

        // Configure the channel descriptor
        // NOTE: the DMA controller expects the memory buffer end address but peripheral address is actual
        descriptor.reserved = 0;
        if dir == Direction::MemoryToPeripheral {
            descriptor.dst_data_end_addr = dstbase as u32;
        } else {
            descriptor.dst_data_end_addr = dstbase as u32 + (xfercount * xferwidth) as u32;
        }
        if dir == Direction::PeripheralToMemory {
            descriptor.src_data_end_addr = srcbase as u32;
        } else {
            descriptor.src_data_end_addr = srcbase as u32 + (xfercount * xferwidth) as u32;
        }
        descriptor.nxt_desc_link_addr = 0;

        // Configure for transfer type, no hardware triggering (we'll trigger via software), high priority
        // SAFETY: unsafe due to .bits usage
        self.info.regs.channel(channel).cfg().write(|w| unsafe {
            if dir == Direction::MemoryToMemory {
                w.periphreqen().clear_bit();
            } else {
                w.periphreqen().set_bit();
            }
            w.hwtrigen().clear_bit();
            w.chpriority().bits(0)
        });

        // Enable the interrupt on this channel
        self.info
            .regs
            .intenset0()
            .write(|w| unsafe { w.inten().bits(1 << channel) });

        // Mark configuration valid, clear trigger on complete, width is 1 byte, source & destination increments are width x 1 (1 byte), no reload
        // SAFETY: unsafe due to .bits usage
        self.info.regs.channel(channel).xfercfg().write(|w| unsafe {
            w.cfgvalid().set_bit();
            w.clrtrig().set_bit();
            w.reload().clear_bit();
            w.setinta().set_bit();
            w.width().bits(options.width.into());
            if dir == Direction::PeripheralToMemory {
                w.srcinc().bits(0);
            } else {
                w.srcinc().bits(1);
            }
            if dir == Direction::MemoryToPeripheral {
                w.dstinc().bits(0);
            } else {
                w.dstinc().bits(1);
            }
            w.xfercount().bits(xfercount as u16)
        });
    }

    /// Configure the DMA channel for ping-pong (double buffer) transfer
    ///
    /// # Note
    ///
    /// `mem_len` should be a multiple of the transfer width, otherwise transfer count will be rounded down
    pub fn configure_channel_ping_pong(
        &self,
        dir: Direction,
        srcbase: *const u32,
        dstbase_a: *mut u32,
        dstbase_b: *mut u32,
        mem_len: usize,
        options: TransferOptions,
    ) {
        debug_assert!(mem_len.is_multiple_of(options.width.byte_width()));

        let xferwidth: usize = options.width.byte_width();
        let xfercount = (mem_len / xferwidth) - 1;
        let channel = self.info.ch_num;

        // Configure for transfer type, no hardware triggering (we'll trigger via software), high priority
        // SAFETY: unsafe due to .bits usage
        self.info.regs.channel(channel).cfg().write(|w| unsafe {
            if dir == Direction::MemoryToMemory {
                w.periphreqen().clear_bit();
            } else {
                w.periphreqen().set_bit();
            }
            w.hwtrigen().clear_bit();
            w.chpriority().bits(0)
        });

        // Enable the interrupt on this channel
        self.info
            .regs
            .intenset0()
            .write(|w| unsafe { w.inten().bits(1 << channel) });

        // Mark configuration valid, clear trigger on complete, width is 1 byte, source & destination increments are width x 1 (1 byte)
        // SAFETY: unsafe due to .bits usage
        self.info.regs.channel(channel).xfercfg().write(|w| unsafe {
            w.cfgvalid().set_bit();
            // Descriptor is exhausted and we need to manually hit SWTRIG to trigger the next one.
            w.clrtrig().set_bit();
            // Set reload to enable continuous ping-pong operation
            w.reload().set_bit();
            w.setinta().set_bit();
            w.width().bits(options.width.into());
            if dir == Direction::PeripheralToMemory {
                w.srcinc().bits(0);
            } else {
                w.srcinc().bits(1);
            }
            if dir == Direction::MemoryToPeripheral {
                w.dstinc().bits(0);
            } else {
                w.dstinc().bits(1);
            }
            w.xfercount().bits(xfercount as u16)
        });

        #[allow(clippy::indexing_slicing)]
        let descriptor_initial = unsafe { &mut DESCRIPTORS.list[channel] };
        #[allow(clippy::indexing_slicing)]
        let descriptor_a = unsafe { &mut PING_DESCRIPTORS.list[channel] };
        #[allow(clippy::indexing_slicing)]
        let descriptor_b = unsafe { &mut PONG_DESCRIPTORS.list[channel] };

        // Configure the channel descriptor
        // NOTE: the DMA controller expects the memory buffer end address but peripheral address is actual
        let xfer_cfg = self.info.regs.channel(channel).xfercfg().read();
        descriptor_initial.reserved = 0;
        descriptor_a.reserved = xfer_cfg.bits();
        descriptor_b.reserved = xfer_cfg.bits();

        descriptor_initial.src_data_end_addr = srcbase as u32;
        descriptor_initial.dst_data_end_addr = dstbase_a as u32 + (xfercount * xferwidth) as u32;
        descriptor_initial.nxt_desc_link_addr = descriptor_b as *const _ as u32;

        descriptor_b.src_data_end_addr = srcbase as u32;
        descriptor_b.dst_data_end_addr = dstbase_b as u32 + (xfercount * xferwidth) as u32;
        descriptor_b.nxt_desc_link_addr = descriptor_a as *const _ as u32;

        descriptor_a.src_data_end_addr = srcbase as u32;
        descriptor_a.dst_data_end_addr = dstbase_a as u32 + (xfercount * xferwidth) as u32;
        descriptor_a.nxt_desc_link_addr = descriptor_b as *const _ as u32;

        #[allow(clippy::indexing_slicing)]
        let ping_pong_status = unsafe { &mut PING_PONG_STATUS[channel] };
        ping_pong_status.current = PingPongSelector::BufferA;
        ping_pong_status.buffer_a_status = BufferConsumeStatus::Committed;
        ping_pong_status.buffer_b_status = BufferConsumeStatus::Committed;

        info!("DMA Ping-Pong Descriptors set up on channel {}", channel);
    }

    /// Enable the DMA channel (only after configuring)
    // SAFETY: unsafe due to .bits usage
    pub fn enable_channel(&self) {
        let channel = self.info.ch_num;
        self.info
            .regs
            .enableset0()
            .modify(|_, w| unsafe { w.ena().bits(1 << channel) });
    }

    /// Disable the DMA channel
    pub fn disable_channel(&self) {
        let channel = self.info.ch_num;
        self.info.regs.enableclr0().write(|w|
            // SAFETY: unsafe due to .bits usage
            unsafe { w.clr().bits(1 << channel) });
    }

    /// Trigger the DMA channel
    pub fn trigger_channel(&self) {
        let channel = self.info.ch_num;
        self.info
            .regs
            .channel(channel)
            .xfercfg()
            .modify(|_, w| w.swtrig().set_bit());
    }

    /// Return the current ping-pong buffer being used by the DMA channel
    pub fn current_buffer(&self) -> PingPongSelector {
        let channel = self.info.ch_num;
        #[allow(clippy::indexing_slicing)]
        let ping_pong_status = unsafe { &PING_PONG_STATUS[channel] };
        ping_pong_status.current
    }

    /// Mark the specified ping-pong buffer as committed (ready for DMA to use)
    ///
    /// # Safety
    ///
    /// The caller must ensure that the buffer being committed is not currently being accessed
    /// by the DMA controller or other parts of the system.
    pub unsafe fn commit_buffer(&self, selector: PingPongSelector) {
        let channel = self.info.ch_num;
        #[allow(clippy::indexing_slicing)]
        let ping_pong_status = unsafe { &mut PING_PONG_STATUS[channel] };
        match selector {
            PingPongSelector::BufferA => {
                ping_pong_status.buffer_a_status = BufferConsumeStatus::Committed;
            }
            PingPongSelector::BufferB => {
                ping_pong_status.buffer_b_status = BufferConsumeStatus::Committed;
            }
        }
    }

    /// Get the status of the specified ping-pong buffer
    pub fn buffer_status(&self, selector: PingPongSelector) -> BufferConsumeStatus {
        let channel = self.info.ch_num;
        #[allow(clippy::indexing_slicing)]
        let ping_pong_status = unsafe { &PING_PONG_STATUS[channel] };
        match selector {
            PingPongSelector::BufferA => ping_pong_status.buffer_a_status,
            PingPongSelector::BufferB => ping_pong_status.buffer_b_status,
        }
    }
}
