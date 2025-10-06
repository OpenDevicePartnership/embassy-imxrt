//! Low level FlexSPI peripheral access.

use crate::peripherals::FLEXSPI;
use crate::{Peri, pac};

/// Constants used by inline assembly.
#[cfg(target_arch = "arm")]
mod arm {
    /// The base address of the FlexSPI peripheral,
    pub const FLEXSPI_BASE: u32 = 0x40134000;

    /// The byte offset of the FlexSPI INTR register.
    pub const FLEXSPI_INTR: u16 = 0x14;

    /// The byte offset of the FlexSPI IPCMD register.
    pub const FLEXSPI_IPCMD: u16 = 0xB0;

    /// The byte offset of the FlexSPI IPCR0 register.
    pub const FLEXSPI_IPCR0: u16 = 0xA0;

    /// The byte offset of the FlexSPI IPCR1 register.
    pub const FLEXSPI_IPCR1: u16 = 0xA4;

    /// The byte offset of the FlexSPI IPRXFCR register.
    pub const FLEXSPI_IPRXFCR: u16 = 0xB8;

    /// The byte offset of the FlexSPI RFDR[0..32] registers.
    pub const FLEXSPI_RFDR: u16 = 0x100;

    /// The bitmask of the IPCMDDONE (command done) interrupt in the INTR register.
    pub const IPCMDDONE: u32 = 1 << 0;

    /// The bitmask of the IPCMDGE (grant timeout) interrupt in the INTR register.
    pub const IPCMDGE: u32 = 1 << 1;

    /// The bitmask of the IPCMDERR (command error) interrupt in the INTR register.
    pub const IPCMDERR: u32 = 1 << 4;

    /// The bitmask of the DATALEARNFAIL (data learn failed) interrupt in the INTR register.
    pub const DATALEARNFAIL: u32 = 1 << 7;

    /// The bitmask of the SEQTIMEOUT (sequence timeout) interrupt in the INTR register.
    pub const SEQTIMEOUT: u32 = 1 << 11;
}

#[cfg(target_arch = "arm")]
use self::arm::*;

/// Low level FlexSPI interface.
pub struct FlexSpi<'a> {
    /// The FlexSPI peripheral.
    #[allow(
        unused,
        reason = "This field represents unique access to the FlexSPI peripheral, but we don't actually need the object"
    )]
    flex_spi: Peri<'a, FLEXSPI>,
}

/// A flash port of the FlexSPI peripheral.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum FlashPort {
    /// Port A1.
    A1,

    /// Port A2.
    A2,

    /// Port B1.
    B1,

    /// Port B2.
    B2,
}

impl FlashPort {
    /// Get an array of all the flash ports, in the order they are mapped to memory.
    pub const fn all() -> [Self; 4] {
        [Self::A1, Self::A2, Self::B1, Self::B2]
    }
}

impl<'a> FlexSpi<'a> {
    /// Create a new FlexSPI peripheral.
    pub fn new(flex_spi: Peri<'a, FLEXSPI>) -> Self {
        Self { flex_spi }
    }

    /// Write a command sequence to the LUT.
    ///
    /// This function will overwrite one single LUT sequence,
    /// which consists of 4 words, where each word contains two instructions.
    ///
    /// See the [`mimxrt600-fcb`] crate for utilities to create LUT commnad sequences.
    ///
    /// # Safety
    /// Altering the LUT will potentiall change the behaviour of memory mapped flash access.
    /// You must ensure that memory mapped flash access still behaves properly.
    /// The easiest way to do this is to only modify LUT sequences that are NOT used for memory mapped flash access.
    pub unsafe fn write_lut_sequence(&mut self, index: u8, data: [u32; 4]) {
        let flexspi = unsafe { pac::Flexspi::steal() };
        let index: usize = index.into();

        // Unlock the LUT.
        unsafe { flexspi.lutkey().modify(|_, w| w.key().bits(0x5AF05AF0)) };
        flexspi.lutcr().write(|w| w.unlock().set_bit());

        // Write the LUT entries.
        unsafe {
            flexspi.lut(index * 4).write(|w| w.bits(data[0]));
            flexspi.lut(index * 4 + 1).write(|w| w.bits(data[1]));
            flexspi.lut(index * 4 + 2).write(|w| w.bits(data[2]));
            flexspi.lut(index * 4 + 3).write(|w| w.bits(data[3]));
        }

        // Lock the LUT.
        unsafe { flexspi.lutkey().modify(|_, w| w.key().bits(0x5AF05AF0)) };
        flexspi.lutcr().write(|w| w.lock().set_bit());
    }

    /// Read a LUT sequence by index.
    ///
    /// The index should be in the range 0..32.
    pub fn read_lut_sequence(&mut self, index: u8) -> [u32; 4] {
        let index: usize = index.into();
        let flexspi = unsafe { pac::Flexspi::steal() };
        [
            flexspi.lut(index * 4).read().bits(),
            flexspi.lut(index * 4 + 1).read().bits(),
            flexspi.lut(index * 4 + 2).read().bits(),
            flexspi.lut(index * 4 + 3).read().bits(),
        ]
    }

    /// Configure a command sequence from the LUT to run using the IP interface.
    ///
    /// This function not start the command sequence.
    ///
    /// This function clears all interrupt bits that indicate a previous command finished.
    ///
    /// # Safety
    /// You must ensure that no IP command is currently running on the FlexSPI peripheral when calling this.
    pub unsafe fn configure_command_sequence(
        &mut self,
        sequence: CommandSequence,
    ) -> Result<(), InvalidCommandSequence> {
        // Check if the sequence start and end fall within the valid range (0..32).
        if sequence.start >= 32 || sequence.count >= 32 || sequence.start + sequence.count >= 32 {
            return Err(InvalidCommandSequence {
                start: sequence.start,
                count: sequence.count,
            });
        }

        // TODO: Can we check if an IP command is already running or queued?

        let flex_spi = unsafe { pac::Flexspi::steal() };

        // Clear all interrupts that indicate a command finished.
        // Not sure who left them there, but it's not for the next command.
        let interrupts = flex_spi.intr().read();
        self.clear_command_finished_bits(&interrupts);

        // Configure the command in IPCR0 and IPCR1.
        let parallel = match sequence.parallel {
            false => pac::flexspi::ipcr1::Iparen::Iparen0,
            true => pac::flexspi::ipcr1::Iparen::Iparen1,
        };
        flex_spi.ipcr0().write(|w| unsafe { w.sfar().bits(sequence.address) });
        flex_spi.ipcr1().write(|w| unsafe {
            w.idatsz().bits(sequence.data_size);
            w.iseqid().bits(sequence.start);
            w.iseqnum().bits(sequence.count.saturating_sub(1));
            w.iparen().variant(parallel);
            w
        });
        Ok(())
    }

    /// Trigger a pre-configured command on the FlexSPI peripheral and wait for it to complete.
    ///
    /// The command must already have been configured in the IPCR0 and IPCR1 registers.
    /// This function will trigger the command and wait for it to finish.
    ///
    /// Part of this function is in the .data section so that it is located in RAM.
    /// This is important to prevent the CPU from trying to fetch instructions from FLASH
    /// while the command in running.
    ///
    /// Interrupts are disabled while waiting for the command to complete,
    /// to prevent interrupt handlers located in FLASH memory from executing.
    ///
    /// # Safety
    /// The command could potentially change the code of the currently running program.
    /// It is up to the caller to ensure that the command does not cause any undefined behaviour.
    ///
    /// Additionally, no IP command may currently be running on the FlexSPI peripheral.
    ///
    /// You must also ensure that the .data section is executable before calling this function.
    pub unsafe fn trigger_command_and_wait(&mut self) -> Result<pac::flexspi::intr::R, WaitCommandError> {
        let interrupts = critical_section::with(|_| unsafe { self._trigger_command_and_wait() });
        self.check_and_clear_command_interrupts(interrupts)
    }

    /// Implementation details for [`Self::trigger_command_and_wait()`].
    ///
    /// This part is located in RAM (the .data section) and implemented in inline assembly,
    /// to ensure that no instructions need to be fetched from FLASH while we keep the FlexSPI peripheral busy.
    ///
    /// TODO: Loading the instructions over the data bus works,
    /// but the end-user may need more control over the address of the function
    /// if they are using TrustZone.
    #[unsafe(link_section = ".data")]
    #[inline(never)]
    unsafe fn _trigger_command_and_wait(&mut self) -> pac::flexspi::intr::R {
        #[cfg(not(target_arch = "arm"))]
        {
            // SAFETY: pac::flexspi::intr::R is a transparent wrapper around a u32.
            unsafe { core::mem::transmute(0u32) }
        }
        #[cfg(target_arch = "arm")]
        {
            let mut interrupts: u32;

            unsafe {
                core::arch::asm! {
                    // Trigger command execution.
                    "mov {value}, 1",
                    "str {value}, [{flexspi_base}, #{FLEXSPI_IPCMD}]",

                    // Wait for the command to complete.
                    "2:",
                        "ldr {value}, [{flexspi_base}, #{FLEXSPI_INTR}]",
                        "tst {value}, {intr_mask}",
                        "beq 2b",

                    flexspi_base = in(reg) FLEXSPI_BASE,
                    FLEXSPI_IPCMD = const FLEXSPI_IPCMD,
                    FLEXSPI_INTR = const FLEXSPI_INTR,
                    intr_mask = in(reg) IPCMDDONE | IPCMDGE | IPCMDERR | DATALEARNFAIL | SEQTIMEOUT,
                    value = out(reg) interrupts,
                    options(nostack),
                }
            }

            // Safety: pac::flexspi::intr::R is a transparent wrapper around a u32.
            unsafe { core::mem::transmute(interrupts) }
        }
    }

    /// Trigger a pre-configured command on the FlexSPI peripheral, wait for it to complete and wait for the write-in-progress bit to go low.
    ///
    /// The command must already have been configured in the IPCR0 and IPCR1 registers.
    /// This function will trigger the command and wait for it to finish.
    ///
    /// Part of this function is in the .data section so that it is located in RAM.
    /// This is important to prevent the CPU from trying to fetch instructions from FLASH
    /// while the command in running.
    ///
    /// Interrupts are disabled while waiting for the command to complete,
    /// to prevent interrupt handlers located in FLASH memory from executing.
    ///
    /// NOTE: This function assumes that LUT sequence 2 is used to read the status register of the flash memory.
    ///
    /// # Safety
    /// The command could potentially change the code of the currently running program.
    /// It is up to the caller to ensure that the command does not cause any undefined behaviour.
    ///
    /// Additionally, no IP command may currently be running on the FlexSPI peripheral.
    ///
    /// You must also ensure that the .data section is executable before calling this function.
    pub unsafe fn trigger_command_and_wait_write(
        &mut self,
    ) -> Result<pac::flexspi::intr::R, super::nor_flash::WriteError> {
        let (stage, interrupts) = critical_section::with(|_| unsafe { self._trigger_command_and_wait_write() });
        self.check_and_clear_command_interrupts(interrupts).map_err(|e| {
            if stage == 0 {
                super::nor_flash::WriteError::Command(e.into())
            } else {
                super::nor_flash::WriteError::ReadStatus(super::nor_flash::ReadError::Command(e.into()))
            }
        })
    }

    /// Implementation details for [`Self::trigger_command_and_wait_write()`].
    ///
    /// This part is located in RAM (the .data section) and implemented in inline assembly,
    /// to ensure that no instructions need to be fetched from FLASH while we keep the FlexSPI peripheral busy.
    ///
    /// TODO: Loading the instructions over the data bus works,
    /// but the end-user may need more control over the address of the function
    /// if they are using TrustZone.
    #[unsafe(link_section = ".data")]
    #[inline(never)]
    unsafe fn _trigger_command_and_wait_write(&mut self) -> (u32, pac::flexspi::intr::R) {
        #[cfg(not(target_arch = "arm"))]
        {
            // SAFETY: pac::flexspi::intr::R is a transparent wrapper around a u32.
            unsafe { (0, core::mem::transmute(0u32)) }
        }
        #[cfg(target_arch = "arm")]
        {
            let mut interrupts: u32;
            let mut stage: u32;

            unsafe {
                core::arch::asm! {
                    // Trigger command execution.
                    "mov {value}, #1",
                    "str {value}, [{flexspi_base}, #{FLEXSPI_IPCMD}]",

                    // Wait for the command to complete.
                    "2:",
                        "ldr {interrupts}, [{flexspi_base}, #{FLEXSPI_INTR}]",

                        // Test for errors and exit with stage = 0.
                        "tst {interrupts}, {intr_mask_error}",
                        "bne 98f",

                        // Check if the command is done.
                        "tst {interrupts}, #{INTR_MASK_DONE}", // test for command done
                        "beq 2b",

                    // Configure read status command
                    "mov {value}, #0", // IPCR0 address
                    "str {value}, [{flexspi_base}, #{FLEXSPI_IPCR0}]",
                    "mov {value}, #{READ_STATUS_CR1_L}",
                    "movt {value}, #{READ_STATUS_CR1_H}",
                    "str {value}, [{flexspi_base}, #{FLEXSPI_IPCR1}]",

                    // Clear RX FIFO
                    "3:",
                        "ldr {value}, [{flexspi_base}, #{FLEXSPI_IPRXFCR}]",
                        "orr {value}, 1",
                        "str {value}, [{flexspi_base}, #{FLEXSPI_IPRXFCR}]",

                        // Clear CMDDONE interrupt flag and trigger command execution.
                        // No need to clear error flags, because we would have exited on errors.
                        "mov {value}, #{INTR_MASK_DONE}",
                        "str {value}, [{flexspi_base}, #{FLEXSPI_INTR}]",
                        "mov {value}, #1",
                        "str {value}, [{flexspi_base}, #{FLEXSPI_IPCMD}]",

                        // Wait for the command to complete.
                        "2:",
                            "ldr {interrupts}, [{flexspi_base}, #{FLEXSPI_INTR}]",

                            // Test for errors, and exit with correct stage number.
                            "tst {interrupts}, {intr_mask_error}",
                            "bne 99f",
                            "tst {interrupts}, #{INTR_MASK_DONE}", // test for command done
                            "beq 2b",

                        // Read the flash status.
                        "ldr {value}, [{flexspi_base}, #{FLEXSPI_RFDR}]",
                        "tst {value}, #{STATUS_WRITE_IN_PROGRESS}", // test the write-in-progress bit
                        "bne 3b",

                    "mov {value}, #2",
                    "b 100f",
                    "98:",
                    "mov {value}, #0",
                    "b 100f",
                    "99:",
                    "mov {value}, #1",

                    // Exit
                    "100:",

                    flexspi_base = in(reg) FLEXSPI_BASE,
                    FLEXSPI_INTR = const FLEXSPI_INTR,
                    FLEXSPI_IPCMD = const FLEXSPI_IPCMD,
                    FLEXSPI_IPRXFCR = const FLEXSPI_IPRXFCR,
                    FLEXSPI_IPCR0 = const FLEXSPI_IPCR0,
                    FLEXSPI_IPCR1 = const FLEXSPI_IPCR1,
                    FLEXSPI_RFDR = const FLEXSPI_RFDR,

                    READ_STATUS_CR1_L = const 4, // data size
                    READ_STATUS_CR1_H = const super::nor_flash::sequence::READ_STATUS, // sequence index

                    // TODO: This may be Macronix specific.
                    // Full flexibility may require a XOR + AND mask as input parameter to allow inverting and testing arbitrary bits.
                    STATUS_WRITE_IN_PROGRESS = const 2,

                    INTR_MASK_DONE = const IPCMDDONE,
                    intr_mask_error = in(reg) IPCMDGE | IPCMDERR | DATALEARNFAIL | SEQTIMEOUT,
                    interrupts = out(reg) interrupts,
                    value = out(reg) stage,
                    options(nostack),
                }
            }

            // SAFETY: pac::flexspi::intr::R is a wrapper around a u32.
            let interrupts = unsafe { core::mem::transmute::<u32, pac::flexspi::intr::R>(interrupts) };
            (stage, interrupts)
        }
    }

    /// Set the IP TX FIFO watermark to the given number of u64 entries.
    ///
    /// Note: Attempts to set the watermark level to zero will set the level to one 64 bit word instead.
    pub fn set_tx_fifo_watermark_u64_words(&mut self, num_u64: u8) {
        let flex_spi = unsafe { pac::Flexspi::steal() };
        let value = num_u64.saturating_sub(1);
        flex_spi.iptxfcr().modify(|_, w| unsafe { w.txwmrk().bits(value) });
    }

    /// Get the TX FIFO watermark level in `u64` words.
    pub fn get_tx_fifo_watermark_u64_words(&mut self) -> u8 {
        let flex_spi = unsafe { pac::Flexspi::steal() };
        flex_spi.iptxfcr().read().txwmrk().bits() + 1
    }

    /// Get the TX FIFO watermark level in bytes.
    pub fn get_tx_fifo_watermark_bytes(&mut self) -> usize {
        usize::from(self.get_tx_fifo_watermark_u64_words()) * 8
    }

    /// Set the IP RX FIFO watermark to the given number of u64 entries.
    ///
    /// Note: Attempts to set the watermark level to zero will set the level to one 64 bit word instead.
    pub fn set_rx_fifo_watermark_u64_words(&mut self, num_u64: u8) {
        let flex_spi = unsafe { pac::Flexspi::steal() };
        let value = num_u64.saturating_sub(1);
        flex_spi.iprxfcr().modify(|_, w| unsafe { w.rxwmrk().bits(value) });
    }

    /// Get the RX FIFO watermark level in `u64` words.
    pub fn get_rx_fifo_watermark_u64_words(&self) -> u8 {
        let flex_spi = unsafe { pac::Flexspi::steal() };
        flex_spi.iprxfcr().read().rxwmrk().bits() + 1
    }

    /// Get the RX FIFO watermark level in bytes.
    pub fn get_rx_fifo_watermark_bytes(&self) -> usize {
        usize::from(self.get_rx_fifo_watermark_u64_words()) * 8
    }

    /// Get the RX FIFO fill level in `u64` words.
    pub fn get_rx_fill_level_u64_words(&self) -> u8 {
        let flex_spi = unsafe { pac::Flexspi::steal() };
        flex_spi.iprxfsts().read().fill().bits()
    }

    /// Get the RX FIFO fill level in bytes.
    pub fn get_rx_fill_level_bytes(&self) -> usize {
        usize::from(self.get_rx_fill_level_u64_words()) * 8
    }

    /// Clear the entire RX fifo.
    pub fn clear_rx_fifo(&mut self) {
        let flex_spi = unsafe { pac::Flexspi::steal() };
        flex_spi.iprxfcr().modify(|_, w| w.clriprxf().set_bit());
    }

    /// Clear the entire TX fifo.
    pub fn clear_tx_fifo(&mut self) {
        let flex_spi = unsafe { pac::Flexspi::steal() };
        flex_spi.iptxfcr().modify(|_, w| w.clriptxf().set_bit());
    }

    /// Get the size in KiB (1024 bytes) of the flash connected to a specific flash port.
    #[inline]
    pub fn flash_size_kb(&self, port: FlashPort) -> u32 {
        let flex_spi = unsafe { pac::Flexspi::steal() };
        match port {
            FlashPort::A1 => flex_spi.flsha1cr0().read().flshsz().bits(),
            FlashPort::A2 => flex_spi.flsha2cr0().read().flshsz().bits(),
            FlashPort::B1 => flex_spi.flshb1cr0().read().flshsz().bits(),
            FlashPort::B2 => flex_spi.flshb2cr0().read().flshsz().bits(),
        }
    }

    /// Get the AHB read sequence for the flash connected to a specific port.
    ///
    /// This gives the command sequences in the LUT used for an AHB read.
    pub fn ahb_read_sequence(&self, port: FlashPort) -> core::ops::Range<u8> {
        let flex_spi = unsafe { pac::Flexspi::steal() };
        let flshcr3 = match port {
            FlashPort::A1 => flex_spi.flshcr2(0).read(),
            FlashPort::A2 => flex_spi.flshcr2(1).read(),
            FlashPort::B1 => flex_spi.flshcr2(2).read(),
            FlashPort::B2 => flex_spi.flshcr2(3).read(),
        };
        let start = flshcr3.ardseqid().bits();
        let len = flshcr3.ardseqnum().bits() + 1;
        start..start + len
    }

    /// Get the flash port used for a sepcific flash address.
    pub fn port_for_address(&self, address: u32) -> Option<FlashPort> {
        let mut offset = 0;
        for port in FlashPort::all() {
            let port_size = self.flash_size_kb(port) * 1024;
            if offset + port_size > address {
                return Some(port);
            }
            offset += port_size
        }
        None
    }

    /// Write data to the IP TX FIFO and mark it ready for sending.
    ///
    /// This copies data into the IP TX FIFO, up to the watermark level.
    pub fn fill_tx_fifo(&mut self, buffer: &[u8]) -> usize {
        // Limit buffer to fifo length.
        let watermark = self.get_tx_fifo_watermark_bytes();
        let copy_len = buffer.len().min(watermark);

        let flex_spi = unsafe { pac::Flexspi::steal() };

        unsafe {
            read_u8_write_u32_volatile(&buffer[..copy_len], flex_spi.tfdr(0).as_ptr().cast());
        }

        // Clear the TX watermark empty interrupt to transmit the data.
        flex_spi.intr().write(|w| w.iptxwe().clear_bit_by_one());

        // Report the number of bytes copied into the buffer.
        copy_len
    }

    /// Drain the RX fifo.
    ///
    /// Returns the number of bytes written into the buffer.
    ///
    /// You should ensure that either the FIFO is filled to the watermark level,
    /// or this is the final drain in a transfer.
    ///
    /// This function will always remove a full watermark of data from the FIFO,
    /// since that is the only way to remove any data from the FIFO.
    pub fn drain_rx_fifo(&mut self, buffer: &mut [u8]) -> usize {
        let flex_spi = unsafe { pac::Flexspi::steal() };

        // Get number of bytes to pop.
        let watermark = self.get_rx_fifo_watermark_bytes();
        let fill_level = self.get_rx_fill_level_bytes();
        let copy_len = buffer.len().min(fill_level).min(watermark);

        // Copy data from TX FIFO to buffer.
        unsafe {
            read_u32_volatile_write_u8(flex_spi.rfdr(0).as_ptr().cast(), &mut buffer[..copy_len]);
        }

        // Pop watermark data from the FIFO.
        flex_spi.intr().write(|w| w.iprxwa().clear_bit_by_one());

        // Return the number of bytes written to the buffer.
        copy_len
    }

    /// Check the interrupt register for command finished/error bits, and clear them.
    ///
    /// Performs one read of the interrupt register and clears only the set bits that indicate the command failed.
    fn check_and_clear_command_interrupts(
        &mut self,
        interrupts: pac::flexspi::intr::R,
    ) -> Result<pac::flexspi::intr::R, WaitCommandError> {
        let flex_spi = unsafe { pac::Flexspi::steal() };
        if interrupts.ipcmderr().bit() {
            // If the cmderr interrupt is set, read status1 before clearing the interrupt.
            let status1 = flex_spi.sts1().read();
            self.clear_command_finished_bits(&interrupts);
            Err(CommandFailed {
                sequence_index: status1.ipcmderrid().bits(),
                error_code: CommandErrorCode::from_pac(status1.ipcmderrcode()),
            }
            .into())
        } else if interrupts.seqtimeout().bit() {
            self.clear_command_finished_bits(&interrupts);
            Err(WaitCommandError::ExecutionTimeout)
        } else if interrupts.datalearnfail().bit() {
            self.clear_command_finished_bits(&interrupts);
            Err(WaitCommandError::DataLearnFailed)
        } else if interrupts.ipcmdge().bit() {
            self.clear_command_finished_bits(&interrupts);
            Err(WaitCommandError::GrantTimeout)
        } else {
            self.clear_command_finished_bits(&interrupts);
            Ok(interrupts)
        }
    }

    /// Clear all set interrupt bits that indicate a command finished (maybe with an error).
    ///
    /// Does not clear bits that are not set in the input.
    fn clear_command_finished_bits(&mut self, interrupts: &pac::flexspi::intr::R) {
        let flex_spi = unsafe { pac::Flexspi::steal() };
        flex_spi.intr().write(|w| {
            w.ipcmddone().bit(interrupts.ipcmddone().bit());
            w.ipcmderr().bit(interrupts.ipcmderr().bit());
            w.ipcmdge().bit(interrupts.ipcmdge().bit());
            w.datalearnfail().bit(interrupts.datalearnfail().bit());
            w.seqtimeout().bit(interrupts.seqtimeout().bit());
            w
        });
    }
}

/// A command sequence to run on the FlexSPI peripheral.
///
/// Note that this struct does not encode an actual command to send to the flash.
/// It points to pre-defined commands in the FlexSPI LUT (lookup table).
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct CommandSequence {
    /// The start index in the LUT of the sequence to execute.
    pub start: u8,

    /// The number of sequences to run.
    ///
    /// If more than one, sequences will be run from the LUT in order, starting at [`Self::sequence_start`].
    /// A value of 0 is interpreted the same as 1: run a single sequence.
    pub count: u8,

    /// The physical flash address for the command sequence.
    ///
    /// This is used by the `RADDR` and `CADDR` instructions.
    pub address: u32,

    /// The data size for the instruction.
    ///
    /// This is used by the `DATSZ` instruction.
    pub data_size: u16,

    /// Enable parallel mode for this command sequence.
    ///
    /// In parallel mode, instructions are sent to two connected flash memories.
    /// Refer to the FlexSPI documentation in the RT6xx user manual for details about parallel mode.
    pub parallel: bool,
}

/// Error that can occur while waiting for a command to complete or make progress.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum WaitCommandError {
    /// The arbiter went into idle state, but the command did not finish.
    ArbiterIdle,

    /// The command failed with an error.
    CommandFailed(CommandFailed),

    /// Timeout waiting for the arbiter to execute the command.
    GrantTimeout,

    /// The command sequence contained a data learn instruction that failed.
    DataLearnFailed,

    /// Timeout while executing the command.
    ExecutionTimeout,
}

/// The FlexSPI peripheral failed to execute a command.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct CommandFailed {
    /// The index of the sequence in the FlexSPI LUT that caused the error.
    pub sequence_index: u8,

    /// The error code reported by the flash.
    pub error_code: CommandErrorCode,
}

impl From<CommandFailed> for WaitCommandError {
    fn from(value: CommandFailed) -> Self {
        Self::CommandFailed(value)
    }
}

/// Error code reported by the FlexSPI peripheral when it fails to execute a command sequence.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[repr(u8)]
pub enum CommandErrorCode {
    /// No error occured.
    NoError = 0b0000,

    /// Unknown error code: 1.
    Unknown1 = 0b0001,

    /// The sequence contains a JUMP_ON_CS instruction, which is not allowed for IP commands.
    IllegalJumpOnCs = 0b0010,

    /// The sequence contains an unknown opcode.
    UnknownOpcode = 0b0011,

    /// There was a DUMMY_SDR or DUMMY_RWDS_SDR instruction in a DDR sequence.
    DummySdrInDdrSequence = 0b0100,

    /// There was a DUMMY_DDR or DUMMY_RWDS_DDR instruction in a SDR sequence.
    DummyDdrInSdrSequence = 0b0101,

    /// The start address exceeds the total flash capacity.
    StartAddressOutOfBounds = 0b0110,

    /// Unknown error code: 7.
    Unknown7 = 0b0111,

    /// Unknown error code: 8.
    Unknown8 = 0b1000,

    /// Unknown error code: 9.
    Unknown9 = 0b1001,

    /// Unknown error code: 10.
    Unknown10 = 0b1010,

    /// Unknown error code: 11.
    Unknown11 = 0b1011,

    /// Unknown error code: 12.
    Unknown12 = 0b1100,

    /// Unknown error code: 13.
    Unknown13 = 0b1101,

    /// The execution of the sequence timed out.
    SequenceTimeout = 0b1110,

    /// The access crossed a flash boundary.
    AccessCrossedFlashBoundary = 0b1111,
}

impl CommandErrorCode {
    fn from_pac(error_code: pac::flexspi::sts1::IpcmderrcodeR) -> Self {
        let code = error_code.bits();
        match code & 0xF {
            0 => Self::NoError,
            1 => Self::Unknown1,
            2 => Self::IllegalJumpOnCs,
            3 => Self::UnknownOpcode,
            4 => Self::DummySdrInDdrSequence,
            5 => Self::DummyDdrInSdrSequence,
            6 => Self::StartAddressOutOfBounds,
            7 => Self::Unknown7,
            8 => Self::Unknown8,
            9 => Self::Unknown9,
            10 => Self::Unknown10,
            11 => Self::Unknown11,
            12 => Self::Unknown12,
            13 => Self::Unknown13,
            14 => Self::SequenceTimeout,
            15 => Self::AccessCrossedFlashBoundary,
            _ => unsafe { core::hint::unreachable_unchecked() },
        }
    }
}

/// Error that can occur while waiting for space in the TX FIFO.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum WaitTxReadyError {
    /// The command failed with an error.
    CommandError(WaitCommandError),

    /// The command finished while we were waiting for space in the TX FIFO.
    CommandFinished,
}

impl From<WaitCommandError> for WaitTxReadyError {
    fn from(value: WaitCommandError) -> Self {
        Self::CommandError(value)
    }
}

/// Error executing a command sequence.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct InvalidCommandSequence {
    /// The requested sequence start index.
    pub start: u8,

    /// The requested number of sequences.
    pub count: u8,
}

/// Copy bytes from `source` to `dest`.
///
/// The data is read from the source as bytes,
/// and written to the destination as [`u32`] words with a volatile write.
///
/// If the number of bytes is not a multiple of 4,
/// the last word will be padded with zeros in the most significant bytes.
///
/// # Safety:
/// The destination pointer must point to an region of writable memory properly aligned for `u32` access.
/// The size in bytes of the region must be at-least `source.len()` rounded up to a multiple of 4 bytes.
/// There may be no reference in existence to the destination region.
/// This also means that the destination may not overlap with the source.
unsafe fn read_u8_write_u32_volatile(source: &[u8], dest: *mut u32) {
    unsafe {
        let word_count = source.len() / 4;
        let remainder = source.len() % 4;

        // Write whole words.
        for i in 0..word_count {
            let source: &[u8; 4] = &*source[i * 4..][..4].as_ptr().cast();
            let word = u32::from_ne_bytes(*source);
            dest.add(i).write_volatile(word);
        }

        // Write remainder, zero padded.
        if remainder > 0 {
            let mut word = [0; 4];
            word[..remainder].copy_from_slice(&source[word_count * 4..][..remainder]);
            let word = u32::from_ne_bytes(word);
            dest.add(word_count).write_volatile(word);
        }
    }
}

/// Copy bytes from `source` to `dest`.
///
/// The data is read as [`u32`] words with a volatile read,
/// and written to the destination as [`u8`].
///
/// If the number of bytes is not a multiple of 4,
/// the unneeded most significant bytes of the last word will be discarded.
///
/// # Safety:
/// The source pointer must point to a readable memory region properly aligned for `u32` access.
/// The size in bytes of the region must be at least `dest.len()` rounded up to a multiple of 4.
/// The source region may not overlap with the `dest` slice.
unsafe fn read_u32_volatile_write_u8(source: *const u32, dest: &mut [u8]) {
    unsafe {
        let word_count = dest.len() / 4;
        let remainder = dest.len() % 4;

        // Read whole words.
        for i in 0..word_count {
            let dest: &mut [u8; 4] = &mut *dest[i * 4..].as_mut_ptr().cast();
            let source = source.add(i);
            let word = source.read_volatile();
            *dest = word.to_ne_bytes();
        }

        // Read last word and truncate.
        if remainder > 0 {
            let word = source.add(word_count).read_volatile();
            let word = word.to_ne_bytes();
            dest[word_count * 4..].copy_from_slice(&word[..remainder]);
        }
    }
}

#[cfg(test)]
mod tests {
    use core::cell::Cell;

    use super::*;

    #[test]
    fn test_read_u8_write_u32_volatile() {
        {
            let source = [1];
            let dest = Cell::new(0xCAFECAFE);
            unsafe { read_u8_write_u32_volatile(&source, dest.as_ptr()) };
            assert!(dest.get().to_le_bytes() == [0x01, 0x00, 0x00, 0x00]);
        }

        {
            let source = [1, 2];
            let dest = Cell::new(0xCAFECAFE);
            unsafe { read_u8_write_u32_volatile(&source, dest.as_ptr()) };
            assert!(dest.get().to_le_bytes() == [0x01, 0x02, 0x00, 0x00]);
        }
        {
            let source = [1, 2, 3];
            let dest = Cell::new(0xCAFECAFE);
            unsafe { read_u8_write_u32_volatile(&source, dest.as_ptr()) };
            assert!(dest.get().to_le_bytes() == [0x01, 0x02, 0x03, 0x00]);
        }
        {
            let source = [1, 2, 3, 4];
            let dest = Cell::new(0xCAFECAFE);
            unsafe { read_u8_write_u32_volatile(&source, dest.as_ptr()) };
            assert!(dest.get().to_le_bytes() == [0x01, 0x02, 0x03, 0x04]);
        }
        {
            let source = [1, 2, 3, 4, 5];
            let mut dest = Cell::new([0xCAFECAFEu32; 2]);
            unsafe { read_u8_write_u32_volatile(&source, dest.get_mut().as_mut_ptr()) };
            assert!(dest.get()[0].to_le_bytes() == [0x01, 0x02, 0x03, 0x04]);
            assert!(dest.get()[1].to_le_bytes() == [0x05, 0x00, 0x00, 0x00]);
        }
        {
            let source = [1, 2, 3, 4, 5, 6, 7];
            let mut dest = Cell::new([0xCAFECAFEu32; 2]);
            unsafe { read_u8_write_u32_volatile(&source, dest.get_mut().as_mut_ptr()) };
            assert!(dest.get()[0].to_le_bytes() == [0x01, 0x02, 0x03, 0x04]);
            assert!(dest.get()[1].to_le_bytes() == [0x05, 0x06, 0x07, 0x00]);
        }
        {
            let source = [1, 2, 3, 4, 5, 6, 7, 8];
            let mut dest = Cell::new([0xCAFECAFEu32; 2]);
            unsafe { read_u8_write_u32_volatile(&source, dest.get_mut().as_mut_ptr()) };
            assert!(dest.get()[0].to_le_bytes() == [0x01, 0x02, 0x03, 0x04]);
            assert!(dest.get()[1].to_le_bytes() == [0x05, 0x06, 0x07, 0x08]);
        }
    }

    #[test]
    fn test_read_u32_volatile_write_u8() {
        let source = [
            u32::from_ne_bytes([0x01, 0x23, 0x45, 0x67]),
            u32::from_ne_bytes([0x89, 0xAB, 0xCD, 0xEF]),
        ];

        {
            let mut dest = [0xFF];
            unsafe {
                read_u32_volatile_write_u8(source.as_ptr(), &mut dest);
            }
            assert!(dest == [0x01]);
        }
        {
            let mut dest = [0xFF; 2];
            unsafe {
                read_u32_volatile_write_u8(source.as_ptr(), &mut dest);
            }
            assert!(dest == [0x01, 0x23]);
        }
        {
            let mut dest = [0xFF; 3];
            unsafe {
                read_u32_volatile_write_u8(source.as_ptr(), &mut dest);
            }
            assert!(dest == [0x01, 0x23, 0x45]);
        }
        {
            let mut dest = [0xFF; 4];
            unsafe {
                read_u32_volatile_write_u8(source.as_ptr(), &mut dest);
            }
            assert!(dest == [0x01, 0x23, 0x45, 0x67]);
        }
        {
            let mut dest = [0xFF; 5];
            unsafe {
                read_u32_volatile_write_u8(source.as_ptr(), &mut dest);
            }
            assert!(dest == [0x01, 0x23, 0x45, 0x67, 0x89]);
        }
        {
            let mut dest = [0xFF; 6];
            unsafe {
                read_u32_volatile_write_u8(source.as_ptr(), &mut dest);
            }
            assert!(dest == [0x01, 0x23, 0x45, 0x67, 0x89, 0xAB]);
        }
        {
            let mut dest = [0xFF; 7];
            unsafe {
                read_u32_volatile_write_u8(source.as_ptr(), &mut dest);
            }
            assert!(dest == [0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD]);
        }
        {
            let mut dest = [0xFF; 8];
            unsafe {
                read_u32_volatile_write_u8(source.as_ptr(), &mut dest);
            }
            assert!(dest == [0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF]);
        }
    }
}
