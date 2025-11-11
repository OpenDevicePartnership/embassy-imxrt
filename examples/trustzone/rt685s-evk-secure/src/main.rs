#![no_std]
#![no_main]
#![feature(abi_cmse_nonsecure_call)]
#![feature(cmse_nonsecure_entry)]

use core::ops::{Range, RangeInclusive};
use core::panic::PanicInfo;
use core::sync::atomic::AtomicU32;

use cortex_m::peripheral::sau::{SauRegion, SauRegionAttribute};
use cortex_m::peripheral::SCB;
use mimxrt600_fcb::FlexSPIFlashConfigurationBlock;
use mimxrt685s_pac::ahb_secure_ctrl::ram00_rule::Rule0;
use mimxrt685s_pac::ahb_secure_ctrl::{self};
use mimxrt685s_pac::{interrupt, AhbSecureCtrl, Sau, ScnScb};
use rtt_target::rprintln;
use rtt_target::ChannelMode::NoBlockSkip;

// auto-generated version information from Cargo.toml
include!(concat!(env!("OUT_DIR"), "/biv.rs"));

#[link_section = ".otfad"]
#[used]
static OTFAD: [u8; 256] = [0; 256];

#[rustfmt::skip]
#[link_section = ".fcb"]
#[used]
static FCB: FlexSPIFlashConfigurationBlock = FlexSPIFlashConfigurationBlock::build();

#[link_section = ".keystore"]
#[used]
static KEYSTORE: [u8; 2048] = [0; 2048];

const NONSECURE_START_FLASH: *const [u32; 2] = 0x0804_0000 as *const [u32; 2];
const NONSECURE_END_FLASH: u32 = 0x08FF_FFFF;
const SECURE_START_RAM: u32 = 0x2000_0000;
const NONSECURE_START_RAM: u32 = 0x2000_1000;
const NONSECURE_END_RAM: u32 = 0x2FFF_FFFF;
const NONSECURE_START_PERIPHERALS: u32 = 0x4000_0000;
const NONSECURE_END_PERIPHERALS: u32 = 0x4FFF_FFFF;

extern "Rust" {
    static __veneer_base: ();
    static __veneer_limit: ();
}

const VTOR_NS: *mut u32 = 0xE002ED08 as *mut u32;

fn test_security(addr: *mut u32) {
    fn opt_if<T>(val: bool, some: T) -> Option<T> {
        if val {
            Some(some)
        } else {
            None
        }
    }

    let res = cortex_m::asm::ttat(addr);
    let mrvalid = res >> 16 & 0b1 == 0b1;
    let srvalid = res >> 17 & 0b1 == 0b1;
    let irvalid = res >> 23 & 0b1 == 0b1;
    let mregion = opt_if(mrvalid, res & 0xf);
    let sregion = opt_if(srvalid, res >> 8 & 0xf);
    let iregion = opt_if(irvalid, res >> 24 & 0xf);
    let r = res >> 18 & 0b1 == 0b1;
    let rw = res >> 19 & 0b1 == 0b1;
    let s = res >> 22 & 0b1 == 0b1;
    rprintln!(
        "ttat({:#010X}): {:#010X} (mregion: {:?}, sregion {:?}, iregion {:?}, r {}, rw {}, s {})",
        addr as u32,
        res,
        mregion,
        sregion,
        iregion,
        r,
        rw,
        s
    );
    unsafe { rtt_target::UpChannel::conjure(0) }.unwrap().flush();
}

// A common failure mode when configuring these security registers is that the changes are ignored,
// without ever throwing a fault or an exception.
// Hence we need to check if the changes persisted.
macro_rules! reg_write_checked {
    ($reg:expr, $f:expr) => {{
        let v = $reg.write($f);
        assert_eq!(v, $reg.read().bits());
    }};
}

macro_rules! reg_modify_checked {
    ($reg:expr, $f:expr) => {{
        let v = $reg.modify($f);
        assert_eq!(v, $reg.read().bits());
    }};
}

#[cortex_m_rt::entry]
fn main() -> ! {
    let channels = rtt_target::rtt_init! {
        up: {
            0: { // channel number
                size: 1024, // buffer size in bytes
                mode: NoBlockSkip, // mode (optional, default: NoBlockSkip, see enum ChannelMode)
                name: "Terminal", // name (optional, default: no name)
                section: ".shared_rtt.buffer" // Buffer linker section (optional, default: no section)
            }
        }
        section_cb: ".shared_rtt.header" // Control block linker section (optional, default: no section)
    };
    rtt_target::set_print_channel(channels.up.0);

    let mut cp = cortex_m::Peripherals::take().unwrap();
    let _dp = mimxrt685s_pac::Peripherals::take().unwrap();

    unsafe {
        let [nonsecure_sp, nonsecure_reset] = NONSECURE_START_FLASH.read_volatile();

        rprintln!("Running. SP: {:#010X}, RV: {:#010X}", nonsecure_sp, nonsecure_reset);

        if nonsecure_sp == u32::MAX || nonsecure_reset == u32::MAX {
            loop {
                cortex_m::asm::nop();
            }
        }

        rprintln!("Setting up regions");
        rprintln!(
            "Veneers: {:#010X} .. {:#010X}",
            &raw const __veneer_base as u32,
            &raw const __veneer_limit as u32
        );

        let ahb_secure_ctrl = &*(AhbSecureCtrl::ptr().byte_add(0x1000_0000));

        // Set all regions not used by this program to non-secure.
        // This only concerns the CM33 access, not any of the other bus masters like DMA
        // All memory regions without a SAU region are 'Secure'.
        rprintln!("Set SAU regions");
        let sau = &*Sau::ptr();

        sau.ctrl().write(|w| w.enable().disabled());

        let regions: [(RangeInclusive<u32>, SauRegionAttribute); 4] = [
            (
                &raw const __veneer_base as u32..=&raw const __veneer_limit as u32 - 1,
                SauRegionAttribute::NonSecureCallable,
            ),
            (
                NONSECURE_START_FLASH as u32..=NONSECURE_END_FLASH,
                SauRegionAttribute::NonSecure,
            ),
            (NONSECURE_START_RAM..=NONSECURE_END_RAM, SauRegionAttribute::NonSecure),
            (
                NONSECURE_START_PERIPHERALS..=NONSECURE_END_PERIPHERALS,
                SauRegionAttribute::NonSecure,
            ),
        ];

        for (region_i, (range, attribute)) in regions.into_iter().enumerate() {
            rprintln!(
                "SAU region {}: {:#010X}..={:#010X} to {:?}",
                region_i,
                range.start(),
                range.end(),
                attribute
            );
            cp.SAU
                .set_region(
                    region_i as u8,
                    SauRegion {
                        base_address: *range.start(),
                        limit_address: *range.end(),
                        attribute,
                    },
                )
                .unwrap();
        }

        // Enable SAU, marking appropriate regions as NonSecure and NonSecureCallable.
        rprintln!("Enabling SAU");
        cp.SAU.enable();

        rprintln!("Set ROM to secure");
        for rom_mem in ahb_secure_ctrl.rom_mem_rule_iter() {
            reg_write_checked!(rom_mem, |w| {
                w.rule0().secure_priv_user_allowed();
                w.rule1().secure_priv_user_allowed();
                w.rule2().secure_priv_user_allowed();
                w.rule3().secure_priv_user_allowed();
                w.rule4().secure_priv_user_allowed();
                w.rule5().secure_priv_user_allowed();
                w.rule6().secure_priv_user_allowed();
                w.rule7().secure_priv_user_allowed()
            });
        }

        rprintln!("Set secure RAM to secure");
        set_ram_secure(SECURE_START_RAM..NONSECURE_START_RAM, ahb_secure_ctrl);

        rprintln!(
            "Set FlexSPI memory to secure (up to {:X}) and the rest to non-secure",
            NONSECURE_START_FLASH as u32
        );
        reg_write_checked!(ahb_secure_ctrl.flexspi0_region0_rule(0), |w| w.bits(0x00000003));
        reg_write_checked!(ahb_secure_ctrl.flexspi0_region0_rule(1), |w| w.bits(0));
        reg_write_checked!(ahb_secure_ctrl.flexspi0_region0_rule(2), |w| w.bits(0));
        reg_write_checked!(ahb_secure_ctrl.flexspi0_region0_rule(3), |w| w.bits(0));

        reg_write_checked!(ahb_secure_ctrl.flexspi0_region1_rule0(), |w| w.bits(0));
        reg_write_checked!(ahb_secure_ctrl.flexspi0_region2_rule0(), |w| w.bits(0));
        reg_write_checked!(ahb_secure_ctrl.flexspi0_region3_rule0(), |w| w.bits(0));
        reg_write_checked!(ahb_secure_ctrl.flexspi0_region4_rule0(), |w| w.bits(0));

        rprintln!("Set all peripherals to non-secure (except for OTP)");
        reg_write_checked!(ahb_secure_ctrl.pif_hifi4_x_mem_rule0(), |w| w.bits(0));
        reg_write_checked!(ahb_secure_ctrl.apb_grp0_mem_rule0(), |w| w.bits(0));
        reg_write_checked!(ahb_secure_ctrl.apb_grp0_mem_rule1(), |w| w.bits(0));
        reg_write_checked!(ahb_secure_ctrl.apb_grp1_mem_rule0(), |w| w.bits(0));
        reg_write_checked!(ahb_secure_ctrl.apb_grp1_mem_rule1(), |w| w.bits(0));
        reg_write_checked!(ahb_secure_ctrl.apb_grp1_mem_rule2(), |w| w.bits(0));
        reg_write_checked!(ahb_secure_ctrl.ahb_periph0_slave_rule0(), |w| w.bits(0));
        reg_write_checked!(ahb_secure_ctrl.aips_bridge0_mem_rule0(), |w| w.bits(0));
        reg_write_checked!(ahb_secure_ctrl.ahb_periph1_slave_rule0(), |w| w.bits(0));
        reg_write_checked!(ahb_secure_ctrl.aips_bridge1_mem_rule0(), |w| {
            w.otp_rule0()
                .bits(0b11)
                .otp_rule1()
                .bits(0b11)
                .otp_rule2()
                .bits(0b11)
                .otp_rule3()
                .bits(0b11)
        });
        reg_write_checked!(ahb_secure_ctrl.aips_bridge1_mem_rule1(), |w| w.bits(0));
        reg_write_checked!(ahb_secure_ctrl.ahb_periph2_slave_rule0(), |w| w.bits(0));
        reg_write_checked!(ahb_secure_ctrl.ahb_periph3_slave_rule0(), |w| w.bits(0));

        rprintln!("Setting all bus masters to non-secure");
        reg_write_checked!(ahb_secure_ctrl.master_sec_level(), |w| {
            w.dma0_sec()
                .enum_ns_np()
                .dma1_sec()
                .enum_ns_np()
                .dsp_sec()
                .enum_ns_np()
                .powerquad_sec()
                .enum_ns_np()
                .sdio0_sec()
                .enum_ns_np()
                .sdio1_sec()
                .enum_ns_np()
                .master_sec_level_lock()
                .blocked()
        });
        reg_write_checked!(ahb_secure_ctrl.master_sec_level_anti_pol(), |w| {
            w.dma0_sec()
                .enum_ns_np()
                .dma1_sec()
                .enum_ns_np()
                .dsp_sec()
                .enum_ns_np()
                .powerquad_sec()
                .enum_ns_np()
                .sdio0_sec()
                .enum_ns_np()
                .sdio1_sec()
                .enum_ns_np()
                .master_sec_level_anti_pole_lock()
                .blocked()
        });

        rprintln!("Configure CM33");
        // [3]  Disable SYSRESETREQ from non-secure.
        // [13] Use secure BusFault, HardFault and NMI.
        // [14] Priority ranges of secure and non-secure exceptions are identical.
        cp.SCB
            .aircr
            .write((cp.SCB.aircr.read() & (0xffff ^ (1 << 3 | 1 << 13 | 1 << 14))) | 0x005FA0000);

        // [3] Set secure mode to normal sleep (contrary to deep sleep)
        cp.SCB.scr.modify(|w| w & 0x0FFFFFFF7);

        // [17] Enable Bus Fault
        // [18] Enable Usage Fault
        // [19] Enable Secure fault
        cp.SCB.shcsr.modify(|w| w | (1 << 19 | 1 << 18 | 1 << 17));

        // [0]  Enable non-secure access to CP0
        // [1]  Enable non-secure access to CP1
        // [10] Enable non-secure access to CP10 - float-point extension
        // [11] Enable non-secure access to CP11 - float-point extension (must be set iff CP10 is set)
        let nsacr = 0xE000ED8C as *mut u32;
        nsacr.write_volatile(0x00000C03);

        // Unset all Coprocessor Power Control power down bits, enabling the FPU.
        let scn_scb = &*ScnScb::ptr();
        scn_scb.cppwr().write(|w| w.bits(0));

        rprintln!("Masking DSP and GPIO");
        // Lock all security configrations for the DPS and the GPIO masks.
        reg_write_checked!(ahb_secure_ctrl.sec_mask_lock(), |w| {
            w.sec_dsp_int_lock()
                .blocked()
                .sec_gpio_mask0_lock()
                .blocked()
                .sec_gpio_mask1_lock()
                .blocked()
                .sec_gpio_mask2_lock()
                .blocked()
                .sec_gpio_mask3_lock()
                .blocked()
                .sec_gpio_mask4_lock()
                .blocked()
                .sec_gpio_mask5_lock()
                .blocked()
                .sec_gpio_mask6_lock()
                .blocked()
                .sec_gpio_mask7_lock()
                .blocked()
        });

        rprintln!("Enabling AHB bus checks");
        reg_modify_checked!(ahb_secure_ctrl.misc_ctrl_reg(), |_, w| {
            w.enable_ns_priv_check()
                .disable()
                .enable_secure_checking()
                .enable()
                .enable_s_priv_check()
                .disable()
        });
        reg_modify_checked!(ahb_secure_ctrl.misc_ctrl_dp_reg(), |_, w| {
            w.enable_ns_priv_check()
                .disable()
                .enable_secure_checking()
                .enable()
                .enable_s_priv_check()
                .disable()
        });

        rprintln!("Configure security ctrl aliases to secure");
        reg_write_checked!(ahb_secure_ctrl.security_ctrl_mem_rule0(), |w| {
            w.rule0()
                .bits(0b11)
                .rule1()
                .bits(0b11)
                .rule2()
                .bits(0b11)
                .rule3()
                .bits(0b11)
        });

        rprintln!("Enabling SAU");
        cp.SAU.enable();

        rprintln!("Lock secure MPU, VTOR and SAU");
        reg_modify_checked!(ahb_secure_ctrl.cm33_lock_reg(), |_, w| {
            w.lock_s_mpu()
                .blocked()
                .lock_s_vtor()
                .blocked()
                .lock_sau()
                .blocked()
                .cm33_lock_reg_lock()
                .blocked()
        });

        rprintln!("Lock all security CTRL");
        reg_modify_checked!(ahb_secure_ctrl.misc_ctrl_reg(), |_, w| w.write_lock().restricted());
        // Cannot set DP register as we have just locked the entire block.
        // reg_modify_checked!(ahb_secure_ctrl.misc_ctrl_dp_reg(), |_, w| w.write_lock().restricted());

        // Set the nonsecure VTOR.
        VTOR_NS.write_volatile(NONSECURE_START_FLASH as u32);

        // Set all interrupts to non-secure.
        for itns in &cp.NVIC.itns {
            itns.write(u32::MAX);
        }

        // Set the non-secure stack pointer.
        cortex_m::register::msp::write_ns(nonsecure_sp);

        // Make sure the new settings take effect immediately:
        // https://developer.arm.com/documentation/100235/0100/The-Cortex-M33-Peripherals/Security-Attribution-and--Memory-Protection/Updating-protected-memory-regions
        cortex_m::asm::dsb();
        cortex_m::asm::isb();

        test_security(&raw const __veneer_base as u32 as *mut u32);
        test_security(nonsecure_reset as *mut u32);

        rprintln!("Jumping");

        // Create the right function pointer to the reset vector.
        let nonsecure_reset =
            core::mem::transmute::<*const u32, extern "cmse-nonsecure-call" fn()>(nonsecure_reset as *const u32);

        // Jump.
        nonsecure_reset();

        cortex_m::asm::udf();
    }
}

fn set_ram_secure(mut region: Range<u32>, ahb_secure_ctrl: &ahb_secure_ctrl::RegisterBlock) {
    let address_to_block = |address: u32| {
        const BLOCK_SIZE_TABLE: &[(u32, u32, u32)] = &[
            (
                0x2010_0000,
                8192,
                0x4_0000 / 0x400 + 0x4_0000 / 0x800 + 0x8_0000 / 0x1000,
            ),
            (0x2008_0000, 4096, 0x4_0000 / 0x400 + 0x4_0000 / 0x800),
            (0x2004_0000, 2048, 0x4_0000 / 0x400),
            (0x2000_0000, 1024, 0),
        ];

        let (block_start, block_size, previous_blocks) = BLOCK_SIZE_TABLE
            .iter()
            .find(|(block_address, _, _)| address >= *block_address)
            .unwrap();

        (
            *previous_blocks + (address - *block_start) / *block_size,
            *block_start + (address - *block_start) / *block_size * *block_size,
            *block_size,
        )
    };

    // Make sure the end of the range is at a boundary
    let (_, block_start, _) = address_to_block(region.end);
    assert_eq!(region.end, block_start);

    while !region.is_empty() {
        let (block_index, block_start, block_size) = address_to_block(region.start);
        assert_eq!(region.start, block_start);

        let register_index = block_index / 8;
        let rule_index = block_index % 8;

        let base_ptr = ahb_secure_ctrl.ram00_rule(0).as_ptr();

        rprintln!(
            "Ram region {:#010X}..={:#010X} to secure ({}, {})",
            block_start,
            block_start + block_size - 1,
            register_index,
            rule_index
        );

        unsafe {
            let target_register = base_ptr.add(register_index as usize);
            let current_val = target_register.read_volatile();
            target_register.write_volatile(
                current_val & !(0b11 << (rule_index * 4)) | ((Rule0::SecurePrivUserAllowed as u32) << (rule_index * 4)),
            );
        }

        region.start += block_size;
    }
}

#[cortex_m_rt::exception(trampoline = false)]
unsafe fn HardFault() -> ! {
    let scb = &*SCB::PTR;
    rprintln!("HardFault! (S) - SHCSR: {:#010X}", scb.shcsr.read());

    loop {
        cortex_m::asm::nop();
    }
}

#[cortex_m_rt::exception]
unsafe fn SecureFault() -> ! {
    let sau = &*cortex_m::peripheral::SAU::PTR;
    rprintln!(
        "SecureFault! (S) - SFSR: {:#010X}, SFAR: {:#010X}",
        sau.sfsr.read().0,
        sau.sfar.read().0
    );
    loop {
        cortex_m::asm::nop();
    }
}

#[cortex_m_rt::exception]
unsafe fn UsageFault() -> ! {
    rprintln!("UsageFault! (S)");
    loop {
        cortex_m::asm::nop();
    }
}

#[cortex_m_rt::exception]
unsafe fn BusFault() -> ! {
    let scb = &*SCB::PTR;
    rprintln!(
        "BusFault! (S) - CFSR: {:#010X}, BFAR: {:#010X}",
        scb.cfsr.read(),
        scb.bfar.read()
    );
    loop {
        cortex_m::asm::nop();
    }
}

#[interrupt]
unsafe fn SECUREVIOLATION() {
    rprintln!("SECUREVIOLATION! (S)");
    loop {
        cortex_m::asm::nop();
    }
}

#[panic_handler]
fn panic(i: &PanicInfo) -> ! {
    rprintln!("{}", i);
    cortex_m::asm::udf();
}

static COUNTER: AtomicU32 = AtomicU32::new(0);

#[unsafe(no_mangle)]
extern "cmse-nonsecure-entry" fn do_stuff_secure(num: u32) -> u32 {
    let old = COUNTER.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
    num * 2 + old
}
