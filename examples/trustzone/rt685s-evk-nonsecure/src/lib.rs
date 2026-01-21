#![no_std]

use core::mem::MaybeUninit;

use embassy_imxrt::interrupt::Interrupt;
use embassy_imxrt::pac::interrupt;
use embassy_imxrt::Peripherals;
use rtt_target::{rprintln, UpChannel};

#[repr(C)]
pub struct RttControlBlock {
    header: rtt_target::rtt::RttHeader,
    up_channels: [rtt_target::rtt::RttChannel; 1],
    down_channels: [rtt_target::rtt::RttChannel; 0],
}

#[used]
#[export_name = "_SEGGER_RTT"]
#[link_section = ".shared_rtt.header"]
pub static mut CONTROL_BLOCK: MaybeUninit<RttControlBlock> = MaybeUninit::uninit();

unsafe extern "C" {
    pub safe fn do_stuff_secure(num: u32) -> u32;
}

#[interrupt]
unsafe fn SECUREVIOLATION() {
    rprintln!("SECUREVIOLATION! (ns)");
    loop {
        cortex_m::asm::nop();
    }
}

pub fn init() -> (Peripherals, cortex_m::Peripherals) {
    unsafe { cortex_m::peripheral::NVIC::unmask(Interrupt::SECUREVIOLATION) };

    let p = embassy_imxrt::init(Default::default());
    let cp = cortex_m::Peripherals::take().unwrap();

    rtt_target::set_print_channel(unsafe { UpChannel::conjure(0) }.unwrap());
    rtt_target::rprintln!("Hello world");

    (p, cp)
}

/// Some location in secure memory that we should not be able to touch.
pub const SECURE_MEMORY: *mut u32 = 0x20000000 as *mut u32;
