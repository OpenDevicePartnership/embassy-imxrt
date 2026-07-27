#![no_std]
#![no_main]

use embassy_executor::Spawner;
use embassy_imxrt::pac::AhbSecureCtrl;
use panic_probe as _;
use rtt_target::rprintln;

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let (_p, _cp) = nonsecure_app::init();

    rprintln!("Trying to get CPU access to AHB bus security configuration (should fail with BusFault!)");
    // Is mapped to NonSecure memory in SAU, but PPC should block access.
    // Try out alias rule3 (+0x3000), as some configurations set that to non-secure
    // that catch writes as an hypervisor interrupt.
    let ahb_secure_ctrl = unsafe { &*AhbSecureCtrl::ptr().byte_add(0x3000) };
    rprintln!("buf: {:#010X}", ahb_secure_ctrl.misc_ctrl_reg().read().bits());

    rprintln!("!!! SHOULD NOT BE REACHABLE !!!");
}
