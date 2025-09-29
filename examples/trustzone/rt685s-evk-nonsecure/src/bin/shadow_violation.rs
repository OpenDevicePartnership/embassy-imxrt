#![no_std]
#![no_main]

use embassy_executor::Spawner;
use panic_probe as _;
use rtt_target::rprintln;

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let (_p, _cp) = nonsecure_app::init();

    // Shadow registers are protected using MPC over the aips_bridge1_mem_rule0 register.
    // In SAU this region is mapped to NonSecure.
    let ptr = 0x40130000 as *const u32;

    rprintln!("Trying to get CPU access to OTP shadow register memory (should fail with BusFault!)");
    let buf = unsafe { ptr.read_volatile() };
    rprintln!("buf: {:X?}", buf);

    rprintln!("!!! SHOULD NOT BE REACHABLE !!!");
}
