#![no_std]
#![no_main]

use embassy_executor::Spawner;
use panic_probe as _;
use rtt_target::rprintln;

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let (_p, _cp) = nonsecure_app::init();

    // Try to access the (undocumented) OTP peripheral address range.
    // Should be blocked using aips_bridge1_mem_rule0.
    let ptr = 0x40130824 as *const u32; // OTP_STATUS

    rprintln!("Trying to get CPU access to OTP peripheral register (should fail with BusFault!)");
    let buf = unsafe { ptr.read_volatile() };
    rprintln!("buf: {:X?}", buf);

    rprintln!("!!! SHOULD NOT BE REACHABLE !!!");
}
