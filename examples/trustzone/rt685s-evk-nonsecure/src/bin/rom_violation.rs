#![no_std]
#![no_main]

use embassy_executor::Spawner;
use panic_probe as _;
use rtt_target::rprintln;

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let (_p, _cp) = nonsecure_app::init();

    // ROM region for OTP driver.
    // SAU does not have this region configured as NonSecure,
    // and we have configured the MPC to emit a BusFault.
    let ptr = 0x1303F020 as *const u32;

    rprintln!("Trying to get CPU access to ROM memory (should fail with SecureFault!)");
    let buf = unsafe { ptr.read_volatile() };
    rprintln!("buf: {:X?}", buf);

    rprintln!("!!! SHOULD NOT BE REACHABLE !!!");
}
