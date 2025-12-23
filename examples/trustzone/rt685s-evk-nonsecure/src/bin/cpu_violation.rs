#![no_std]
#![no_main]

use embassy_executor::Spawner;
use nonsecure_app::SECURE_MEMORY;
use panic_probe as _;
use rtt_target::rprintln;

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let (_p, _cp) = nonsecure_app::init();

    rprintln!("Trying to get CPU access to secure memory (should fail with SecureFault!)");
    let buf = unsafe { SECURE_MEMORY.read_volatile() };
    rprintln!("buf: {:X?}", buf);

    rprintln!("!!! SHOULD NOT BE REACHABLE !!!");
}
