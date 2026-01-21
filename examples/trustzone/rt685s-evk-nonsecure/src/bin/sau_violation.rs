#![no_std]
#![no_main]

use cortex_m::peripheral::sau::{SauRegion, SauRegionAttribute};
use embassy_executor::Spawner;
use nonsecure_app::SECURE_MEMORY;
use panic_probe as _;
use rtt_target::rprintln;

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let (_p, mut cp) = nonsecure_app::init();

    rprintln!("Trying to reconfigure SAU to give access to secure memory (is RAZ/WI, should not do anything)");
    assert_eq!(cp.SAU.region_numbers(), 0); // RAZ/WI
    if let Err(e) = cp.SAU.set_region(
        5,
        SauRegion {
            base_address: SECURE_MEMORY as u32,
            limit_address: SECURE_MEMORY as u32 + 3,
            attribute: SauRegionAttribute::NonSecure,
        },
    ) {
        rprintln!("Failed to set: {:?}", e); // As region number is RAZ/WI.
    }

    rprintln!("Trying to get CPU access to secure memory (should fail with SecureFault!)");
    let buf = unsafe { SECURE_MEMORY.read_volatile() };
    rprintln!("buf: {:X?}", buf);

    rprintln!("!!! SHOULD NOT BE REACHABLE !!!");
}
