#![no_std]
#![no_main]

use embassy_executor::Spawner;
use embassy_time::Timer;
use panic_probe as _;
use rtt_target::rprintln;

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let (_p, _cp) = nonsecure_app::init();
    rprintln!("Test whether we can call a secure function (with success)");

    loop {
        rprintln!("Calling secure function: {}", nonsecure_app::do_stuff_secure(5));
        Timer::after_secs(1).await;
    }
}
