#![no_std]
#![no_main]

extern crate embassy_imxrt_examples;

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::clocks::delay_loop_clocks;
use embassy_imxrt::gpio;
use embassy_imxrt::gpio::{Input, Level, Output};
use embassy_imxrt::iopctl::{DriveMode, DriveStrength, Inverter, Pull, SlewRate};
use embassy_time::{Duration, Timer};
use keyberon::debounce::Debouncer;
use keyberon::key_code::KbHidReport;
use keyberon::layout::Layout;
use keyberon::matrix::Matrix;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

const COLS: usize = 4;
const ROWS: usize = 4;
const N_LAYERS: usize = 1;

type Keymap = keyberon::layout::Layers<COLS, ROWS, N_LAYERS>;

static KEYMAP: Keymap = keyberon::layout::layout! {
  {
    [ Kp7 Kp8   Kp9     KpSlash ],
    [ Kp4 Kp5   Kp6     KpAsterisk ],
    [ Kp1 Kp2   Kp3     KpMinus ],
    [ Kp0 KpDot KpEqual KpPlus ],
 }
};

#[embassy_executor::task]
async fn led_task(mut led: gpio::Output<'static>) {
    loop {
        led.toggle();
        Timer::after_secs(1).await;
    }
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!("Keyboard example using Keyberon");

    spawner
        .spawn(led_task(gpio::Output::new(
            p.PIO0_26,
            gpio::Level::Low,
            gpio::DriveMode::PushPull,
            gpio::DriveStrength::Normal,
            gpio::SlewRate::Standard,
        )))
        .unwrap();

    let rows = [
        Input::new(p.PIO1_6, Pull::Up, Inverter::Disabled),
        Input::new(p.PIO1_4, Pull::Up, Inverter::Disabled),
        Input::new(p.PIO1_3, Pull::Up, Inverter::Disabled),
        Input::new(p.PIO0_18, Pull::Up, Inverter::Disabled),
    ];

    let cols = [
        Output::new(
            p.PIO0_30,
            Level::Low,
            DriveMode::PushPull,
            DriveStrength::Normal,
            SlewRate::Standard,
        ),
        Output::new(
            p.PIO0_29,
            Level::Low,
            DriveMode::PushPull,
            DriveStrength::Normal,
            SlewRate::Standard,
        ),
        Output::new(
            p.PIO0_28,
            Level::Low,
            DriveMode::PushPull,
            DriveStrength::Normal,
            SlewRate::Standard,
        ),
        Output::new(
            p.PIO0_27,
            Level::Low,
            DriveMode::PushPull,
            DriveStrength::Normal,
            SlewRate::Standard,
        ),
    ];

    let mut matrix = Matrix::new(rows, cols).unwrap();
    let mut debouncer = Debouncer::new([[false; 4]; 4], [[false; 4]; 4], 5);
    let mut layout = Layout::new(&KEYMAP);

    loop {
        for event in debouncer.events(matrix.get_with_delay(|| delay_loop_clocks(5, 250_000_000)).unwrap()) {
            layout.event(event);
        }

        layout.tick();

        let report = KbHidReport::from_iter(layout.keycodes());
        let bytes = report.as_bytes();

        if !bytes.iter().all(|k| *k == 0x00) {
            info!("HID Report Bytes: {:02x}", report.as_bytes());
        }

        Timer::after(Duration::from_millis(5)).await;
    }
}
