#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::clocks::config::{ClockOutSource, Div8, M4860IrcSelect};
use embassy_time::Timer;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let peripherals = unsafe { embassy_imxrt::Peripherals::steal() };
    let mut cfg = embassy_imxrt::config::Config::default();

    // // 16m: works!
    // cfg.clocks.enable_16m_irc = true;
    // cfg.clocks.clk_out_select = ClockOutSource::M16Irc;
    // cfg.clocks.clk_out_div = Some(Div8::from_raw(1));

    // 32k: works!
    // cfg.clocks.enable_32k_clk = true;
    // cfg.clocks.clk_out_select = ClockOutSource::K32Clk;
    // cfg.clocks.clk_out_div = Some(Div8::from_raw(0));

    // 1m: works!
    // cfg.clocks.enable_1m_lposc = true;
    // cfg.clocks.clk_out_select = ClockOutSource::M1Lposc;
    // cfg.clocks.clk_out_div = Some(Div8::from_raw(0));

    // 48m: weird
    // 48mhz is 50mhz? 50/50
    // 60mhz is 62.5mhz, 37.5% duty cycle?
    // At /10
    // 48mhz is 4.97MHz
    // 60mhz is 6.28MHz
    // cfg.clocks.m4860_irc_select = M4860IrcSelect::Mhz60;
    // cfg.clocks.m4860_irc_select = M4860IrcSelect::Mhz48;
    // cfg.clocks.clk_out_select = ClockOutSource::M4860Irc;
    // cfg.clocks.clk_out_div = Some(Div8::from_raw(9));

    // MainClk is currently set up to 16mhz irc x 20: works!
    // cfg.clocks.clk_out_select = ClockOutSource::MainClk;
    // cfg.clocks.clk_out_div = Some(Div8::from_raw(19));

    // pfd0 (clkout div 20): 15.976, works!
    // pdd0 (clkout div 20, pll 18/34): 8.452
    cfg.clocks.clk_out_select = ClockOutSource::MainPllClk;
    cfg.clocks.clk_out_div = Some(Div8::from_raw(19));
    {
        let pll = cfg.clocks.main_pll.as_mut().unwrap();
        pll.pfd0_div = Some(34);
    }

    cfg.clock_out_select = embassy_imxrt::clocks::config::ClkOutSelect::ClkOut0_24(peripherals.PIO0_24);
    embassy_imxrt::init_without_periphs(cfg);

    info!("Hello world");

    loop {
        Timer::after_millis(1000).await;
    }
}
