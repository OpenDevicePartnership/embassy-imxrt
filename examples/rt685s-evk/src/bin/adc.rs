#![no_std]
#![no_main]

use defmt::info;
use embassy_executor::Spawner;
use embassy_imxrt::adc::{Adc, Average, ChannelConfig, Config, InterruptHandler};
use embassy_imxrt::{bind_interrupts, peripherals};
use embassy_time::Timer;
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

bind_interrupts!(struct Irqs {
    ADC0 => InterruptHandler<peripherals::ADC0>;
});

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());
    let channel_config = [
        ChannelConfig::single_ended_with_average(p.PIO0_5, Average::_16),
        ChannelConfig::single_ended(p.PIO0_6),
    ];
    let mut adc = Adc::new(p.ADC0, Irqs, Config::default(), channel_config);

    loop {
        let mut data: [i16; 2] = [0; 2];
        adc.sample(&mut data).await;

        info!("ADC sample = {:#x}", data);

        Timer::after_millis(1000).await;
    }
}
