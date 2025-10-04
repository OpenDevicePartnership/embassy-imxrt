#![no_std]
#![no_main]

use core::slice;

use defmt::{error, info};
use embassy_executor::Spawner;
use embassy_imxrt::bind_interrupts;
use embassy_imxrt::espi::{
    Base, BaseOrAsz, BootStatus, Capabilities, Config, Direction, Espi, Event, InterruptHandler, Len, Maxspd,
    PortConfig,
};
use embassy_imxrt::peripherals::ESPI;
use {defmt_rtt as _, panic_probe as _, rt633_examples as _};

bind_interrupts!(struct Irqs {
    ESPI => InterruptHandler<ESPI>;
});

extern "C" {
    static __start_espi_data: u8;
    static __end_espi_data: u8;
}

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    let mut espi = Espi::new(
        p.ESPI,
        p.PIO7_29,
        p.PIO7_26,
        p.PIO7_27,
        p.PIO7_28,
        p.PIO7_30,
        p.PIO7_31,
        p.PIO7_25,
        p.PIO7_24,
        Irqs,
        Config {
            caps: Capabilities {
                max_speed: Maxspd::SmallThan20m,
                alert_as_a_pin: true,
                allow_oob: true,
                allow_128b_payload: true,
                ..Default::default()
            },
            ram_base: 0x2000_0000,
            status_addr: Some(0x480),
            status_base: Base::OffsetFrom0,
            ports_config: [
                PortConfig::MailboxSplit {
                    direction: Direction::BidirectionalUnenforced,
                    base_sel: BaseOrAsz::OffsetFrom0,
                    offset: 0,
                    // RAM use will be 2x length, one half for each
                    // direction.
                    length: Len::Len256,
                },
                PortConfig::MailboxSplitOOB {
                    offset: 512,
                    length: Len::Len256,
                },
                Default::default(),
                Default::default(),
                Default::default(),
            ],
            ..Default::default()
        },
    );

    info!("Hello eSPI");

    let data = unsafe {
        let start_espi_data = &__start_espi_data as *const u8 as *mut u32;
        let end_espi_data = &__end_espi_data as *const u8 as *mut u32;
        let espi_data_len = end_espi_data.offset_from(start_espi_data) as usize;

        slice::from_raw_parts_mut(start_espi_data, espi_data_len)
    };

    data.fill(0);

    // Boot success
    espi.boot_status(BootStatus::Success);
    espi.boot_done();

    loop {
        let event = espi.wait_for_event().await;

        match event {
            Ok(Event::PeripheralEvent(port_event)) => {
                info!(
                    "eSPI PeripheralEvent Port: {}, direction: {}, address: {}, offset: {}, length: {}",
                    port_event.port, port_event.direction, port_event.offset, port_event.base_addr, port_event.length,
                );
                espi.complete_port(port_event.port);
            }
            Ok(Event::OOBEvent(port_event)) => {
                info!(
                    "eSPI OOBEvent Port: {}, direction: {}, address: {}, offset: {}, length: {}",
                    port_event.port, port_event.direction, port_event.offset, port_event.base_addr, port_event.length,
                );
                espi.complete_port(port_event.port);
            }
            Ok(Event::WireChange(event)) => {
                info!("Wire Change! {}", event);

                if event.is_host_reset_warn() {
                    espi.host_reset_ack();
                }

                if event.is_suspend_warn() {
                    espi.suspend_ack();
                }

                if event.is_oob_reset_warn() {
                    espi.oob_reset_ack();
                }
            }
            Err(_) => {
                error!("Failed");
            }
            _ => todo!(),
        }
    }
}
