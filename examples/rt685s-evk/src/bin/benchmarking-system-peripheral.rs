#![no_std]
#![no_main]

use embassy_imxrt_examples as _;

use defmt::info;
use defmt_rtt as _;
use embassy_executor::Spawner;
use embassy_time::Timer;

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let _p = embassy_imxrt::init(Default::default());

    info!("Benchmarking using systick");

    let n = 10;

    let mut cortex = cortex_m::Peripherals::take().unwrap();

    loop {
        // If DWT cycle counter is available, we can use it to measure the time taken.
        // It is a 32-bit counter counting the CPU cycles
        // DWT only counts when the CPU clocks is alive
        // If there's WFE or other sleep operations that can occur within profiled sections,
        // then it can produce misleading results
        // Beware if your code has any async await point or can be preempted by ISRs
        if cortex_m::peripheral::DWT::has_cycle_counter() {
            cortex.DCB.enable_trace();
            cortex.DWT.enable_cycle_counter();
            cortex.DWT.set_cycle_count(0);

            for _i in 0..n {
                cortex_m::asm::nop();
            }

            let cycles = cortex_m::peripheral::DWT::cycle_count();
            cortex.DWT.disable_cycle_counter();
            cortex.DCB.disable_trace();
            info!("DWT Cycle Counter That took {} cycles!!!", cycles);
        } else {
            // But if DWT cycle counter is not available, we can use the systick timer
            // Beware that SysTick may or may not be clocked across WFI/WFE boundaries depending
            //   on the current configured CPU sleep state
            // SysTick can be used as an OS timer as well. If it is,
            //   then just use the OS timer to do the profiling
            cortex.SYST.disable_counter();
            cortex
                .SYST
                .set_clock_source(cortex_m::peripheral::syst::SystClkSource::Core);

            // Do be aware that systick is only 23 bits and our cpu clock is running at 250 MHz
            // so this will wrap around 15 times per second. If the operation will be longer than
            // 1/15 of a second, then wraparound have to be taken into account
            cortex.SYST.set_reload(0xFFFFFF);
            cortex.SYST.clear_current();
            cortex.SYST.enable_counter();

            let start = cortex_m::peripheral::SYST::get_current();

            // Operation to be benchmarked
            for _i in 0..n {
                cortex_m::asm::nop();
            }

            let end = cortex_m::peripheral::SYST::get_current();

            // systick is counting down so subtract end from start
            info!("SYSTICK That took {} ticks!!!", start - end);
        }

        // we can trace the duration out
        // or we can keep a running average
        // or we can write the values to scratch regs, rtc::Gpreg 3 to 7 (0 to 2 are being used by RTC timer)

        Timer::after_millis(100).await;
    }
}
