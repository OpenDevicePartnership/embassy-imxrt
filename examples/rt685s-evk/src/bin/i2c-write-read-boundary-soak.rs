//! I2C `write_read` boundary soak.
//!
//! Exercises the specific master pattern that surfaces
//! `WriteStatus::Restarted(0)` on the slave's `embedded_mcu_hal::i2c::target`
//! trait API:
//!
//!   master.write_read(addr, &w[..k*S], &mut r[..m])
//!
//! where:
//!
//! * `S` is the slave receive-buffer length (see `SLAVE_BUFLEN`).
//! * `k` cycles round-robin over `BOUNDARY_K_MIN ..= BOUNDARY_K_MAX`.
//! * `m` cycles round-robin over `READ_LEN_MIN ..= READ_LEN_MAX`, with
//!   `READ_LEN_MAX < S` so the read leg is always a simple
//!   NACK+STOP-terminated short read (never another `k*S` boundary).
//!
//! ## Why this matters
//!
//! When the master writes exactly `k*S` bytes and follows with a
//! repeated-START into the read phase, the slave's first
//! `respond_to_write` call drains a full buffer and returns
//! `WriteStatus::BufferFull(S)`. The caller loops with a fresh buffer; by
//! then the controller has issued Sr on the wire and the second
//! `respond_to_write` returns `WriteStatus::Restarted(0)` — a zero-byte
//! restart. The `i2c-slave-async-target-trait` example flags this as a
//! `RACE WATCH` line because, on a healthy bus, a real Sr is preceded by
//! at least one ACKed payload byte on the call that observes it.
//!
//! Hypothesis under test: the `Restarted(0)` shape is a *buffer-boundary
//! surfacing artifact*, not a hardware race. If the soak runs for
//! millions of iterations without:
//!
//! * a transfer timing out (master or slave wedge),
//! * an error return from any trait/master call,
//! * a mismatch in the read-back payload,
//!
//! then the artifact is benign and the surfacing API is the place to
//! address it (if at all). Any timeout or mismatch panics immediately so
//! RTT freezes with the offending iteration's context.
//!
//! ## Wiring
//!
//! Same FC2 ↔ FC4 loopback as `i2c-loopback-async.rs` on the RT685S-EVK:
//!
//! * FC2 slave:  SCL = PIO0_18, SDA = PIO0_17, DMA = DMA0_CH4
//! * FC4 master: SCL = PIO0_29, SDA = PIO0_30, DMA = DMA0_CH9
//! * Speed: Fast (400 kHz), 50% duty.
//!
//! ### Pull-ups
//!
//! I2C requires pull-up resistors on SDA and SCL to drive the lines
//! high when neither end is asserting them low (per UM10204). The
//! FC2 ↔ FC4 loopback on the EVK wires two GPIO pins directly with no
//! external resistors. Without pull-ups, every "release" of the line
//! leaves it floating and both peripheral state machines stall
//! waiting for SCL/SDA edges that never come.
//!
//! The driver's `as_scl()`/`as_sda()` enables the SoC's internal
//! pull-ups (~40 kΩ-100 kΩ) so this loopback configuration works
//! out-of-the-box. On a real I2C bus with external pull-ups the
//! internal pull-up parallels them with negligible effect on rise
//! time.
//!
//! ## What to look for in RTT
//!
//! Per-event `info!` logging is intentionally silenced: at thousands of
//! transactions per second it saturates the RTT channel and slows the
//! loop. Instead each task emits a counter summary every `REPORT_EVERY`
//! iterations:
//!
//! * `[slave] iter=… cont=… restZ=… …` — slave-side event tallies.
//! * `[master] iter=… k=… m=… write_len=…` — master-side progress.
//!
//! A healthy run shows both counters climbing steadily with `restZ`
//! (zero-byte restarts) and `cont` (buffer-full continuations) growing
//! every iteration and no `RACE WATCH` warnings. Absence of any
//! `defmt::panic!` over a long run is the pass signal; a wedge, error,
//! or read-back mismatch panics immediately with the offending
//! iteration's context.

#![no_std]
#![no_main]

use defmt::{info, warn};
use defmt_rtt as _;
use embassy_executor::Spawner;
use embassy_imxrt::i2c::master::{DutyCycle, I2cMaster};
use embassy_imxrt::i2c::slave::{Address, I2cSlave};
use embassy_imxrt::i2c::{self, Async};
use embassy_imxrt::{bind_interrupts, peripherals};
use embassy_imxrt_examples as _;
use embassy_time::{Duration, with_timeout};
use embedded_hal_async::i2c::I2c;
use embedded_mcu_hal::i2c::SevenBitAddress;
use embedded_mcu_hal::i2c::target::asynch::I2c as TargetI2c;
use embedded_mcu_hal::i2c::target::{ReadStatus, Request, WriteStatus};
use panic_probe as _;

// ---------------------------------------------------------------------------
// Tunables
// ---------------------------------------------------------------------------

const ADDR: u8 = 0x20;
const SLAVE_ADDR: Option<Address> = Address::new(ADDR);

/// Slave receive-buffer length `S`. Small on purpose — keeps the `k*S`
/// boundary firing every iteration and minimises stack use.
const SLAVE_BUFLEN: usize = 4;

/// Smallest `k` in `master.write_read(addr, &w[..k*S], …)`.
const BOUNDARY_K_MIN: usize = 1;
/// Largest `k`. The master write payload length sweeps round-robin over
/// `[k*S for k in K_MIN..=K_MAX]`, i.e. always an exact multiple of `S`.
const BOUNDARY_K_MAX: usize = 4;

/// Smallest read-leg length `m`.
const READ_LEN_MIN: usize = 1;
/// Largest read-leg length. Keep `< SLAVE_BUFLEN` so the read leg always
/// terminates with a NACK+STOP on the first `respond_to_read` call.
const READ_LEN_MAX: usize = SLAVE_BUFLEN - 1;

/// How often each task emits a counter-summary line.
const REPORT_EVERY: u32 = 10_000;

/// Per-await timeout for every transfer. Generous to absorb defmt-rtt
/// flush jitter during periodic summary lines; anything longer than this
/// is a wedge worth investigating.
const PER_TRANSFER_TIMEOUT: Duration = Duration::from_millis(250);

/// Outer timeout on `listen()`. Generous compared to the per-transfer
/// timeout because between transactions the bus can sit idle briefly
/// while the master service formats its next buffer, but a 2 s wait
/// with both ends running on the same chip means something is wrong.
const PER_LISTEN_TIMEOUT: Duration = Duration::from_millis(2000);

/// Maximum master write payload size — `k_max * S`.
const MASTER_MAX_WRITE: usize = BOUNDARY_K_MAX * SLAVE_BUFLEN;
/// Maximum master read payload size — `m_max`.
const MASTER_MAX_READ: usize = READ_LEN_MAX;

bind_interrupts!(struct Irqs {
    FLEXCOMM2 => i2c::InterruptHandler<peripherals::FLEXCOMM2>;
    FLEXCOMM4 => i2c::InterruptHandler<peripherals::FLEXCOMM4>;
});

// ---------------------------------------------------------------------------
// Slave service
// ---------------------------------------------------------------------------

#[embassy_executor::task]
async fn slave_service(mut slave: I2cSlave<'static, Async>) {
    // Slave-local iteration counter. Advances once per `listen()` event.
    // The TX pattern is keyed on its low byte; the master verifies the
    // monotonic increment in the read buffer relative to the first byte
    // it actually received, so the two counters do not need to be in
    // lock-step.
    let mut slv_iter: u32 = 0;

    // Tracks whether the most recent `respond_to_*` ended with
    // `Restarted(_)`. The next `listen()` should return
    // `Request::RepeatedStart(_)`; any other shape is suspicious.
    let mut expect_repeated_start = false;

    // Counters.
    let mut write_continued: u32 = 0;
    let mut write_restarted_zero: u32 = 0;
    let mut write_restarted_nonzero: u32 = 0;
    let mut write_stopped_zero: u32 = 0;
    let mut write_stopped_nonzero: u32 = 0;
    let mut read_complete: u32 = 0;
    let mut read_need_more: u32 = 0;
    let mut read_early_stop: u32 = 0;
    let mut repeated_start_count: u32 = 0;
    let mut probe_count: u32 = 0;

    loop {
        let mut r_buf = [0xAAu8; SLAVE_BUFLEN];
        let mut t_buf = [0xAAu8; SLAVE_BUFLEN];

        // Per-iteration keyed TX pattern: t_buf[j] = (j + key) mod 256.
        // The master checks the increment r_buf[j] - r_buf[0] == j (mod
        // 256). This catches cross-iteration buffer bleed without
        // requiring shared state between tasks.
        let key = slv_iter as u8;
        for (j, e) in t_buf.iter_mut().enumerate() {
            *e = (j as u8).wrapping_add(key);
        }

        // listen() guarded by PER_LISTEN_TIMEOUT. The chip is both
        // master and slave; under healthy operation the master is
        // hammering the slave at thousands of transactions/sec, so a
        // listen() that does not return within the timeout window
        // indicates a real wedge worth investigating.
        let req = match with_timeout(
            PER_LISTEN_TIMEOUT,
            TargetI2c::<SevenBitAddress>::listen(&mut slave),
        )
        .await
        {
            Err(_) => defmt::panic!("WEDGE: slave.listen() at slv_iter={}", slv_iter),
            Ok(Err(e)) => defmt::panic!(
                "slave.listen() err at slv_iter={}: {:?}",
                slv_iter,
                defmt::Debug2Format(&e)
            ),
            Ok(Ok(r)) => r,
        };

        let was_expecting_restart = expect_repeated_start;
        expect_repeated_start = false;

        match req {
            Request::Stop(_) => {
                probe_count += 1;
                if was_expecting_restart {
                    warn!("RACE WATCH: prior respond_to_* reported Stop but expected RepeatedStart");
                }
            }
            Request::RepeatedStart(_) => {
                repeated_start_count += 1;
                if !was_expecting_restart {
                    warn!("RACE WATCH: RepeatedStart surfaced without a prior Restarted(_)");
                }
            }
            Request::Read(_) => {
                loop {
                    let r = match with_timeout(
                        PER_TRANSFER_TIMEOUT,
                        TargetI2c::<SevenBitAddress>::respond_to_read(&mut slave, &t_buf),
                    )
                    .await
                    {
                        Err(_) => defmt::panic!("WEDGE: respond_to_read at slv_iter={}", slv_iter),
                        Ok(Err(e)) => defmt::panic!(
                            "respond_to_read err at slv_iter={}: {:?}",
                            slv_iter,
                            defmt::Debug2Format(&e)
                        ),
                        Ok(Ok(r)) => r,
                    };
                    match r {
                        ReadStatus::Complete(_) => {
                            read_complete += 1;
                            break;
                        }
                        ReadStatus::EarlyStop(_) => {
                            read_early_stop += 1;
                            break;
                        }
                        ReadStatus::NeedMore(_) => {
                            read_need_more += 1;
                            // Loop and supply `t_buf` again.
                        }
                        _ => {
                            // ReadStatus is #[non_exhaustive]; ignore.
                            break;
                        }
                    }
                }
            }
            Request::Write(_) => {
                loop {
                    let r = match with_timeout(
                        PER_TRANSFER_TIMEOUT,
                        TargetI2c::<SevenBitAddress>::respond_to_write(&mut slave, &mut r_buf),
                    )
                    .await
                    {
                        Err(_) => defmt::panic!("WEDGE: respond_to_write at slv_iter={}", slv_iter),
                        Ok(Err(e)) => defmt::panic!(
                            "respond_to_write err at slv_iter={}: {:?}",
                            slv_iter,
                            defmt::Debug2Format(&e)
                        ),
                        Ok(Ok(r)) => r,
                    };
                    match r {
                        WriteStatus::BufferFull(_) => {
                            write_continued += 1;
                            // Loop and continue draining.
                        }
                        WriteStatus::Stopped(n) => {
                            if n == 0 {
                                write_stopped_zero += 1;
                            } else {
                                write_stopped_nonzero += 1;
                            }
                            break;
                        }
                        WriteStatus::Restarted(n) => {
                            if n == 0 {
                                write_restarted_zero += 1;
                            } else {
                                write_restarted_nonzero += 1;
                            }
                            // Do NOT call recover() — the Sr+ADDR is queued
                            // on the wire and the next listen() must surface
                            // it as RepeatedStart.
                            expect_repeated_start = true;
                            break;
                        }
                        _ => {
                            // WriteStatus is #[non_exhaustive]; ignore.
                            break;
                        }
                    }
                }
            }
            _ => {
                info!("unhandled request variant");
            }
        }

        slv_iter = slv_iter.wrapping_add(1);

        if slv_iter % REPORT_EVERY == 0 {
            info!(
                "[slave] iter={} cont={} restZ={} restN={} stopZ={} stopN={} readC={} readNM={} readES={} rstart={} probe={}",
                slv_iter,
                write_continued,
                write_restarted_zero,
                write_restarted_nonzero,
                write_stopped_zero,
                write_stopped_nonzero,
                read_complete,
                read_need_more,
                read_early_stop,
                repeated_start_count,
                probe_count
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Master service
//
// FC4 master driving FC2 slave via PIO0_29/PIO0_30 ↔ PIO0_18/PIO0_17
// loopback wires. No external controller — the rt685 talks to itself,
// so the soak is self-contained on a single board.
// ---------------------------------------------------------------------------

#[embassy_executor::task]
async fn master_service(mut master: I2cMaster<'static, Async>) {
    let mut w_buf = [0u8; MASTER_MAX_WRITE];
    let mut r_buf = [0u8; MASTER_MAX_READ];

    let mut iter: u32 = 0;

    loop {
        // Round-robin sweep over (k, m). k_window = 4 entries, m_window = 3
        // entries; together that's 12 unique pairs in 12 iterations.
        let k = BOUNDARY_K_MIN + ((iter as usize) % (BOUNDARY_K_MAX - BOUNDARY_K_MIN + 1));
        let read_len = READ_LEN_MIN + ((iter as usize) % (READ_LEN_MAX - READ_LEN_MIN + 1));
        let write_len = k * SLAVE_BUFLEN;

        // Tag the write payload with the iter low byte for forensics on
        // the slave side if a future test wants to inspect r_buf there.
        // Content is otherwise irrelevant to the soak's verification.
        for (j, e) in w_buf[..write_len].iter_mut().enumerate() {
            *e = (j as u8).wrapping_add(iter as u8);
        }
        for e in r_buf[..read_len].iter_mut() {
            *e = 0;
        }

        match with_timeout(
            PER_TRANSFER_TIMEOUT,
            master.write_read(ADDR, &w_buf[..write_len], &mut r_buf[..read_len]),
        )
        .await
        {
            Err(_) => defmt::panic!(
                "WEDGE: master.write_read timed out at iter={}, k={}, m={}",
                iter,
                k,
                read_len
            ),
            Ok(Err(e)) => defmt::panic!(
                "master.write_read err at iter={}, k={}, m={}: {:?}",
                iter,
                k,
                read_len,
                defmt::Debug2Format(&e)
            ),
            Ok(Ok(())) => {
                // Verify the read buffer is a monotonic increment starting
                // from `r_buf[0]`. Slave fills `t_buf[j] = (j + key) mod
                // 256` so the difference `r_buf[j] - r_buf[0]` must equal
                // `j` (mod 256) regardless of which slave iteration
                // produced the data.
                let base = r_buf[0];
                for j in 1..read_len {
                    let expect = base.wrapping_add(j as u8);
                    if r_buf[j] != expect {
                        defmt::panic!(
                            "READ MISMATCH at iter={}, k={}, m={}, j={}: got 0x{:02X}, expected 0x{:02X} (base=0x{:02X})",
                            iter,
                            k,
                            read_len,
                            j,
                            r_buf[j],
                            expect,
                            base
                        );
                    }
                }
            }
        }

        if iter % REPORT_EVERY == 0 {
            info!("[master] iter={} k={} m={} write_len={}", iter, k, read_len, write_len);
        }
        iter = iter.wrapping_add(1);
    }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());

    info!(
        "i2c write_read boundary soak (S={}, k=[{}..={}], m=[{}..={}], timeout={}ms)",
        SLAVE_BUFLEN,
        BOUNDARY_K_MIN,
        BOUNDARY_K_MAX,
        READ_LEN_MIN,
        READ_LEN_MAX,
        PER_TRANSFER_TIMEOUT.as_millis()
    );

    let slave = I2cSlave::new_async(p.FLEXCOMM2, p.PIO0_18, p.PIO0_17, Irqs, SLAVE_ADDR.unwrap(), p.DMA0_CH4).unwrap();

    // FC4 master on PIO0_29 (SCL) / PIO0_30 (SDA) driving FC2 slave on
    // PIO0_18 (SCL) / PIO0_17 (SDA) via direct loopback wires on the
    // rt685s-evk. No external controller — the chip drives both sides
    // of the bus.
    let cfg = i2c::master::Config {
        speed: i2c::master::Speed::Fast,
        duty_cycle: DutyCycle::new(50).unwrap(),
        ..Default::default()
    };
    let master = I2cMaster::new_async(p.FLEXCOMM4, p.PIO0_29, p.PIO0_30, Irqs, cfg, p.DMA0_CH9).unwrap();

    spawner.spawn(slave_service(slave).unwrap());
    spawner.spawn(master_service(master).unwrap());
}
