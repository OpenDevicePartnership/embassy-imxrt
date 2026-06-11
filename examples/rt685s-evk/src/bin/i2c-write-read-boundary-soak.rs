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
//! waiting for SCL/SDA edges that never come — reproducible as the
//! master/slave mutual wedge captured by an early breadcrumb dump on
//! this soak.
//!
//! The driver's `as_scl()`/`as_sda()` enables the SoC's internal
//! pull-ups (~40 kΩ-100 kΩ) so this loopback configuration works
//! out-of-the-box. On a real I2C bus with external pull-ups the
//! internal pull-up parallels them with negligible effect on rise
//! time.
//!
//! ## What to look for in RTT
//!
//! Per master iteration (one of 4×3 = 12 unique `(k, m)` pairs in
//! round-robin):
//!
//! * 1× `Write @ 0x20` on the slave (from `Request::Write`).
//! * `k`× `Write BufferFull after S bytes — supplying more buffer space`.
//! * 1× `Write restarted after 0 bytes …` + `RACE WATCH:
//!   WriteStatus::Restarted(0)` warning.
//! * 1× `RepeatedStart from prev @ 0x20`.
//! * 1× `Read @ 0x20`.
//! * 1× `Read terminated by controller after m bytes` (always EarlyStop
//!   because `m < S`).
//!
//! Counter summaries are emitted by each task every `REPORT_EVERY`
//! iterations. Absence of any `defmt::panic!` over a long run is the
//! pass signal.
//!
//! ## Forensic breadcrumbs
//!
//! Adding per-step `info!` lines slows the loop enough to mask the
//! release-mode HardFault we are chasing. Instead each step in both
//! tasks stores a packed `(site_id, iter)` u32 into a 32-entry static
//! ring buffer (a single relaxed atomic store, no formatting, no
//! critical section). Every `wedge_panic!` call flushes the ring via
//! `defmt::error!` *before* delegating to `defmt::panic!`, so the RTT
//! log carries the last 32 (task, site, iter) transitions immediately
//! preceding any wedge/error/mismatch panic. See `breadcrumb()` and the
//! site-ID table near the top of this file.
//!
//! ## Reading the breadcrumb ring with probe-rs
//!
//! When the failure is our own `wedge_panic!`, the ring contents are
//! already on RTT — no extra step is required. When the failure is a
//! true CPU HardFault (no panic message reached RTT, just
//! `Firmware exited unexpectedly: Exception` from probe-rs), the ring
//! still lives in RAM because `panic-probe`'s `udf` halt loop does not
//! touch user data. Read it directly:
//!
//! ### 1. Discover the symbol addresses
//!
//! ```text
//! $ rust-nm target/thumbv8m.main-none-eabihf/release/i2c-write-read-boundary-soak \
//!     | rg 'BREADCRUMB_(INDEX|RING)'
//! 20081200 D BREADCRUMB_INDEX
//! 20081204 D BREADCRUMB_RING
//! ```
//!
//! Address values will differ per build; always rediscover after a
//! rebuild. The `D` flag confirms the symbols live in the data
//! (`.bss` / `.data`) region, which `panic-probe`'s `udf` halt does
//! not perturb.
//!
//! ### 2. Read the ring index and the ring
//!
//! `probe-rs read` opens its own debug session on each invocation, so
//! no separate `attach` is required — and a long-lived `attach` in
//! another shell would actually block the read. probe-rs also rejects
//! `_` digit separators in numeric arguments; use plain hex.
//!
//! ```text
//! # 32-bit index (1 word):
//! $ probe-rs read --chip MIMXRT685SFVKB b32 0x20081200 1
//! 0x00000087
//!
//! # 32-entry ring (32 words = 128 bytes):
//! $ probe-rs read --chip MIMXRT685SFVKB b32 0x20081204 32
//! 0x14000086 0x15000086 0x19000086 0x13000086 0x14000087 ...
//! ```
//!
//! ### 3. Decode entries
//!
//! Each `u32` is packed `(site << 24) | (iter & 0x00FFFFFF)`:
//!
//! * **site** = `(packed >> 24) & 0xFF` — cross-reference with the
//!   site-ID table in the source comments above (`0x10`..`0x19` =
//!   slave_service, `0x20`..`0x24` = master_service).
//! * **iter** = `packed & 0x00FFFFFF` — the task-local iteration
//!   counter at the time the breadcrumb was dropped. Saturates at
//!   24 bits; not unique across long soaks but the local ordering
//!   within the last 32 entries is always meaningful.
//!
//! ### 4. Reconstruct chronological order
//!
//! Entries are written round-robin. Let `next = BREADCRUMB_INDEX`,
//! `count = min(next, 32)`, `start = next.wrapping_sub(count)`. Read
//! in order: slots `(start + 0) & 31`, `(start + 1) & 31`, …,
//! `(start + count - 1) & 31`. The on-target `dump_breadcrumbs()`
//! function does the same reconstruction; emulating it off-target
//! recovers the same oldest-to-newest sequence.
//!
//! ### 5. Optional: Python decoder
//!
//! Paste the `probe-rs read` outputs into this short script to
//! reproduce the RTT dump format off-target. Python accepts `_` in
//! numeric literals; the example values below drop them so they match
//! `probe-rs read` output verbatim.
//!
//! ```python
//! #!/usr/bin/env python3
//! # usage: paste the index value and 32 ring words below, then run.
//! index = 0x00000087
//! ring  = [
//!     0x14000086, 0x15000086, 0x19000086, 0x13000086,
//!     # ... 28 more u32 words from `probe-rs read` ...
//! ]
//! count = min(index, len(ring))
//! start = (index - count) % len(ring)
//! for i in range(count):
//!     packed = ring[(start + i) % len(ring)]
//!     site = (packed >> 24) & 0xFF
//!     iter = packed & 0x00FFFFFF
//!     print(f"bc[{i:2}]: site=0x{site:02X} iter={iter}")
//! ```
//!
//! ### 6. Optional: GDB stub
//!
//! If you prefer GDB:
//!
//! ```text
//! $ probe-rs gdb --chip MIMXRT685SFVKB &
//! $ arm-none-eabi-gdb \
//!     target/thumbv8m.main-none-eabihf/release/i2c-write-read-boundary-soak
//! (gdb) target remote :1337
//! (gdb) print/x BREADCRUMB_INDEX
//! (gdb) print/x BREADCRUMB_RING
//! ```
//!
//! GDB prints the array nicely formatted; apply the same decoding
//! from step 3 to each element.

#![no_std]
#![no_main]

use core::sync::atomic::{AtomicU32, AtomicUsize, Ordering};

use defmt::{error, info, warn};
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
// Forensic breadcrumb ring
// ---------------------------------------------------------------------------
//
// In release mode this soak has been observed to HardFault between
// `Read @ 0x20` and the subsequent `respond_to_read` await, with no
// `WEDGE:` panic message reaching RTT. Adding any per-iteration `info!`
// slows the loop enough to mask the fault. The breadcrumb ring is the
// cheapest possible forensic trail: each checkpoint does one atomic
// store of a packed `(site << 24) | (iter & 0xFFFFFF)` u32 into a
// 32-entry static ring, no formatting and no critical section.
//
// On a wedge `defmt::panic!`, `dump_breadcrumbs!()` flushes the last 32
// entries via `defmt::error!` *before* delegating to the panic macro.
// That gives us the exact sequence of slave + master steps leading up
// to the failure, even when the per-iteration `info!` lines that would
// usually narrate the state cannot be afforded.
//
// Site IDs are packed into the upper byte:
//
// 0x1_ — slave_service lane
//   0x10 enter loop / about to call listen()
//   0x11 listen() returned
//   0x12 Probe arm
//   0x13 RepeatedStart arm
//   0x14 Read arm entered
//   0x15 about to await respond_to_read
//   0x16 respond_to_read returned, classifying status
//   0x17 Write arm entered
//   0x18 about to await respond_to_write
//   0x19 respond_to_write returned, classifying status
//
// 0x2_ — master_service lane
//   0x20 chose k, m; filled buffers
//   0x21 about to await master.write_read
//   0x22 master.write_read returned Ok
//   0x23 verifying read payload increment
//   0x24 verification passed

const BREADCRUMB_RING_LEN: usize = 32;
const BREADCRUMB_RING_MASK: usize = BREADCRUMB_RING_LEN - 1;
const _: () = assert!(BREADCRUMB_RING_LEN.is_power_of_two());

static BREADCRUMB_INDEX: AtomicUsize = AtomicUsize::new(0);
static BREADCRUMB_RING: [AtomicU32; BREADCRUMB_RING_LEN] = {
    const Z: AtomicU32 = AtomicU32::new(0);
    [Z; BREADCRUMB_RING_LEN]
};

#[inline(always)]
fn breadcrumb(site: u8, iter: u32) {
    let packed = ((site as u32) << 24) | (iter & 0x00FF_FFFF);
    let idx = BREADCRUMB_INDEX.fetch_add(1, Ordering::Relaxed) & BREADCRUMB_RING_MASK;
    BREADCRUMB_RING[idx].store(packed, Ordering::Relaxed);
}

/// Dump the breadcrumb ring oldest-to-newest via `defmt::error!`.
/// Intended to be called immediately before `defmt::panic!` at any
/// wedge site so the panic-loop halt does not race the panic message
/// to RTT.
fn dump_breadcrumbs() {
    let next = BREADCRUMB_INDEX.load(Ordering::Relaxed);
    let count = next.min(BREADCRUMB_RING_LEN);
    let start = next.wrapping_sub(count);
    error!("---- breadcrumb dump ({} entries, newest last) ----", count);
    for i in 0..count {
        let slot = (start.wrapping_add(i)) & BREADCRUMB_RING_MASK;
        let packed = BREADCRUMB_RING[slot].load(Ordering::Relaxed);
        let site = (packed >> 24) as u8;
        let iter = packed & 0x00FF_FFFF;
        error!("  bc[{}]: site=0x{:02X} iter={}", i, site, iter);
    }
    error!("---- end breadcrumb dump ----");
}

/// Panic with full breadcrumb dump. Replaces `defmt::panic!` at every
/// wedge / error site so the RTT log carries the last 32 (site, iter)
/// transitions before the chip halts.
macro_rules! wedge_panic {
    ($($arg:tt)*) => {{
        $crate::dump_breadcrumbs();
        defmt::panic!($($arg)*);
    }};
}

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

        // listen() with timeout — wedge on the listen side panics.
        breadcrumb(0x10, slv_iter);
        let req = match with_timeout(PER_TRANSFER_TIMEOUT, TargetI2c::<SevenBitAddress>::listen(&mut slave)).await {
            Err(_) => wedge_panic!("WEDGE: slave.listen() timed out at slv_iter={}", slv_iter),
            Ok(Err(e)) => wedge_panic!(
                "slave.listen() err at slv_iter={}: {:?}",
                slv_iter,
                defmt::Debug2Format(&e)
            ),
            Ok(Ok(r)) => r,
        };
        breadcrumb(0x11, slv_iter);

        let was_expecting_restart = expect_repeated_start;
        expect_repeated_start = false;

        match req {
            Request::Stop(addr) => {
                breadcrumb(0x12, slv_iter);
                probe_count += 1;
                info!("Stop @ 0x{:02X} (probe)", addr);
                if was_expecting_restart {
                    warn!(
                        "RACE WATCH: prior respond_to_* reported Restarted but listen() returned Stop(0x{:02X}); expected RepeatedStart",
                        addr
                    );
                }
            }
            Request::RepeatedStart(prev_addr) => {
                breadcrumb(0x13, slv_iter);
                repeated_start_count += 1;
                info!("RepeatedStart from prev @ 0x{:02X}", prev_addr);
                if !was_expecting_restart {
                    warn!(
                        "RACE WATCH: RepeatedStart(0x{:02X}) surfaced without a prior Restarted(_)",
                        prev_addr
                    );
                }
            }
            Request::Read(addr) => {
                breadcrumb(0x14, slv_iter);
                info!("Read @ 0x{:02X}", addr);
                if was_expecting_restart {
                    info!("(consumed expected RepeatedStart edge before Read)");
                }
                loop {
                    breadcrumb(0x15, slv_iter);
                    let r = match with_timeout(
                        PER_TRANSFER_TIMEOUT,
                        TargetI2c::<SevenBitAddress>::respond_to_read(&mut slave, &t_buf),
                    )
                    .await
                    {
                        Err(_) => wedge_panic!("WEDGE: respond_to_read at slv_iter={}", slv_iter),
                        Ok(Err(e)) => wedge_panic!(
                            "respond_to_read err at slv_iter={}: {:?}",
                            slv_iter,
                            defmt::Debug2Format(&e)
                        ),
                        Ok(Ok(r)) => r,
                    };
                    breadcrumb(0x16, slv_iter);
                    match r {
                        ReadStatus::Complete(n) => {
                            read_complete += 1;
                            info!("Read complete with {} bytes", n);
                            break;
                        }
                        ReadStatus::EarlyStop(n) => {
                            read_early_stop += 1;
                            info!("Read terminated by controller after {} bytes", n);
                            break;
                        }
                        ReadStatus::NeedMore(n) => {
                            read_need_more += 1;
                            info!("Read NeedMore: sent {} bytes so far, more requested", n);
                            // Loop and supply `t_buf` again.
                        }
                        _ => {
                            // ReadStatus is #[non_exhaustive]; ignore.
                            info!("Read: unknown status variant");
                            break;
                        }
                    }
                }
            }
            Request::Write(addr) => {
                breadcrumb(0x17, slv_iter);
                info!("Write @ 0x{:02X}", addr);
                if was_expecting_restart {
                    info!("(consumed expected RepeatedStart edge before Write)");
                }
                loop {
                    breadcrumb(0x18, slv_iter);
                    let r = match with_timeout(
                        PER_TRANSFER_TIMEOUT,
                        TargetI2c::<SevenBitAddress>::respond_to_write(&mut slave, &mut r_buf),
                    )
                    .await
                    {
                        Err(_) => wedge_panic!("WEDGE: respond_to_write at slv_iter={}", slv_iter),
                        Ok(Err(e)) => wedge_panic!(
                            "respond_to_write err at slv_iter={}: {:?}",
                            slv_iter,
                            defmt::Debug2Format(&e)
                        ),
                        Ok(Ok(r)) => r,
                    };
                    breadcrumb(0x19, slv_iter);
                    match r {
                        WriteStatus::BufferFull(n) => {
                            write_continued += 1;
                            info!("Write BufferFull after {} bytes — supplying more buffer space", n);
                            // Loop and continue draining.
                        }
                        WriteStatus::Stopped(n) => {
                            if n == 0 {
                                write_stopped_zero += 1;
                            } else {
                                write_stopped_nonzero += 1;
                            }
                            info!("Write stopped after {} bytes", n);
                            break;
                        }
                        WriteStatus::Restarted(n) => {
                            if n == 0 {
                                write_restarted_zero += 1;
                                info!("Write restarted after 0 bytes — next listen will surface RepeatedStart");
                                warn!(
                                    "RACE WATCH: WriteStatus::Restarted(0) — buffer-boundary surfacing artifact under test"
                                );
                            } else {
                                write_restarted_nonzero += 1;
                                info!("Write restarted after {} bytes", n);
                            }
                            // Do NOT call recover() — the Sr+ADDR is queued
                            // on the wire and the next listen() must surface
                            // it as RepeatedStart.
                            expect_repeated_start = true;
                            break;
                        }
                        _ => {
                            // WriteStatus is #[non_exhaustive]; ignore.
                            info!("Write: unknown status variant");
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
        breadcrumb(0x20, iter);

        breadcrumb(0x21, iter);
        match with_timeout(
            PER_TRANSFER_TIMEOUT,
            master.write_read(ADDR, &w_buf[..write_len], &mut r_buf[..read_len]),
        )
        .await
        {
            Err(_) => wedge_panic!(
                "WEDGE: master.write_read timed out at iter={}, k={}, m={}",
                iter,
                k,
                read_len
            ),
            Ok(Err(e)) => wedge_panic!(
                "master.write_read err at iter={}, k={}, m={}: {:?}",
                iter,
                k,
                read_len,
                defmt::Debug2Format(&e)
            ),
            Ok(Ok(())) => {
                breadcrumb(0x22, iter);
                // Verify the read buffer is a monotonic increment starting
                // from `r_buf[0]`. Slave fills `t_buf[j] = (j + key) mod
                // 256` so the difference `r_buf[j] - r_buf[0]` must equal
                // `j` (mod 256) regardless of which slave iteration
                // produced the data.
                let base = r_buf[0];
                breadcrumb(0x23, iter);
                for j in 1..read_len {
                    let expect = base.wrapping_add(j as u8);
                    if r_buf[j] != expect {
                        wedge_panic!(
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
                breadcrumb(0x24, iter);
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

    let cfg = i2c::master::Config {
        speed: i2c::master::Speed::Fast,
        duty_cycle: DutyCycle::new(50).unwrap(),
        ..Default::default()
    };
    let master = I2cMaster::new_async(p.FLEXCOMM4, p.PIO0_29, p.PIO0_30, Irqs, cfg, p.DMA0_CH9).unwrap();

    spawner.spawn(slave_service(slave).unwrap());
    spawner.spawn(master_service(master).unwrap());
}
