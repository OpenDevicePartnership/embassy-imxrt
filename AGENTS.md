# AGENTS.md — embassy-imxrt

Operational guide for AI coding agents working on `embassy-imxrt`, the Embassy
Hardware Abstraction Layer (HAL) for NXP iMXRT MCUs (currently MIMXRT685S and
MIMXRT633S). Human contributors should read `CONTRIBUTING.md` and `README.md`.

This file complements `.github/copilot-instructions.md` (commit-message and
AI-attribution rules) — read both.

---

## 1. Repository layout

```
.
├── Cargo.toml                       # the HAL crate
├── ci.sh                            # full feature-matrix build (cargo-batch)
├── clippy.toml, rustfmt.toml, deny.toml
├── src/
│   ├── lib.rs                       # crate root + #![no_std], chip gate
│   ├── chips/{mimxrt633s.rs, mimxrt685s.rs}   # per-chip wiring (selected by feature)
│   ├── fmt.rs                       # defmt/log/no-log macro shims (MUST stay first)
│   ├── adc.rs, clocks.rs, crc.rs, espi.rs, flash.rs, flexcomm.rs,
│   ├── gpio.rs, iopctl.rs, pwm.rs, rng.rs, rtc.rs, spi.rs, uart.rs,
│   ├── uuid.rs, wwdt.rs, timer.rs
│   ├── dma/, flexspi/, hashcrypt/, i2c/, time_driver/
├── examples/
│   ├── rt685s-evk/                  # MIMXRT685S-EVK example binaries
│   ├── rt633/                       # MIMXRT633S example binaries
│   └── rt685s-evk-performance-tracing/
├── .github/workflows/               # check.yml, nostd.yml, rolling.yml, cargo-vet*.yml
└── .github/copilot-instructions.md  # commit & attribution rules
```

This is **not** a Cargo workspace. The HAL crate at the repo root and each
`examples/<board>` crate are independent Cargo projects with their own
`Cargo.lock` and `rust-toolchain.toml`. Run `cargo` commands from the
appropriate directory.

---

## 2. Chip / feature model (read before touching `Cargo.toml` or `cfg`)

`src/lib.rs` enforces:

```rust
#[cfg(not(any(feature = "mimxrt633s", feature = "mimxrt685s")))]
compile_error!("No chip feature activated. ...");
```

Rules an agent must respect:

* **Exactly one chip feature** must be enabled per build:
  `mimxrt685s` *xor* `mimxrt633s`. Never enable both. The check workflows
  always run each combination separately.
* Public chip features `mimxrt685s` / `mimxrt633s` activate the matching PAC
  (`mimxrt685s-pac` / `mimxrt633s-pac`) **and** an internal underscore feature
  (`_mimxrt685s`, `_mimxrt633s`). Use the underscore features (or `cfg(feature
  = "_espi")` etc.) inside `src/` to gate code on chip family/peripheral.
* Peripheral availability is gated via underscore features (e.g. `_espi` is
  enabled only by `_mimxrt633s`). When adding a peripheral that is not on all
  chips, add a new `_<peripheral>` feature in `Cargo.toml`, activate it from
  the appropriate `_mimxrt*` feature, and gate the module in `src/lib.rs`.
* Time drivers are mutually exclusive: `time-driver-os-timer` (1 MHz OS timer)
  *xor* `time-driver-rtc` (32 kHz RTC). Both imply the internal `_time-driver`
  feature. `time-driver` is a deprecated alias for `time-driver-rtc`; do not
  use it in new code. When `time-driver-rtc` is on, `pub mod rtc` is **not**
  compiled (the RTC is owned by the driver).
* `rt` enables the cortex-m runtime via the PAC; it is on by default.
* `unstable-pac` re-exports `chip::pac` as `embassy_imxrt::pac`. Without it,
  the PAC is `pub(crate)`. Do not rely on PAC symbols from public API.
* `defmt` and `log` are independent logging backends consumed by `src/fmt.rs`.
  Never `use defmt::*` or `use log::*` directly in modules — go through the
  macros in `fmt.rs` so both backends and the "no logging" build keep working.
* Features must be **strictly additive** (cargo-hack contract). Adding a
  feature that removes/changes behaviour of another build will break the
  `hack` CI job.

The chip module is selected by `#[cfg_attr]` on `mod chip;` in `lib.rs` — do
not change its ordering relative to the `impl_foo!` macro uses; the comment
"MUST go last" is load-bearing. Likewise `pub(crate) mod fmt;` must stay
first.

Target triple is **`thumbv8m.main-none-eabihf`** for every build of the HAL
crate. The examples crates pin their toolchain via
`examples/<board>/rust-toolchain.toml`.

---

## 3. Build, lint, test — exact commands used by CI

All commands below match what runs in `.github/workflows/` and `ci.sh`.
Agents should run at least the relevant subset before declaring a change
done. Long compiles are expected (~5–10 min cold per feature combo).

### 3.1 Format (`check.yml` job `fmt`, **nightly**)

`rustfmt.toml` uses `imports_granularity` and `group_imports`, which are
**nightly-only**. On stable, `cargo fmt --check` silently warns and exits 0;
CI runs nightly and will fail on real formatting differences. Run:

```powershell
# Repo root and each examples crate (matches the CI matrix)
cargo +nightly fmt --check
cd examples/rt633          ; cargo +nightly fmt --check ; cd ../..
cd examples/rt685s-evk     ; cargo +nightly fmt --check ; cd ../..
```

If nightly is unavailable, prefer formatting via your editor's rustfmt
configured to nightly — do not "fix" formatting by removing the
`imports_granularity`/`group_imports` settings.

### 3.2 Clippy on examples (`check.yml` job `clippy-examples`, stable)

```powershell
cd examples/rt633
cargo clippy --locked -- -Dwarnings -D clippy::suspicious -D clippy::correctness -D clippy::perf -D clippy::style
cd ../rt685s-evk
cargo clippy --locked -- -Dwarnings -D clippy::suspicious -D clippy::correctness -D clippy::perf -D clippy::style
```

### 3.3 HAL clippy (run as part of `ci.sh`, stable)

```powershell
$env:RUSTFLAGS = "-Dwarnings"
cargo clippy --locked --target thumbv8m.main-none-eabihf `
  --features "mimxrt633s,rt,time-driver-os-timer,unstable-pac" -- -Dwarnings
cargo clippy --locked --target thumbv8m.main-none-eabihf `
  --features "mimxrt633s,rt,time-driver-rtc,unstable-pac" -- -Dwarnings
```

The crate-level `[lints.clippy]` in `Cargo.toml` denies
`expect_used`, `unwrap_used`, `panic`, `panic_in_result_fn`,
`indexing_slicing`, `todo`, `unimplemented`, `unreachable`, plus the standard
`correctness`/`perf`/`style`/`suspicious` groups. Don't disable these crate-
wide. Prefer locally-scoped `#[allow(...)]` with a justification comment when
truly necessary (see e.g. `pub mod espi` gated with
`#[allow(clippy::indexing_slicing)]`).

### 3.4 Docs (`check.yml` job `doc`, **nightly**)

```powershell
$env:RUSTDOCFLAGS = "--cfg docsrs"
cargo +nightly doc --no-deps --locked `
  -F mimxrt685s,rt,defmt,time,time-driver-os-timer,unstable-pac
cargo +nightly doc --no-deps --locked `
  -F mimxrt633s,rt,defmt,time,time-driver-os-timer,unstable-pac
```

Public items have `#![warn(missing_docs)]` — add doc comments on any new
public item.

### 3.5 Feature-matrix build (`check.yml` job `hack`, stable)

The full matrix lives in `ci.sh` and is driven by `cargo-batch`:

```powershell
cargo install --git https://github.com/embassy-rs/cargo-batch cargo --bin cargo-batch --locked
bash ./ci.sh      # ~96 dev+release combos × 2 chips, plus the two clippy commands
```

If `cargo-batch` is unavailable, at minimum reproduce the per-feature combos
the workflow cares about by iterating over the `FEATURE_COMBINATIONS` list in
`ci.sh` with plain `cargo build --target thumbv8m.main-none-eabihf
--features "<combo>"`. Don't edit `ci.sh` to skip combos to make CI pass.

### 3.6 `no-std` smoke check (`nostd.yml`, stable)

```powershell
rustup target add thumbv8m.main-none-eabihf  # one-time
cargo check --target thumbv8m.main-none-eabihf --no-default-features -F mimxrt685s --locked
cargo check --target thumbv8m.main-none-eabihf --no-default-features -F mimxrt633s --locked
```

### 3.7 MSRV (`check.yml` and `rolling.yml`)

MSRV is **1.90** (rationale documented inline in both workflows — `fixed`,
`embedded-hal-async`, `embassy-time`, `embedded-services`, and
`unsigned_is_multiple_of` set the floor). Don't bump it without updating both
workflow files and noting the reason.

```powershell
cargo +1.90 check -F mimxrt685s,rt,defmt,time,time-driver-os-timer,unstable-pac --locked
cargo +1.90 check -F mimxrt633s,rt,defmt,time,time-driver-os-timer,unstable-pac --locked
```

### 3.8 Supply chain (`check.yml` job `deny`, `cargo-vet*.yml`)

```powershell
cargo deny --manifest-path ./Cargo.toml check --all-features --locked
```

`cargo-vet` runs via the dedicated workflows; agents normally don't need to
re-run it locally, but do not delete entries in `supply-chain/`.

### 3.9 Tests

There is no `cargo test` job — the crate is `#![no_std]` for an embedded
target, and `[dev-dependencies]` only pull in `embassy-executor` and
`static_cell`. Per `CONTRIBUTING.md`, **new HAL drivers must come with an
example binary** under `examples/rt685s-evk/src/bin/` and/or
`examples/rt633/src/bin/` that exercises them on the EVK.

---

## 4. Coding conventions specific to this crate

* `#![no_std]`. No `std`, no `alloc` unless behind a feature you also add.
* All logging through `src/fmt.rs` macros (`info!`, `warn!`, `unwrap!`,
  `assert!`, etc.). `defmt` and `log` features are mutually compatible only
  via this shim.
* Public APIs that take peripherals use `embassy_hal_internal::Peri<'d, T>`
  (re-exported as `embassy_imxrt::Peri`). Singletons live in
  `embassy_imxrt::peripherals` (generated by chip-module macros).
* Interrupt handlers use the `embassy_hal_internal::interrupt::typelevel`
  machinery; the helper `__handle_interrupt` in `lib.rs` wraps optional
  systemview tracing — use it from generated handlers, don't open-code it.
* Implement embedded-hal traits across the matrix: `embedded-hal` 0.2 *and*
  1.0, plus `embedded-hal-async`, `embedded-hal-nb`, `embedded-io`, and
  `embedded-io-async` where applicable. Existing drivers (e.g. `i2c`, `spi`,
  `uart`) are the reference.
* DMA APIs live in `src/dma/`. Buffer-lifetime, `OnDrop` cleanup, and
  cancellation-safety patterns from upstream Embassy HALs apply — review
  `src/dma/` and existing peripherals (`uart`, `spi`, `i2c`) before adding a
  new DMA-capable driver.
* For new peripherals, follow the existing structure: `Info` / sealed
  `Instance` trait / mode type-state / pin trait macros / interrupt binding
  via `bind_interrupts!`. Wire instances in `src/chips/<chip>.rs`.
* Prefer `cfg(feature = "_<peripheral>")` over `cfg(feature = "mimxrt6XXs")`
  inside `src/` so that peripheral availability is encoded once.
* `unsafe` is unavoidable; per `CONTRIBUTING.md`, wrap it in safe interfaces
  and keep `unsafe` blocks small and commented.

---

## 5. Commits, branches, PR flow

`.github/copilot-instructions.md` (read it) is authoritative for commit
messages and AI attribution. Key points an agent must enforce on itself:

* **Subject:** capitalized, imperative, ≤ 50 chars. Blank line. Body wrapped
  at 72 cols, explaining *what* and *why*.
* Every AI-assisted commit **must** carry an `Assisted-by:` trailer of the
  form `Assisted-by: GitHub Copilot:<model-version> [tool1] [tool2]`. The
  agent must verify its own model identity per session before composing this
  trailer.
* AI agents **must not** add `Signed-off-by` lines — only humans certify the
  DCO.
* Squashing is disabled. Keep commits logically separated; each commit must
  build cleanly with no `rustc` or `clippy` warnings.
* Branch naming: `user_alias/feature` style. Avoid `wip`/`test` prefixes.
* Open a **draft PR first**, and let the `.github` workflows pass on the
  draft before requesting review. Use the `RFC:` title prefix for design
  RFCs.
* When fixing a regression, use `git bisect` to identify the first bad
  commit and reference it in the PR.

When committing programmatically, set the author per-commit, never globally:

```powershell
git -c user.name="Felipe Balbi" -c user.email="felipe.balbi@microsoft.com" `
    commit -m "Subject" -m "Body" -m "Assisted-by: GitHub Copilot:<model>"
```

---

## 6. Things to avoid

* Enabling both chip features simultaneously, or both time drivers
  simultaneously.
* Removing or weakening the `compile_error!` guard in `src/lib.rs`.
* Reordering `mod fmt;` (must be first) or `mod chip;` (must be last) in
  `src/lib.rs`.
* Using `defmt`/`log` directly from drivers instead of `fmt.rs` macros.
* Adding `expect`, `unwrap`, `panic!`, `todo!`, `unimplemented!`,
  `unreachable!`, or raw indexing on slices — they are denied crate-wide.
* Bumping MSRV without updating both `check.yml` and `rolling.yml` matrices
  and the explanatory comments.
* Editing `ci.sh` to drop feature combinations or relax `-Dwarnings`.
* Force-pushing or squashing on shared branches.
* Re-exporting PAC types from public APIs (gate behind `unstable-pac` if
  unavoidable).
* Touching `Cargo.lock` of either examples crate just to silence
  `--locked` — investigate the real version drift first.
