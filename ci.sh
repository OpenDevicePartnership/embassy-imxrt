#!/bin/bash

set -eo pipefail

if ! command -v cargo-batch &> /dev/null; then
    echo "cargo-batch could not be found. Install it with the following command:"
    echo ""
    echo "    cargo install --git https://github.com/embassy-rs/cargo-batch cargo --bin cargo-batch --locked"
    echo ""
    exit 1
fi

export RUSTFLAGS=-Dwarnings
export DEFMT_LOG=trace,embassy_hal_internal=debug
if [[ -z "${CARGO_TARGET_DIR}" ]]; then
    export CARGO_TARGET_DIR=target_ci
fi

TARGET="thumbv8m.main-none-eabihf"

BUILD_EXTRA=""

cargo batch \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time,time-driver-os-timer \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time,time-driver-os-timer,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time,time-driver-rtc \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time,time-driver-rtc,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time-driver-os-timer \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time-driver-os-timer,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time-driver-rtc \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time-driver-rtc,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time,time-driver-os-timer \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time,time-driver-os-timer,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time,time-driver-rtc \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time,time-driver-rtc,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time-driver-os-timer \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time-driver-os-timer,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time-driver-rtc \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time-driver-rtc,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time,time-driver-os-timer \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time,time-driver-os-timer,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time,time-driver-rtc \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time,time-driver-rtc,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time-driver-os-timer \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time-driver-os-timer,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time-driver-rtc \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time-driver-rtc,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time,time-driver-os-timer \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time,time-driver-os-timer,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time,time-driver-rtc \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time,time-driver-rtc,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time-driver-os-timer \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time-driver-os-timer,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time-driver-rtc \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time-driver-rtc,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time,time-driver-os-timer \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time,time-driver-os-timer,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time,time-driver-rtc \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time,time-driver-rtc,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time-driver-os-timer \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time-driver-os-timer,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time-driver-rtc \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time-driver-rtc,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time,time-driver-os-timer \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time,time-driver-os-timer,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time,time-driver-rtc \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time,time-driver-rtc,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time-driver-os-timer \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time-driver-os-timer,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time-driver-rtc \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time-driver-rtc,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time,time-driver-os-timer \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time,time-driver-os-timer,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time,time-driver-rtc \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time,time-driver-rtc,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time-driver-os-timer \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time-driver-os-timer,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time-driver-rtc \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time-driver-rtc,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time,time-driver-os-timer \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time,time-driver-os-timer,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time,time-driver-rtc \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time,time-driver-rtc,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time-driver-os-timer \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time-driver-os-timer,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time-driver-rtc \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time-driver-rtc,unstable-pac \
      --- build --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time,time-driver-os-timer \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time,time-driver-os-timer,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time,time-driver-rtc \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time,time-driver-rtc,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time-driver-os-timer \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time-driver-os-timer,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time-driver-rtc \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,time-driver-rtc,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,defmt,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time,time-driver-os-timer \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time,time-driver-os-timer,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time,time-driver-rtc \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time,time-driver-rtc,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time-driver-os-timer \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time-driver-os-timer,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time-driver-rtc \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,time-driver-rtc,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,defmt,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time,time-driver-os-timer \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time,time-driver-os-timer,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time,time-driver-rtc \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time,time-driver-rtc,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time-driver-os-timer \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time-driver-os-timer,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time-driver-rtc \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,time-driver-rtc,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,rt,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time,time-driver-os-timer \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time,time-driver-os-timer,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time,time-driver-rtc \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time,time-driver-rtc,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time-driver-os-timer \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time-driver-os-timer,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time-driver-rtc \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,time-driver-rtc,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt633s,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time,time-driver-os-timer \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time,time-driver-os-timer,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time,time-driver-rtc \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time,time-driver-rtc,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time-driver-os-timer \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time-driver-os-timer,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time-driver-rtc \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,time-driver-rtc,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,defmt,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time,time-driver-os-timer \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time,time-driver-os-timer,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time,time-driver-rtc \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time,time-driver-rtc,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time-driver-os-timer \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time-driver-os-timer,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time-driver-rtc \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,time-driver-rtc,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,defmt,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time,time-driver-os-timer \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time,time-driver-os-timer,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time,time-driver-rtc \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time,time-driver-rtc,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time-driver-os-timer \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time-driver-os-timer,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time-driver-rtc \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,time-driver-rtc,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,rt,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time,time-driver-os-timer \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time,time-driver-os-timer,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time,time-driver-rtc \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time,time-driver-rtc,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time-driver-os-timer \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time-driver-os-timer,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time-driver-rtc \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,time-driver-rtc,unstable-pac \
      --- build --release --manifest-path Cargo.toml --target thumbv8m.main-none-eabihf --features mimxrt685s,unstable-pac \
      $BUILD_EXTRA
