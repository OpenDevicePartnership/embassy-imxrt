#!/bin/bash
set -e

pushd rt685s-evk-secure > /dev/null
cargo build --release
popd > /dev/null

probe-rs download --chip MIMXRT685SFVKB --preverify --verify  target/thumbv8m.main-none-eabihf/release/secure-app

pushd rt685s-evk-nonsecure > /dev/null
cargo run --release --bin $1
popd > /dev/null
