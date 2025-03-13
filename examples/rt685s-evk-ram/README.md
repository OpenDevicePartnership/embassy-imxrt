# embassy-imxrt-examples

## Introduction

These examples illustrates how to use the embassy-imxrt HAL.

## Adding Examples
Add uniquely named example to `src/bin` like `adc.rs`

## Build
`cd` to examples folder
`cargo build --bin <example_name>` for example, `cargo build --bin adc`

## Run
Assuming RT685 is powered and connected to Jlink debug probe and the latest probe-rs is installed via  
  `$ cargo install probe-rs-tools --git https://github.com/probe-rs/probe-rs --locked`  
`cd` to examples folder  
`cargo objcopy --release --bin <example_name> -- -O binary <example_name>.bin`
`cargo install nxp-header --git https://github.com/OpenDevicePartnership/nxp-header.git`
`nxp-header <example_name>.bin`
`probe-rs download --chip MIMXRT685SFVKB --binary-format bin <example_name>.bin --base-address 0x08000000`
Then reset the EVK to run the program

`probe-rs attach --chip MIMXRT685SFVKB target/thumbv8m.main-none-eabihf/release/<example_name>` to see RTT traces