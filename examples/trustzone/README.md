# Trustzone for IMXRT6xx
This example uses the nightly compiler the `abi_cmse_nonsecure_call` and `cmse_nonsecure_entry` features.

It is split into two parts:
* a Secure mode mini 'bootloader' that runs in XIP mode and configures all busses and the core. It has a small veneer with the `do_stuff_secure` function that is callable from the NonSecure mode. All peripherals are set to NonSecure, with the notable exception being the OTP peripheral.
* a collection of NonSecure binaries that showcase TrustZone.

It is imperative that the secure firmware is compiled first.
It places a `veneers.o` in the target folder.
The nonsecure links that in to be able to call secure functions.

For copy-to-ram mode the secure part should be configured quite differently.

In order to quickly run this example, call `run.sh secure_function`, or use any other binary in `rt685s-evk-nonsecure/src/bin`.
