//! Flash

/// Enable flash cache so we can execute out of flash faster
/// SAFETY: Must be called after clock is initialized or else it will hang
pub(crate) unsafe fn init() {
    critical_section::with(|_| {
        let cache64 = unsafe { crate::pac::Cache64::steal() };

        // Enable flash cache and invalidate all existing cache lines
        cache64
            .ccr()
            .write(|w| w.encache().enabled().invw0().invw0().invw1().invw1().go().init_cmd());

        let cache64polsel = unsafe { crate::pac::Cache64Polsel::steal() };

        // Set region 0 to be 0x0000_0000 to the end of flash 0x0880_0000
        cache64polsel.reg0_top().write(|w| unsafe { w.bits(0x0880_0000) });

        // Set cache policy to write-through for region 0 and non-cacheable for other regions
        cache64polsel.polsel().write(|w| {
            w.reg0_policy()
                .reg0_01()
                .reg1_policy()
                .reg1_00()
                .reg02_policy()
                .reg2_00()
        });

        // Clear instruction and data pipeline
        cortex_m::asm::dsb();
        cortex_m::asm::isb();
    })
}
