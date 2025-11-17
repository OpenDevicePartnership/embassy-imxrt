MEMORY {
    OTFAD     : ORIGIN = 0x08000000, LENGTH = 256,
    FCB       : ORIGIN = 0x08000400, LENGTH = 512,
    BIV       : ORIGIN = 0x08000600, LENGTH = 4,
    KEYSTORE  : ORIGIN = 0x08000800, LENGTH = 2K,
    FLASH     : ORIGIN = 0x08001000, LENGTH = 20k,
    RAM       : ORIGIN = 0x20000000, LENGTH = 4K,
    SHAREDRTT : ORIGIN = 0x20001000, LENGTH = 2K
}

SECTIONS {
    .otfad : {
        . = ALIGN(4);
        KEEP(* (.otfad))
        . = ALIGN(4);
    } > OTFAD

    .fcb : {
        . = ALIGN(4);
        KEEP(* (.fcb))
        . = ALIGN(4);
    } > FCB

    .biv : {
        . = ALIGN(4);
        KEEP(* (.biv))
        . = ALIGN(4);
    } > BIV

    .keystore : {
        . = ALIGN(4);
        KEEP(* (.keystore))
        . = ALIGN(4);
    } > KEYSTORE

    .shared_rtt : {
        . = ALIGN(4);
        KEEP(* (.shared_rtt.header))
        KEEP(* (.shared_rtt.buffer))
        . = ALIGN(4);
    } > SHAREDRTT
}
