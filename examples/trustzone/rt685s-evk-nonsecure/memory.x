MEMORY {
    FLASH     : ORIGIN = 0x08040000, LENGTH = 32K
    RAM       : ORIGIN = 0x20001800, LENGTH = 1536K - 6K
    SHAREDRTT : ORIGIN = 0x20001000, LENGTH = 2K
}

SECTIONS {
    .shared_rtt : {
        . = ALIGN(4);
        KEEP(* (.shared_rtt.header))
        KEEP(* (.shared_rtt.buffer))
        . = ALIGN(4);
    } > SHAREDRTT
}
