MEMORY {
	OTFAD    : ORIGIN = 0x08000000, LENGTH = 256
	FCB      : ORIGIN = 0x08000400, LENGTH = 512
	BIV      : ORIGIN = 0x08000600, LENGTH = 4
	KEYSTORE : ORIGIN = 0x08000800, LENGTH = 2K
	FLASH    : ORIGIN = 0x08001000, LENGTH = 1004K
	FLEXSPIFLASH: ORIGIN = 0x080FC000, LENGTH = 10K
	RAM      : ORIGIN = 0x20080000, LENGTH = 1536K
	FLEXSPIRAM: ORIGIN = 0x0, LENGTH = 10K
}
 
__flexspi_ram_start_addr__ = ORIGIN(FLEXSPIRAM);
__flexspi_flash_start_addr__ = ORIGIN(FLEXSPIFLASH);
__flexspi_flash_end_addr__ = ORIGIN(FLEXSPIFLASH) + LENGTH(FLEXSPIFLASH);
 
 
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
 
	.flexspi_code : { 
		* (.flexspi_code)
	} >FLEXSPIRAM AT>FLEXSPIFLASH
}