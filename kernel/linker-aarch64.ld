ENTRY(_start)

SECTIONS {
    . = 0x40100000;

    .text : {
        *(.text._start)
        *(.text .text.*)
    }

    .vectors : ALIGN(0x800) {
        KEEP(*(.vectors))
    }

    .rodata : {
        *(.rodata .rodata.*)
    }

    .data : {
        *(.data .data.*)
    }

    .bss : {
        *(.bss .bss.*)
    }

    /DISCARD/ : {
        *(.eh_frame)
        *(.comment)
    }
}
