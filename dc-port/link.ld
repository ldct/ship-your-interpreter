/* Linker script of the dc port (from c/src/link.ld). Two addresses are
 * fixed to the WHILE binary's, which the step layer (`Vsa.Sim.GoodState`,
 * `LdOK`/`StOK`, `VsaIris.MallocFast.roR`) takes as constants: `.tohost` at
 * 0x8001ad00 (`tohostAddr`; every writable byte lies above it) and gp at
 * 0x8001b510.
 * Bare-metal RISC-V on the QEMU `virt` machine.
 * RAM starts at 0x80000000; QEMU loads the ELF at its link address
 * when started with `-bios none -kernel while-riscv.elf`. */
OUTPUT_ARCH(riscv)
ENTRY(_start)

MEMORY
{
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 128M
}

__stack_size = 8M;

SECTIONS
{
    .text : {
        *(.text.init)
        *(.text .text.*)
    } > RAM

    .rodata : ALIGN(8) {
        *(.rodata .rodata.*)
        *(.srodata .srodata.*)
    } > RAM

    /* HTIF mailbox (tohost/fromhost); HTIF hosts such as Spike and the
     * sail-riscv emulators find it via the section name. */
    .tohost 0x8001ad00 : {
        *(.tohost)
    } > RAM

    .data : ALIGN(8) {
        __global_pointer$ = ABSOLUTE(0x8001b510);
        *(.data .data.*)
        *(.sdata .sdata.*)
    } > RAM

    .bss : ALIGN(8) {
        __bss_start = .;
        *(.sbss .sbss.*)
        *(.bss .bss.*)
        *(COMMON)
        . = ALIGN(8);
        __bss_end = .;
    } > RAM

    . = ALIGN(16);
    _end = .;
    PROVIDE(end = .);

    __stack_top = ORIGIN(RAM) + LENGTH(RAM);
    __heap_end = __stack_top - __stack_size;
}
