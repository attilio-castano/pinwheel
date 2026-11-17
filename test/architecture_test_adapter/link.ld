OUTPUT_ARCH("riscv")
ENTRY(rvtest_entry_point)
MEMORY {
  rom (rx) : ORIGIN = 0x00000000, LENGTH = 0x00400000
  ram (rw) : ORIGIN = 0x01000000, LENGTH = 0x00100000
}
SECTIONS {
  .text.init 0 : { *(.text.init) } > rom
  .text.rvtest : { *(.text.rvtest) *(.text.rvtest.*) } > rom
  .text.rvmodel : { *(.text.rvmodel) *(.text.rvmodel.*) *(.text) *(.text.*) } > rom
  .rodata : { *(.rodata) *(.rodata.*) *(.srodata) *(.srodata.*) } > rom
  .data 0x01000000 : { *(.data) *(.data.*) *(.sdata) *(.sdata.*) } > ram
  .bss : { *(.sbss) *(.sbss.*) *(.bss) *(.bss.*) *(COMMON) } > ram
  ASSERT(. <= ORIGIN(ram) + LENGTH(ram), "RAM overflow")
}
