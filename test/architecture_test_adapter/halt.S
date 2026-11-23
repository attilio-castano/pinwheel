.section .text.pinwheel_halt,"ax",@progbits
.balign 4
.global pinwheel_test_halt
pinwheel_test_halt:
  ebreak
  j pinwheel_test_halt
