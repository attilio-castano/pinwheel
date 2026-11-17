/* Pinwheel ACT4 EEI adapter. Upstream test bodies/headers remain unchanged. */
#ifndef _RVMODEL_MACROS_H
#define _RVMODEL_MACROS_H
/* Use the identical explicit EEI in signature generation and self-check mode. */
#define _SAIL_MACROS_H
#define RVMODEL_BOOT_TO_MMODE
#define RVMODEL_DATA_SECTION
#define RVMODEL_HALT_PASS li a0, 1; j pinwheel_test_halt
#define RVMODEL_HALT_FAIL li a0, 3; j pinwheel_test_halt
/* Diagnostic console is optional. Pass/fail is always checked independently. */
#define RVMODEL_IO_WRITE_STR(_R1,_R2,_R3,_STR_PTR)
#define RVMODEL_INTERRUPT_LATENCY 1
#define RVMODEL_TIMER_INT_SOON_DELAY 100
#define RVMODEL_SET_MEXT_INT(_R1,_R2) .error "interrupts excluded"
#define RVMODEL_CLR_MEXT_INT(_R1,_R2) .error "interrupts excluded"
#define RVMODEL_SET_MSW_INT(_R1,_R2) .error "interrupts excluded"
#define RVMODEL_CLR_MSW_INT(_R1,_R2) .error "interrupts excluded"
#define RVMODEL_SET_SEXT_INT(_R1,_R2) .error "interrupts excluded"
#define RVMODEL_CLR_SEXT_INT(_R1,_R2) .error "interrupts excluded"
#define RVMODEL_SET_SSW_INT(_R1,_R2) .error "interrupts excluded"
#define RVMODEL_CLR_SSW_INT(_R1,_R2) .error "interrupts excluded"
#endif
