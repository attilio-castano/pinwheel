# Timed-action engine contract

Implementation contract selected **2026-09-13**; proof and execution evidence will be recorded when checked.

This pure Lean milestone implements the [shared-engine proposal](shared-engine.md). One unchanged machine will execute separately loaded UART and SPI programs. The existing protocol specifications remain the independent contracts.

## Finite resources and instructions

The experimental instance has 32 instruction slots, three logical output bits, one logical input, eight Boolean receive slots, a five-bit program index, and an eight-bit remaining-duration counter. `Action` carries a complete output vector, a duration of 1–256 cycles encoded minus one, and an optional receive-slot destination. `Halt` completes execution. The typed format prevents invalid durations and receive destinations; it is not a binary instruction encoding or a measured hardware layout.

Logical output mapping for the examples: bit 0 = UART TX or SPI MOSI; bit 1 = SPI SCLK; bit 2 = SPI CS_N. UART holds unused SCLK low and CS_N high. UART idle is `101`, SPI idle is `100`. Physical pin assignment and output enables are outside this milestone.

## Edge and transaction semantics

An accepted start clears all receive slots and enters instruction zero on that same edge (elapsed cycle zero). Action entry captures the edge's input snapshot into its selected receive slot, updates all outputs, and begins its duration. These are simultaneous state updates, not sequential physical operations. An action lasting `D` occupies intervals `0` through `D-1`; the next instruction enters on edge `D`. There is no fetch/decode gap, including between duration-one actions.

`incoming n` is the Boolean input snapshot at edge `n`. Starting execution consumes `incoming 0`; the transition from elapsed cycle `n` to `n+1` consumes `incoming (n+1)`. Captures occur only on action entry. A repeated capture destination overwrites that slot; all other slots retain their values.

`Halt` applies the loaded idle outputs, clears busy, and exposes the receive slots as a valid result. A halt in slot zero completes immediately. A sequence that exhausts slot 31 without encountering halt faults at the end of its last action, applies idle outputs, and exposes no valid result. Faults preserve the internal receive slots for inspection but do not mark them successful.

Reset takes priority over start and input, aborts execution, clears receive slots and result status, applies the loaded idle outputs, and retains the loaded program. Starts while busy are ignored, including on the edge that completes or faults. A new start is possible on the following edge; inactive execution otherwise retains state and any completed result.

Program loading is an atomic host operation separate from clock stepping. While busy it returns rejection and leaves the whole machine unchanged. While stopped (ready, completed, or faulted), it replaces the entire program and idle profile, clears execution/result state and receive slots, and immediately applies the new idle outputs. No serial loading interface, partial writes, or simultaneous load/clock arbitration is modeled.

Program and execution state are separate. In this first compiler, the outgoing payload is expanded into literal action levels. Changing a byte therefore replaces the program. Payload registers and reuse of one protocol program across changing bytes remain a later design question.

## Intended evidence

Check general action duration, unchanged state between boundaries, capture on entry, exact sequential composition, halt/fault/reset, and loading behavior. Prove UART and SPI program observations against the existing independent specifications, including SPI receive results. Demonstrate UART → SPI → UART reloads and run boundary/noise/interface checks. No claim here covers RTL translation, synthesized area, electrical timing, or reactive protocol control flow.
