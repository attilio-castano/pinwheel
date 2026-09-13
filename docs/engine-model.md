# Timed-action engine contract

Implemented and verified **2026-09-13**: bounded engine, two protocol compilers, correctness proofs, execution checks, and reloadability demonstration.

This pure Lean milestone implements the [shared-engine proposal](shared-engine.md). One unchanged machine executes separately loaded UART and SPI programs. The existing protocol specifications remain the independent contracts.

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

## Proof structure and checked claims

`Engine/ISA.lean` owns typed instructions and bounded program storage. `Engine/Step.lean` owns clock transitions and atomic loading. `Engine/Proofs.lean` proves general engine properties. `Compile/UART.lean` and `Compile/SPI.lean` construct programs and prove their behavior.

The compiler actions compute outgoing levels from bit positions; they do not use the independent specifications' frame arrays as their generator. Each compiler has a one-step simulation proof relating engine execution to the already verified finite protocol controller. Induction extends that correspondence to every elapsed cycle. The final waveform theorems then connect to the independent protocol specifications. This explicitly reuses the existing controller proofs instead of replacing the specification with the compiler's own output.

| Claim | Checked theorem(s) |
| --- | --- |
| Within an action, only the remaining timer changes; outputs and samples retain their values. | `Engine.countdown` |
| An action enters its successor exactly after its positive duration. | `Engine.action_boundary` |
| Execution composes with the correctly shifted input history; two adjacent actions take exactly the sum of their durations. | `Engine.run_add`, `Engine.two_action_boundary` |
| An entry capture updates only the selected receive slot. | `Engine.capture_slot`, together with `enter` and the boundary theorem |
| Reset wins; busy starts are ignored; stopped execution retains its state. | `Engine.reset_priority`, `Engine.busy_ignores_start`, `Engine.stopped_retains` |
| Halt completes; falling off the last instruction faults. | `Engine.halt_entry`, `Engine.exhausted_program` |
| Busy loading leaves the entire machine unchanged; stopped loading replaces the program and resets execution. | `Engine.load_busy`, `Engine.load_stopped` |
| Compiled UART matches its independent waveform, busy duration, and completion time; incoming history cannot populate receive storage. | `Compile.UART.waveform_correct`, `busy_exact`, `result_exact`, `samples_empty` |
| Compiled SPI matches the independent three-pin waveform, sample history, received byte, and completion time. | `Compile.SPI.waveform_correct`, `samples_correct`, `received_correct`, `busy_exact`, `result_exact` |

The protocol theorems cover every byte, every configured duration from 1–256, every elapsed cycle, and arbitrary Boolean input histories. They describe uninterrupted execution following acceptance. Reset and load behavior have separate engine-level theorems; an aborted transfer is not claimed to produce a valid completed result. The SPI state correspondence maps idle after uninterrupted execution to completed status; it is not a correspondence between aborted/reset states.

`lake build` checks all modules through `Pinwheel.lean`, with warnings as errors. The axiom audit of the main general and compiler proofs found only subsets of `[propext, Classical.choice, Quot.sound]`. There are no custom axioms or unfinished proof placeholders in the library.

## Executable evidence

Run from the repository root:

```sh
lake build
lake env lean -DwarningAsError=true --run test/Engine.lean
lake env lean -DwarningAsError=true --run test/UART.lean
lake env lean -DwarningAsError=true --run test/SPI.lean
```

The engine suite checks 2,560 compiled protocol transfers:

- UART: all 256 bytes at durations 1, 4, and 256, with changing incoming data (768 transfers).
- SPI: all 256 transmitted bytes paired with complement replies at half-durations 1, 4, and 256, with both quiet and noisy off-edge inputs (1,536 transfers).
- SPI: fixed TX `0x53` and all 256 possible replies at half-duration 1 (256 transfers).

This covers every TX and RX value at each selected duration, not every Cartesian TX/RX pair. Every transfer checks independent cycle-level outputs, exact busy/result timing, received byte, reset priority, ignored busy starts including completion, and result retention.

Additional engine cases check:

- A non-protocol sequence with action durations `1,4,256,1`, changing all output bits, sampling at edges `0,1,5`, and overwriting a receive slot. It completes at cycle `262`; changing inputs between entries has no effect on samples.
- Halt in slot zero, successful halt in slot 31, fall-through from a duration-one action in slot 31, fault persistence, restart, and loading from completed/faulted state.
- UART → SPI → UART using one `Machine` value and unchanged transition function. SPI receives `0xff`; loading UART clears that data and its valid status. Busy loading is rejected at every cycle of a 68-cycle SPI transfer, including the state immediately before completion. Reset and subsequent loading/restart are checked at each of those cycles.

The traces are `build/engine/uart-0x53-4cycles.csv` and `build/engine/spi-0x53-rx0xa6-4cycles.csv`. They describe logical output intervals and edge-indexed inputs. An independent CSV comparison matched all 42 UART rows and every common field in all 70 SPI rows against the fixed-controller traces. Literal SPI transmitted/received bits were also checked as `01010011`/`10100110`, with result `166` valid at cycle `68`. CSV and scratch proof files remain ignored generated artifacts.

A deliberately false scratch theorem claimed that two duration-one actions were already completed at cycle one. Lean rejected it because the proposition is false. The existing fixed UART (768 transfers) and SPI (1,792 transfers) suites also passed as regressions.

## Program cost and next questions

Both programs occupy the same 32-slot store. UART uses 10 actions and reaches halt in slot 10 (11 used instructions); SPI uses 17 actions and reaches halt in slot 17 (18 used instructions). Remaining memory is padded with halt. These counts are checked by the executable suite. There is no chosen binary word size, storage bit count, synthesized area, or clock-rate result yet.

The experiment establishes a reusable timed-action engine for these fixed schedules. It does not yet separate payload data from program instructions, branch on received inputs, wait conditionally, or control line release. The next design review should examine those needs before extending the instruction set. The exact no-gap timing promise also creates a concrete fetch/decode obligation for a later hardware implementation.

No claim here covers RTL translation, synthesized area, electrical timing, or reactive protocol control flow.
