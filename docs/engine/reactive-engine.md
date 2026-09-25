# Candidate engine: drive, observe, wait, then time

Implementation record: **2026-09-13**. The next pure Lean milestone is implemented in `Pinwheel.Engine.Reactive`: three output values with independent drive enables, two observed inputs, selected-input capture, and a bounded wait instruction. A five-slot program emits one stretched clock pulse. This is a candidate extension of the [shared engine](engine-model.md), with a proved embedding of every existing typed program. The existing 16-bit encoding and structural hardware still implement the original engine.

Follow-up: [compiled I²C](../protocols/compiled-i2c.md) now adds guarded timing, terminal capture/branching, input qualification, and complete write correspondence. The candidate bank has expanded to 128 slots with a per-program last address. This page retains the pulse experiment's timing/evidence; the compiled-I²C record owns the additional operations and storage decision.

## Instruction and interface contract

```text
Action(pin commands, duration, optional input/destination capture)
Wait(pin commands, input/value condition, blocked-observation budget)
Halt
```

Programs now have 128 typed slots, a last executable address, and an idle pin-command profile. Embedded original programs and the pulse retain last address 31. Duration and wait budget each range from 1 to 256. The later `Checked` and `Qualify` operations add guarded timing, terminal capture, jumps/branches, and consecutive input qualification; see the compiled-I²C contract. This explicit engine has no arithmetic instructions or separate payload registers. The [counted-store follow-up](../protocols/looped-i2c.md) adds separate byte data, and [PWL v0](../storage/binary-images.md) now serializes both forms. A new circuit word format remains open.

`Pins.levels` holds three output values; `Pins.enabled` selects which drivers are enabled. Disabled outputs are released. `Inputs` contains two independently observed Boolean levels. The transition function never substitutes a commanded output for an observed input.

`Pins.pushPull` enables all outputs and is used by the compatibility embedding. `Pins.openDrain` fixes output values to zero and enables only the chosen low drivers. Its theorem establishes that this constructor never commands an active high. The generic machine also accepts push-pull commands; it does not infer or enforce a protocol mode. Open-drain safety depends on the chosen program, including its idle profile. The pulse checks inspect every command for active-high drive and keep the unassigned third output released.

Entry to an `Action` updates commands and optionally captures a selected input from that edge's input snapshot. Commands are retained for its full duration; its successor enters at the terminal edge. This preserves the old timing convention. A terminal observation can be captured by the next action on that boundary, as the pulse's falling-clock action demonstrates.

Entry to `Wait` applies its commands and loads its budget, without consuming the entry-edge input. That snapshot preceded the new commands and cannot establish the effect of releasing a line. Subsequent observations behave as follows:

- A matching input enters the next instruction on the same observation edge. The next timed action loads its full duration and any capture uses this edge's input.
- A blocked observation decrements only the wait counter. Pin commands, samples, and the program index stay unchanged.
- Readiness wins when the counter is zero. Persistent blocking stops on the `W`th blocked observation; at most `W - 1` blocked observations can precede readiness.

Wait completion at the last slot faults instead of wrapping. A waiting state whose program slot is not a wait also faults. Timeout is a distinct stopped status and does not expose a successful result. All stopped states retain their state until reset, start, or accepted loading.

Reset has priority, clears samples and status, and restores the program's idle profile. Busy starts are ignored, including during waits and on completion edges. Atomic program replacement is accepted only while stopped and resets the execution state. Timeout and faults restore the idle commands and preserve captured samples internally. Thus the pulse's idle profile releases all lines, while an embedded UART/SPI program preserves its original idle behavior. No abort can force an externally held line high.

## Concrete pulse and observation edge

`Compile.StretchedPulse.program` assigns output/input 0 to SCL and 1 to SDA. It contains setup-low, wait-for-SCL-high, timed-high, timed-low with SDA capture, and halt. The remaining slots are halt. Both data values use open-drain commands.

For phase duration `H`, budget `W`, and `B < W` blocked observations after clock release:

| Elapsed edge | Program behavior |
| --- | --- |
| `0` | Enter setup; pull SCL low and establish SDA. |
| `H` | Enter wait and release SCL. |
| `H + B + 1` | Consume the first ready observation; enter high with a fresh duration. |
| `2H + B + 1` | Enter low and capture SDA from this edge's pre-update snapshot. |
| `3H + B + 1` | Halt, restore released idle pins, and expose captured data. |

In the emitted example, `H=4`, `W=8`, `B=3`: SCL is released at edge 4; the target holds it low for observations 4–6. The resolved line is high in observation 7, consumed at edge 8. The full four-cycle timer runs from edge 8 to edge 12, when SDA is captured and SCL is pulled low. Completion is edge 16. Without stretching, completion would be edge 13.

The CSV row at cycle `t` shows post-edge commands and their resolved bus; that observation feeds the transition to `t+1`. Consequently external SCL can be high one cycle before the timed-high action begins. The guarantee is an exact internal duration after observed readiness, with an external high interval at least that long under the test's stable-high target assumption.

This pulse has no START, address, ACK decision, or STOP. It is a timing experiment, not a complete I²C transaction. Its ordinary timed actions do not monitor continued readiness. The later checked-action variant supplies that guard for complete I²C programs and now matches the reference's bus-fault behavior.

## Proof and execution evidence

The initial milestone's thirty theorems cover two boundaries below. The current audit has 38 after adding guard, branch, and qualification theorems; the compiler has a separate 29-theorem audit.

1. **Legacy compatibility:** all original typed programs, states, and input histories embed into the candidate engine with identical pin values, fully enabled outputs, samples, busy/result status, and execution-edge behavior. Reset/start priority and accepted/rejected loads are preserved. The first observed input carries the original input; the second may vary arbitrarily. Composed corollaries establish UART and SPI waveforms and SPI samples against their existing specifications.
2. **Wait and timed execution:** blocked-prefix retention, exact timeout, ready-at-deadline priority, exact continuation, timed countdown and boundaries, and their composition. `wait_then_timed` proves that `B` blocked observations followed by readiness anchor a complete action duration at observation `B + 1`. Interface lemmas cover wait entry, reset, busy starts, and loading.

Dependencies are limited to standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) or none. There are no unfinished-proof or custom axioms. These are model theorems; no new structural-circuit or emitted-RTL correspondence is claimed.

The executable suite passed:

- **1,024 pulse cases across 528,384 observations:** every duration 1–256, both data values, and zero or 255 blocked observations with budget 256. The oracle uses arithmetic deadlines and separate bus resolution, without inspecting the candidate's control state to derive expected pulse timing.
- All 256 budgets and durations with both observed-input selectors and both target polarities; readiness at every surviving wait position, fresh duration, selected capture, timeout, restart/reload, invalid waiting state, and last-slot handling.
- **1,024 UART/SPI transfers** at durations 1 and 4 across every payload, compared both with original engine execution and independent waveform/sample specifications. The compatibility proofs cover the broader parameter ranges and arbitrary histories.
- UART → SPI → stretched pulse → UART on one candidate machine through stopped program replacement. Pulse runs also check reset priority and busy start/load rejection at every active observation.
- Three faulty transitions rejected for their expected assertion: ignoring readiness, shortening the post-wait timer, and losing captured data.

Pulse observation counts exclude separate boundary checks, legacy transfers, mixed reloads, negative variants, and the example trace. The library build passed with 32 jobs. Existing hardware sources and encoding were unchanged; prior RTL/synthesis receipts identify their own source snapshots and do not validate this extension.

Reproduce with Lean and Python only:

```sh
python3 scripts/check-reactive.py
```

The runner builds, audits all 38 named theorems, executes the pulse/legacy suite and `test/Control.lean`, and publishes source/artifact hashes in ignored `build/reactive/report.json` only on success. Logs, `coverage.txt`, and `stretched-pulse.csv` accompany it. Direct executable/audit entry points are `test/Reactive.lean`, `test/Control.lean`, and `test/ReactiveAxioms.lean` through `lake env lean -DwarningAsError=true` after building.

## Next bounded step

Conditional continuation, qualification, guarded phases, and complete [I²C compilation](../protocols/compiled-i2c.md) are now implemented with reference correspondence. Reset remains the engine's status-clearing interface, separately documented from the reference's `resetAbort` result.

The expansion is 79 typed instructions. A [counted store](../protocols/looped-i2c.md) now uses 15 templates plus loop structure and two data bytes, with complete-state equality and unchanged modeled timing. [PWL v0](../storage/binary-images.md) now measures full serialized footprints and proves decoded execution. Compare physical record layouts and decoder costs with the explicit bank before freezing the circuit representation. Then extend the structural decoder, scheduler, pin-enable registers, and storage, followed by refinement proofs, RTL checks, fault injections, and synthesis. Translation/equivalence, physical loading, synchronization, and electrical timing remain separate obligations in the [processor plan](processor-verification.md).
