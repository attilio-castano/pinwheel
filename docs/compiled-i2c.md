# I²C programs on the candidate Lean engine

Implementation record: **2026-09-13**. The [candidate reactive engine](reactive-engine.md) now executes the [I²C reference](i2c-model.md)'s address-plus-byte write as a loaded program. It handles ACK/NACK, clock stretching, bus-free qualification, clock-high faults, and STOP/error paths. The original encoded UART/SPI hardware is unchanged. The later [PWL v0 format](binary-images.md) encodes candidate programs with round-trip and execution proofs; the later [E64 frontends](execution-hardware.md) implement the wider decoder and stores, while the extended structural scheduler remains pending.

## General operations added

The engine keeps ordinary `Action`, `Wait`, and `Halt` instructions and adds two operations:

- **`Checked`:** a timed action with a masked input guard, optional terminal capture, and a successor choice. Every execution edge checks the guard first. Failure restores the idle commands and faults without capturing. On the terminal edge, capture occurs first, then the successor is selected from the updated samples. The successor can be sequential, an explicit jump, or a branch on a stored sample. Its entry occurs on that same edge, including any entry capture it specifies.
- **`Qualify`:** apply pin commands and require an input condition for a consecutive duration. A blocked observation resets the duration counter and consumes the wait budget. A ready observation advances the duration and refreshes the wait budget; readiness wins at the deadline. This implements initial bus-free qualification.

Both operations use the same two observed inputs and three output value/enable pairs as the pulse experiment. Checked guards are evaluated after entry, on subsequent execution edges. The compiler enters clock-high phases only after a preceding ready observation. No hardware path calls the I²C reference controller: the shared transition function interprets general instructions and knows nothing about I²C addresses, bytes, ACKs, or STOP.

Branch targets are bounded addresses and must also fall within the loaded program's execution limit. An invalid target faults. Terminal capture precedes target validation, so the captured value remains available internally on that fault. A malformed checked/qualifying state whose slot contains another instruction also faults. Busy starts and program replacement remain rejected; reset retains its existing priority.

## Program layout and capacity decision

The fully expanded write needs **79 instructions**, including halt:

| Slots | Purpose |
| --- | --- |
| 0 | Qualify both observed lines high. |
| 1 | START hold, guarded by observed SCL high. |
| 2–73 | Eighteen clocks, with setup, wait-for-rise, guarded high, and low hold per clock. |
| 74–77 | STOP low, wait for SCL high, guarded STOP setup, and guarded bus-free hold. |
| 78 | Halt and expose the result. |

Address ACK is captured from SDA on the terminal edge of slot 36 into sample 0. Slot 37 holds SCL low, then branches to STOP at slot 74 on NACK or payload setup at slot 38 on ACK. Data ACK is captured into sample 1; the final low hold proceeds to STOP for either outcome. Completion distinguishes success, address NACK, and data NACK from those flags. Engine timeout and fault map to reference timeout and bus fault for this well-formed program.

The original 32-slot capacity cannot contain this expansion. The Lean candidate therefore has a **128-slot bounded bank plus a per-program last address**. This compiler sets the last address to 78 and pads remaining storage with halt. Embedded original programs retain last address 31, preserving their exhaustion behavior; the compatibility proof includes that boundary. The pulse program also retains its 32-slot execution limit.

This is an experiment capacity, not a hardware memory allocation or area result. Literal expansion makes timing and correspondence explicit but stores payload bits in instruction contents. The follow-up [counted byte loop](looped-i2c.md) stores 15 templates, two repeat descriptors, and two data bytes, with proved complete-state equality. It derives loop indices from the existing execution PC, adding selection logic without extra modeled cycles. The [V0 image comparison](binary-images.md) now reports 715 bytes explicit versus 205 counted. The subsequent [E64 hardware comparison](execution-hardware.md) measures allocated storage and generic synthesized cost for direct and indexed literal stores. Multiplying the new slot count by the old 16-bit word width would be misleading: the old encoding cannot express these instructions.

## Formal correspondence

`I2CPhases.lean` defines a relation between reference phases and concrete program counters, timers, pin commands, and ACK sample flags. It proves one-edge correspondence for each phase. The relation allows captured data to remain internally after abort, while the reference records the abort outcome.

`I2CProofs.lean` composes those phase proofs into `run_simulation`. For every bounded configuration, request, sampled input history, and elapsed cycle, execution of the compiled image corresponds to execution of the fixed I²C reference. Corollaries establish:

- Identical drive/release commands on SDA/SCL, with the unused output released.
- Identical busy status and decoded success, NACK, timeout, or bus-fault result.
- The same capture, wait, STOP, and fault boundaries, including after completion.

The theorem uses the same edge-indexed input history on both machines and does not assume that history is electrically legal. It does not assert that arbitrary inputs lead to success. In particular, intermittent interference during qualification may prevent termination indefinitely. A universal liveness theorem for a cooperating target is not part of this milestone.

**Reset boundary:** the full-run theorem has no reset, new start, or program replacement during execution. The engine's reset contract clears status/samples and restores idle commands; the fixed I²C reference reports `resetAbort`. They agree on release behavior but have different result interfaces. A separate compiled reset theorem proves release, and generic engine proofs retain reset priority and stopped loading. The original UART/SPI embedding and its waveform/sample corollaries still pass on the widened candidate.

The compiler audit covers **29 public theorems**, including the reference wire-order theorem and the new phase/run/observation claims. Dependencies are limited to standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) or none. The generic reactive audit covers **38 theorems** after adding guard, branch, and qualification claims. There are no unfinished proofs or custom axioms. These guarantees concern Lean models; emitter correctness, circuit refinement, RTL behavior, synchronization, electrical timing, and area remain separate boundaries.

## Executable evidence and reproduction

The compiled suite passed **4,224 transactions across 822,896 observed cycles**, using the same payload/address/duration/stretch matrix as the reference experiment. At every cycle it compares pin commands, busy status, and results with the reference. A separate monitor derives bits, ACK slots, START/STOP, and timing from resolved wire transitions, with actual drive commands supplied by the compiled engine.

The example at address `0x53`, payload `0xA6`, duration 4 and wait budget 8 completes in **255 cycles** without stretching and **282 cycles** with the selected stretches. Additional checks fork each example observation into all four sampled-input values and hold them through timing/wait boundaries to compare error paths. These injections test digital input semantics, including histories that would not describe a cooperating physical target.

Three corrupted programs were rejected: missing ACK capture, ignored NACK branch, and early ACK capture. The early-capture case needs input changes near the capture boundary; a constant ACK value alone cannot distinguish it. A mixed UART → SPI → I²C address-NACK/STOP → UART sequence passes through stopped program replacement on one candidate machine. The broader I²C matrix separately covers successful writes and data NACK.

The generic suite also passes all 256 checked durations and qualification budgets, terminal capture/branch ordering, guard/reset priority, interrupted qualification, malformed states, invalid targets, 1,024 pulse cases, and 1,024 UART/SPI transfers. Transaction/observation totals exclude these additional suites, error forks, negative variants, mixed reloads, and example runs. The full library build passes with 36 jobs.

```sh
python3 scripts/check-compiled-i2c.py
python3 scripts/check-reactive.py
```

Only the installed Lean toolchain and Python are required. The compiled runner writes logs, the stretched CSV, coverage, theorem audit, and source/artifact hashes under ignored `build/compiled-i2c/`; the generic runner uses `build/reactive/`. Each removes its previous success receipt before starting and publishes `report.json` only after its checks pass. Earlier I²C and hardware receipts identify earlier snapshots; no RTL or synthesis flow was rerun for this pure Lean batch.

## Next hardware-facing decision

The [byte-loop comparison](looped-i2c.md) now establishes instruction reuse, supported bounds, and exact cycle preservation. The [V0 image milestone](binary-images.md) now supplies codec proofs and exact byte costs. The [E64 layout](execution-records.md) now selects load-time lowering into literal records, and its [decoder/store circuits](execution-hardware.md) have proofs, RTL checks, and generic synthesis measurements. Next connect those frontends to structural qualification/wait counters, guard and branch logic, pin-enable registers, and capture state, then prove that complete circuit implements the reactive semantics. Repeat independent protocol RTL checks and measure the integrated path. Translation/equivalence and physical loading remain open in the [processor plan](processor-verification.md); this milestone does not settle the competition area or clock target.
