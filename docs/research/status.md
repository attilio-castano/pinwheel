# Research status

Updated 2026-09-17 with the hardware closure, [cache-enable follow-up](../cache-enable-study.md),
and UART receive capability from main.
This is the current decision brief; [results](results.md) owns completed
conclusions and [journal](journal.md) routes historical evidence.

## Objective and current belief

Build a general reloadable protocol engine whose implementation preserves
specified pin timing, input capture, branching, and atomic program replacement,
then establish physical feasibility under the [competition constraints](../competition.md).
Keep the reference execution semantics steady while closing implementation gaps.

The formal work now connects the emitted RTL of one explicitly composed 32-entry
dense cached Lean netlist to the reference machine. Its initialization, per-edge
state relation, and every pre/post-edge
observation refine the atomic machine with the existing 322-word capacity
restriction. The serializer consumes that netlist. The legacy dense cached
emitter remains the default and physical comparison baseline.

Completed validation distinguishes the two translation endpoints:

- **Countdown:** actual emitted RTL is interpreted back into Lean, with
  kernel-checked transition/trace equality and rejected corrupted artifacts.
  Yosys proves all 19 RTL/generic-gate comparison points.
- **Composed backend:** Lean checks the actual emitted RTL against the complete
  netlist refinement, covering 607 registers, 33 outputs and initialized traces.
  Its audit permits only standard axioms. Yosys proves
  all 6,315 old/new RTL and 6,309 RTL/generic-gate comparison points under the
  recorded state correspondence. Independent loader/storage regression and two
  mapped corners pass. The Verilog frontend/JSON adapter remain explicit trusted
  boundaries; technology-mapped sequential equivalence remains open.
- **External interface:** a proposed two-register sampling pipeline and
  open-drain interpretation have Lean contracts. They add no latency to the
  current core; the wrapper, serial transport and electrical assumptions remain
  integration work.

The [bank-selection experiment](../bank-selection-study.md) applies that method
to a composed command-split control and one candidate that selects between
completed bank reads. Both full circuit refinements and actual emitted-RTL
read-backs pass, including initialization, all 607 register updates and all 33
outputs. Each passes legacy/generic-gate equivalence, independent loader/storage
regressions, focused bank-switch cases and corruption checks. The actual circuit
can now be changed and measured with an explicit proof for each emitted variant.

The [cache-enable follow-up](../cache-enable-study.md) preserves the shared read
and every register update while simplifying the update decision. Both fresh
control and candidate pass complete emitted-RTL read-back, the standard-axiom
audit, equivalence and independent regressions. Exact-cache cases cover stopped
and running edges, faults, reset, self-branches and busy commit rejection. The
result removes direct control dependencies from the enable, while an indirect
cursor/command path remains through successor decoding.

The earlier portable gate passed 109 modules, 9,125 declarations / 4,665 theorems using
only standard Lean axioms, and all 20 executable suites. See the owning
[closure record](../hardware-closure.md) for exact hashes, initial-state
assumptions and failed attempts.

## Physical finding

The matched `command-split-closure` candidate completed routing and final
three-corner extracted timing with unchanged F2 controls and constraints.
Worst setup is **−5.049 ns**, essentially unchanged from F2's **−5.055 ns**.
Cell area excluding fill falls about 0.91%, while setup violations rise from
112 to 1,426 and the worst hold margin shrinks to about 2.9 ps. Electrical
violations remain. The implemented-netlist regression passes.

The worst path now starts at `loader_cursor[5]` and ends in the current-word
cache. Loader-data timing improves, but that does not close the core. The
[matched comparison](../successor-fetch-study.md#matched-command-split-physical-comparison)
owns launch-family measurements and the final layout-check disposition. The
one-hour attempt stopped during Magic DRC with exit 124. Magic DRC, LVS and later
checks are incomplete; routing/antenna checks report zero violations. The
[physical manifest](../../physical/experiments/command-split-physical-results.json)
pins that partial flow result. No candidate is promoted to the default.

The new bank-selection candidate stops at the matched mapping gate. Cursor-to-cache
logic depth falls from 32 to 25, but protocol-input depth grows from 35 to 38.
Area rises about 2.1%; typical ABC delay worsens 6.6% and the slow estimate improves
only 0.15%. This does not justify routing under the agreed gate. No new physical
run was started, and the conditional two-run allocation was unused. The
[bank-selection manifest](../../physical/experiments/bank-selection-results.json)
retains the proved candidate and exact receipts. These mapping measurements
do not replace the legacy artifact's extracted physical timing.

The cache-enable candidate improves the matched mapping screen: typical/slow
cell area falls 0.375% / 0.452%, and ABC delay falls 9.108% / 1.312%. Cursor logic
depth drops 32 → 28; protocol depth drops 35 → 32. Commands and reset also get
shallower, with unchanged maximum fanout. Retain this experimental variant; the
modest slow-corner gain supports a fresh matched physical comparison but does
not establish routed improvement. No physical run or default promotion occurred.
The [cache-enable manifest](../../physical/experiments/cache-enable-results.json)
pins eight completed receipts and 914 verified source/artifact hash entries.

## Next discriminators

1. Extend sequential equivalence from generic gates to a selected technology
   mapping, explicitly accounting for initial-state correspondence and eliminated
   bits. Preserve independent tests with uninitialized storage.
2. Use the [cache-enable candidate](../cache-enable-study.md) for the next matched
   physical discriminator, with a separately accounted fresh composed control,
   unchanged 20 ns/I/O constraints and F2 controls. Keep the indirect shared-read
   dependency visible when interpreting the worst path. The current completed
   batch ends at mapping; the next physical allocation remains a separate step.
3. Resolve the actual wrapper/I/O budget and loading transport, then compose the
   [external timing contract](../external-interface.md) with protocol assumptions.
   Synchronizer delay must appear in those bounds; no asynchronous or analog
   detection guarantee follows from the digital two-edge theorem.

The completed command-split physical attempt used four CPUs, a 6 GiB limit and a
one-hour cap; its receipt records the end state. The bank-selection and
cache-enable follow-ups consumed no additional physical run. Historical cumulative
resource use remains unknown. This status record grants no additional run or
external action.

## UART receive capability

The [one-byte UART receiver](../uart-receive.md) now compiles to the existing
reactive engine and runs through E64, the atomic loader, and the default dense
cached core. It adds a digital receive contract without changing core circuitry.
All supported period/input configurations fit the current storage capacities.
TX and RX remain separate loaded programs. The [link contract](../uart-link.md)
now proves communication between independent program instances under clock and
observation-age bounds, including successive frames under the strengthened
continuous bound. Continuous buffering has a Lean supervisor contract;
its structural circuit and loader composition, a concrete input wrapper, and
concurrent execution still need their own designs and evidence. These capability
results add no physical closure evidence to the comparison above.

## Next proposed Lean question: receiver lifecycle and program replacement

Continuous listening keeps the current RX program busy, so stopping, resetting,
and reloading need an explicit supervisor contract that composes with
[atomic program replacement](../atomic-loader.md). It must also define ownership
of a pending result. The present theorem assumes one fixed RX program; this
lifecycle contract is the proposed follow-on.

## Deferred questions

- Synchronous SRAM/latches need a proved availability/write schedule for arbitrary
  accepted programs; average protocol idle time is insufficient.
- The bounded I²C repetition prototype has narrower scope than the general engine.
- The official 8×4 wrapper, package pins, electrical limits and physical timing
  closure remain separate obligations.

Reopen these when evidence changes the allocation, using the conditions in
[results](results.md). Preserve detailed limitations and frozen comparison contracts.
