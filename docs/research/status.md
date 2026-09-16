# Research status

Updated 2026-09-15. Physical conclusions use committed evidence through `5d89d95`;
the UART receive additions, from one-byte frames to continuous reception with
unequal clocks, are identified by their validation receipts. This is the current
decision brief; [results](results.md) owns completed conclusions and
[journal](journal.md) routes historical evidence. The bounded command-decoder
experiment is complete; candidate physical validation remains pending. The current
UART work stays at the Lean specification and compiler level.

## Objective and current belief

Build a general reloadable protocol engine whose implementation preserves specified
pin timing, input capture, branching, and atomic program replacement, then establish
its physical feasibility under the [competition constraints](../competition.md).

The general 32-entry dense cached core remains the default implementation and
physical comparison baseline. Its first routed slow-corner setup slack is
−6.254 ns. F2 flow repair improves the overall worst slack to −5.055 ns, but does
not close timing or electrical limits. Two speculative-read layouts were proved
and screened without earning a routing run. See [completed results](results.md).

The completed `command-split` candidate removes capacity-check dependencies from
commit/start decoding while retaining push validation and all existing semantics:

- Structural Lean theorems preserve every pre/post-edge observation for arbitrary
  two-state initial values and input histories; **102 declarations** pass the
  standard-axiom audit. Dense emission and CIRCT retain a separate test boundary.
- **21,864 regression edges**, 13,444,072 storage observations, and 3,585,618
  defined output-bit comparisons pass; capacity-bypass and output-inversion
  mutations are rejected.
- Mapped cell area falls about **1.1%**, with 6,226 flip-flops unchanged. Typical
  ABC delay improves about 9.8%; the slow estimate changes only about 0.19%.
- Loader-data connectivity to the **57 retained cache-register data inputs**
  falls from 57 to zero in both mapped corners. Protocol inputs still reach all
  57. This establishes removal of the within-cycle dependency, not timing closure;
  loaded data still affects later execution through memory registers.

The [decoder closeout](../successor-fetch-study.md#command-decoder-experiment) and
[committed manifest](../../physical/experiments/command-split-results.json) own the
exact measurements and source identities. The candidate has not been routed or
promoted to the default implementation.

## Completed Lean milestone: continuous receive with unequal clocks

The [UART link proof](../uart-link.md) connects one transmitted byte through
independent clock periods/phases and bounded digital observation age to the
receiver, including both compiler paths. Start detection and all sample values
follow from numerical timing bounds. A physical sampler must still justify the
assumed age contract.

The [continuous receive model](../uart-stream.md) now defines automatic rearm,
a one-entry result buffer, explicit consumption, sticky overrun, and reset
flushes. Lean proves occurrence ordering/accounting, independence from consumer
controls, ideal finite back-to-back frame pulses, and correspondence with the
compiled-program supervisor. The `uart-stream-01` full gate passed all 23 suites
and both independent oracles; the stream suite covers all 65,536 ordered byte
pairs and 11,844,449 RX edges. The technical record owns the exact receipts.

The [continuous clock contract](../uart-stream-clocks.md) now strengthens the
single-frame margin with two additional RX ticks for rearm and an idle-high
observation. Lean proves finite-stream reception under unequal constant clocks,
arbitrary relative phases satisfying the contract, and independently varying
bounded observation age. The result composes through the existing compiled RX
supervisor, with arbitrary consumer controls and initial buffer contents.
The previous rearm failure is retained and excluded by the stronger bound.
The `uart-stream-clocks-01` full gate passed all 24 suites and both independent
oracles in 1,012.316 seconds. The audit covers 10,058 declarations and 5,254
theorems; all 179 source hashes matched at closeout. Its new suite covers 392
streams, 38,808 frames, and 10,531,120 RX edges. The detailed study owns the
receipt and count balance.

## Next proposed Lean question: receiver lifecycle and program replacement

Continuous listening keeps the current RX program busy, so stopping, resetting,
and reloading need an explicit supervisor contract that composes with
[atomic program replacement](../atomic-loader.md). It must also define ownership
of a pending result. The present theorem assumes one fixed RX program; this
lifecycle contract is the proposed follow-on.

## Deferred physical question: does decoder isolation help after routing?

Does one matched physical implementation of `command-split` improve extracted
area/timing and electrical behavior under F2's flow controls?

The [targeted source-family baseline](../successor-fetch-study.md#targeted-launch-family-timing)
measures **−4.928 ns protocol-input slack in the previously routed F2 design**,
nearly tied with its −5.055 ns loader-data slack. That value is not a routed
measurement of `command-split`. The evidence supports cleaner command logic and
slightly smaller mapped area; it does not predict automatic physical closure.

## Gates for a future physical comparison

1. Recover the validated candidate at `1a0c960`, its receipt, and actual checkout/run
   state before starting anything. Preserve the default reference and freeze the
   candidate RTL separately in a candidate-aware physical runner.
2. For the next authorized physical comparison, start from synthesis with F2's
   controls, the same 20 ns clock, I/O constraints, and diagnostic floorplan. A
   routed checkpoint for the old RTL cannot initialize the changed candidate.
3. Compare final extracted paths by launch family, area, setup/hold, electrical
   limits, antenna/DRC/LVS checks, and defined-output regression. Investigate where
   the critical path moves; mapped connectivity alone cannot establish timing.
4. Record the physical result and allocation in the owning study and these records.
   Preserve failures and decide the next experiment from the remaining bottleneck.

Scope and resource limits come from the approved main task and its retained run
briefs; this documentation adds no compute budget, new run, or external authority.
No aggregate historical resource total was reconstructed here.

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

## Deferred questions

- Synchronous SRAM/latches need a proved availability/write schedule for arbitrary
  accepted programs; average protocol idle time is insufficient.
- The bounded I²C repetition prototype has narrower scope than the general engine.
- Antenna-related fanout, protocol-input delay, the official 8×4 wrapper, external
  serial loading, and translation equivalence remain separate obligations.

Reopen these when evidence changes the allocation, using the conditions in
[results](results.md). Preserve earlier studies' detailed limitations and frozen
comparison contracts.
