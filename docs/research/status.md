# Research status

Updated 2026-09-15 from committed evidence through `5d89d95`. This is the current
decision brief; [results](results.md) owns completed conclusions and
[journal](journal.md) routes historical evidence. The bounded command-decoder
experiment is complete; candidate physical validation remains pending.

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

## Active question: does decoder isolation help after routing?

Does one matched physical implementation of `command-split` improve extracted
area/timing and electrical behavior under F2's flow controls?

The [targeted source-family baseline](../successor-fetch-study.md#targeted-launch-family-timing)
measures **−4.928 ns protocol-input slack in the previously routed F2 design**,
nearly tied with its −5.055 ns loader-data slack. That value is not a routed
measurement of `command-split`. The evidence supports cleaner command logic and
slightly smaller mapped area; it does not predict automatic physical closure.

## Continuation and gates

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

## Deferred questions

- Synchronous SRAM/latches need a proved availability/write schedule for arbitrary
  accepted programs; average protocol idle time is insufficient.
- The bounded I²C repetition prototype has narrower scope than the general engine.
- Antenna-related fanout, protocol-input delay, the official 8×4 wrapper, external
  serial loading, and translation equivalence remain separate obligations.

Reopen these when evidence changes the allocation, using the conditions in
[results](results.md). Preserve earlier studies' detailed limitations and frozen
comparison contracts.
