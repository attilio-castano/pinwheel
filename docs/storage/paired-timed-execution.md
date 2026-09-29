# Paired timed execution

On **2026-09-28**, the retained paired controller gains a **cycle-for-cycle
proof against the canonical E64 execution model**. For every finite execution
history within one certified program segment, its public mode, program address,
counters, pin commands and sixteen samples agree before and after every edge.
The SRAM behavior law remains an explicit premise. The circuit is unchanged.

This closes the control and observation gap left by the
[running-state gate](paired-runtime-ownership.md): dispatch times and branch
choices now follow the reference's guards, counters and captures. It advances
the [complete design iteration](../research/complete-design-iteration.md) by
connecting a stored program's meaning to the retained controller's behavior.
[Research status](../research/status.md) owns the next gate.

**Follow-up:** the [package and host lifecycle gate](paired-host-lifecycle.md)
now proves that accepted commit establishes the relation without another reset
and composes execution with the actual adapters and mailbox. The checkpoint
below retains its original reset-based theorem and validation receipt.

## Exact claim and starting conditions

[`PairedTimed.initialized_segment`](../../Pinwheel/Hardware/Storage/PairedTimed.lean)
starts with arbitrary registers, SRAM contents and Q. Its sequence is:

1. An initialization edge establishes the earlier storage invariants.
2. An arbitrary decoded upload history ends with a valid active image whose
   **accepted transcript**, recorded from the actual controller, passes the
   independent E64 image certificate.
3. A reset edge establishes the execution relation: ready mode, zero counters
   and samples, and the program's idle pin commands.
4. Every edge of the subsequent execution segment agrees with E64. Inputs are
   arbitrary subject to `init = 0` and `command != 3` on each consumed edge.

The segment rule conservatively excludes every command 3, including a rejected
commit. Initialization or replacement begins a new segment and needs its own
certificate. Reset, restart, staging commands, ignored busy commands and arbitrary
input samples are allowed. Branches may loop: the theorem covers any finite
prefix, without asserting that every program terminates.

The reset in step 3 is a real controller edge, not an assumed clean power-up
state. `retained_trace` also applies to any already-related starting state.
Showing that the existing host's commit/start sequence establishes that relation
without an additional reset is part of the package/host composition gate.
The theorem does not assume arbitrary internal graph wires are correct: the
retained constructor and closed SRAM feedback discharge those obligations.

## What the proof connects

| Obligation | Proof owner and consequence |
| --- | --- |
| Packed sample bits and capture descriptors | [`PairedBits`](../../Pinwheel/Hardware/Storage/PairedBits.lean) interprets the actual capture circuit and branch sample. |
| Stored fields and source operations | [`PairedE64`](../../Pinwheel/Hardware/Storage/PairedE64.lean) connects canonical token/parameter fields and successor selection to E64 entry and dispatch. |
| Advance, guard, wait and qualification decisions | [`PairedControl`](../../Pinwheel/Hardware/Storage/PairedControl.lean) derives the actual control wires for every running mode. |
| Pin commands, samples and counters after an edge | [`PairedEntry`](../../Pinwheel/Hardware/Storage/PairedEntry.lean) interprets entry, countdown, retry, stop and reset register updates. |
| A fixed active program and its entry data | [`PairedCertified`](../../Pinwheel/Hardware/Storage/PairedCertified.lean) preserves the certificate under the segment rule and connects actual entry tokens, parameters and idle metadata. |
| Source-state consistency | [`PairedReference`](../../Pinwheel/Hardware/Storage/PairedReference.lean) proves that each running reference mode retains the operation that installed it. |
| Terminal capture and subsequent entry | [`PairedEdges`](../../Pinwheel/Hardware/Storage/PairedEdges.lean) connects certified entry to sequential and checked dispatch. A branch reads the terminal capture before the next instruction can overwrite its destination. |
| One complete execution edge | [`PairedTimedStep.step`](../../Pinwheel/Hardware/Storage/PairedTimedStep.lean) covers all running modes, idle states, start, reset, halt, timeout and fault. |
| Retained-controller observations and histories | [`PairedTimed`](../../Pinwheel/Hardware/Storage/PairedTimed.lean) projects the actual public core-state outputs, composes the explicit memory contract and proves every before/after trace observation. |

A ready input wins on the final permitted wait edge. A failed checked guard
wins over countdown or dispatch, including when the counter is zero.
Qualification counts consecutive ready edges, reloads the interval on a blocked
edge, consumes its wait budget, and refreshes that budget on a ready countdown
edge. Start clears old samples before entry capture; reset wins over start.
Terminal states apply the program's idle pin commands.

Pin levels and enables are **digital drive commands**, not measurements of
voltages or claims about external sampling margins. The observation includes
normalized PC (zero while stopped), both counters and every sample bit. Loader
status and speculative read addresses are outside the E64 observation.

## Validation and reproduction

```sh
python3 scripts/check-paired-formal.py --tag paired-timed-fresh \
  --retained-manifest physical/experiments/paired-validation-mapping.json
```

Use a fresh tag. Omit the optional retained manifest when the historical local
mapping artifacts are unavailable. The tracked
[manifest](../../physical/experiments/paired-timed-results.json) links the new
source freeze and receipt to the unchanged prior runtime manifest. The runner
now includes the timed gate; older reports keep their original hashes and scope.

The `paired-timed-02` receipt passes in **123.265 seconds**. The build and
import check cover **226 reachable modules**. The whole-library audit checks
**16,564 declarations / 8,585 theorems** with only standard Lean axioms, and an
injected unapproved axiom is rejected. Existing contract, graph/package, upload,
runtime and schedule controls pass. Fresh core/package MLIR and interface
metadata are byte-identical to the retained mapping artifacts. The report binds
**246 source inputs / 16 artifacts**. The full protocol executable suite was
not rerun.

The new boundary test passes **686 before/after edge pairs** and rejects
**eight live-state or capture-parameter corruptions**. The earlier 100-edge
runtime test also passes. The first `paired-timed-01` attempt retained a failed
receipt for a missing dependent type annotation in the new mutation harness;
the library and axiom audit had passed. The corrected harness has a new source
freeze and receipt. No proof premise or audit policy was relaxed.

The new [boundary controls](../../test/PairedTimed.lean) compare actual retained
public outputs before and after execution edges. Both active banks are loaded
through real commands, and the resulting accepted transcript is certified.
Six scenarios cover terminal capture/branch/entry capture of the same slot,
maximum duration, zero-budget deadline success and timeout, guard priority,
reset/start priority, and repeated backward jumps. Live counter, pin, sample and
capture-parameter corruptions are executed through another edge and must diverge
from the independent reference. These finite checks support the universal
proof; their coverage is not its quantifier.

## Remaining boundary

The proof covers canonical E64 at the **decoded-command boundary**, under the
stated segment rule and memory law. Resident SHIFT/KEEP extensions are outside
that certificate. The next formal gate connects this result to the existing
package adapters, result observer and qualified host delivery, including the
actual commit/start lifecycle and program replacement between segments.

RTL emission, CIRCT, synthesis and the complete source-to-GDS connection remain
separate obligations. The [component contract proposal](../../physical/fixtures/sram-trust/contract.json)
has not changed; the supplied SRAM's internal qualification and compatible fast
operating conditions remain open. A and B remain unaccepted.

There are **zero CAD calls**. Campaign usage remains 8,412.163 CAD seconds,
with three A routes used and two B routes reserved. The proof adds no hardware
state. Fourteen existing graph-wire lemmas become public for reuse, with their
statements and proofs unchanged; the new receipt accounts for that source change.
