# Paired running-state ownership

**Follow-up:** the [timed execution gate](paired-timed-execution.md) now proves
dispatch decisions and complete public execution traces within a certified
program segment. This page preserves the earlier ownership receipt and scope.

On **2026-09-28**, the retained paired controller acquires a proof that its
**current instruction, cached parameter and usable SRAM response belong to the
active image whenever it is running**. This holds after initialization through
every finite decoded-command history, from arbitrary prior registers, SRAM
contents and Q. It closes the running-state obligation from the
[upload gate](paired-upload-coverage.md). The circuit is unchanged.

For the complete design iteration, this connects accepted storage to what the
controller actually uses during execution. With the existing image certificate,
the current token denotes its source instruction and an actual dispatch selects
the certified successor for the actual branch wire. Proving **when** dispatch
occurs and **why** that branch bit agrees with E64 remains the next step.
[Research status](../research/status.md) owns that decision.

## What is proved

`PairedRunning.Ready` states that, in modes 1–4:

- The active image is valid.
- The cached parameter equals the active bank's parameter at the current token's index.
- Q equals the active bank's SRAM row addressed by the current token.
- The current token is nonterminal and came from that bank's boot token or a stored successor.

The invariant is preserved using the actual shared graph equations and actual
memory response feedback. The graph-equation and feedback premises are
discharged when composing the initialized-history theorem with the retained
controller; they are not independent assumptions about arbitrary internal wires.

| Connection | Proof owner |
| --- | --- |
| Every edge whose resulting state is running requests a read and preserves stored contents | [`PairedRunning.running_read`, `running_memory`](../../Pinwheel/Hardware/Storage/PairedRunning.lean) |
| Current token, parameter, response, validity and provenance stay together | `PairedRunning.ready_next` |
| Initialized histories preserve both upload coverage and running ownership | [`PairedRuntime.initialized_run`](../../Pinwheel/Hardware/Storage/PairedRuntime.lean) |
| The retained controller inherits the invariant with an explicit SRAM behavior law | `PairedRuntime.retained_initialized_history` |
| A certificate for the active accepted transcript identifies actual parameter and response values | `PairedRuntime.certified_values` |
| The running token matches the canonical source instruction at its row address | `PairedRuntime.certified_current` |
| On actual entry from a running state, the controller installs the certified successor selected by its actual branch wire | `PairedRuntime.dispatch_token`, `dispatch_matches` |

The upload ledger remains mathematical state; no storage or logic is added to
the chip. These ownership results also survive commands that are rejected while
busy. Initialization need not clear SRAM or parameter registers: it prevents
running until the required validity and storage relationships are established.

## The response timing result

The proof resolves an uncertainty in the prior plan: **there are no Q-hold edges
whose resulting state is running** in this controller. Holding an instruction
during a countdown or blocked wait still reads its row. An instruction transition
uses the old Q to select its successor and reads the new current token's row
for the state after the edge. Starting uses the boot token and refreshes Q.

Stopped states may retain stale or arbitrary Q; the invariant makes no usability
claim there. A terminal transition can consume the old Q and leave it held,
because no further running instruction needs the resulting response.

## Validation and reproduction

```sh
python3 scripts/check-paired-formal.py --tag paired-runtime-fresh \
  --retained-manifest physical/experiments/paired-validation-mapping.json
```

The optional manifest checks identity against retained local mapping artifacts;
omit it when those historical artifacts are unavailable. Use a fresh tag. The
[runtime manifest](../../physical/experiments/paired-runtime-results.json)
binds this source freeze and receipt to the unchanged prior upload manifest.
Earlier receipts remain unchanged; the current runner includes this new gate.

The `paired-runtime-01` receipt passes in **62.091 seconds**. The complete build
and import check cover **217 reachable modules**. The whole-library audit checks
**16,268 declarations / 8,328 theorems** with only standard Lean axioms, and
rejects an injected unapproved axiom. Existing graph/package, memory, schedule
and adversarial upload controls pass. Fresh core/package MLIR and interface
metadata are byte-identical to the retained mapping inputs.

The new [runtime controls](../../test/PairedRuntime.lean) construct a small
canonical program, check its complete image certificate, and load it through
actual controller commands into each active bank. Six histories exercise entry
capture, countdown, ignored busy commands, wait success/timeout, guard fault,
terminal capture and both branch outcomes, out-of-range fault, qualification
success/interval restart/timeout, halt, both reset forms and restart. Across **100 reference
edges**, including **82 running edges**, modes, counters, samples, pin commands
and running program addresses agree with the independent E64 model. Stopped Q
holds as required. Deliberately stale Q, corrupted parameters and invalid source
tokens are each rejected in both banks. These are finite execution checks.

## Remaining boundary

The universal proof establishes ownership and successor correspondence conditional
on an actual entry edge and the actual branch wire. It does **not** yet derive
that edge or wire from the timed E64 reference. Mode/counter correspondence,
capture ordering, guard/wait/qualification decisions, terminal/reset pin timing
and the complete initialized timed refinement remain to be proved. The finite
execution checks support that next proof; they do not replace it.

The theorem starts at decoded commands. Package composition and successful host
delivery must be connected under their existing conditions. The certified source
language is canonical E64; resident SHIFT/KEEP extensions are outside its scope.
The [SRAM contract proposal](../../physical/fixtures/sram-trust/contract.json)
remains an explicit theorem parameter, with no global memory axiom. Exact-version
physical qualification, compatible fast timing, RTL/synthesis/source-to-GDS
correspondence, accepted A/B and clean-source physical replay remain open.

There are **zero CAD calls**. The chip, installed PDK, proposed component contract
and prior physical receipts are unchanged. Campaign usage remains 8,412.163 CAD
seconds, with three A routes used and two B routes reserved. The full protocol
executable suite was not rerun; this receipt covers the focused formal gate.
