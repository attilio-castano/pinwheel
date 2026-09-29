# Paired package and host lifecycle

The retained paired package now has a **conditional E64 execution proof through
its real input adapters and result mailbox**. An accepted commit establishes the
new program's execution state directly. The existing commit/start sequence needs
no additional reset or pipeline edge. The same boundary supports certified
replacement while preserving an unread result.

This connects the [timed core proof](paired-timed-execution.md) to what a host can
observe. It advances the [complete design iteration](../research/complete-design-iteration.md)
without changing the circuit. [Research status](../research/status.md) owns the
next gate; the [manifest](../../physical/experiments/paired-host-results.json)
records this source freeze and its validation receipt.

## Exact claim

[`PairedHost.retained_initialized_commit_segment`](../../Pinwheel/Hardware/Storage/PairedHost.lean)
composes these steps:

1. Start with arbitrary controller state, adapter registers, mailbox contents,
   SRAM contents and Q, represented by the typed package state.
2. Hold the reset pin low for three sampled edges. The two sampler stages
   propagate initialization to the core; no clean power-up state is assumed.
3. Allow an arbitrary finite pin history. It may include incomplete uploads,
   rejected commands, previous executions and earlier program replacements.
4. At the chosen boundary, the actual controller accepts commit and its actual
   **staged accepted transcript** passes the independent E64 image certificate.
5. Every before/after observation of all three package output ports agrees with
   the composed reference throughout the following finite execution segment.
   Its decoded inputs must satisfy `init = 0` and `command != 3`.

Commit sets ready mode, clears both counters and all samples, and applies the
newly selected bank's certified idle pin commands. Start may follow immediately.
The mailbox keeps its own existing state and timing; commit does not clear an
unread result. `retained_commit_segment` can be reapplied to any later certified
accepted replacement, independently of the previous program and sample values.

The segment rule still excludes even a rejected command 3. A replacement starts
a new segment with its own certificate. Arbitrary finite loops, reset commands,
staging, ignored busy commands and input samples remain covered where the rule
permits them. No termination guarantee is asserted.

## What each layer means

| Layer | Connection |
| --- | --- |
| [`PairedLifecycle`](../../Pinwheel/Hardware/Storage/PairedLifecycle.lean) | Derives the reset-like E64 state from the actual accepted commit, including new-bank idle metadata and accepted transcript ownership. |
| [`PairedPackage`](../../Pinwheel/Hardware/Storage/PairedPackage.lean) | Interprets the retained typed package as its actual pin map, two sampler registers, serial receiver, closed SRAM/controller and result observer. All register steps and output ports agree for arbitrary histories. |
| [`PairedHost`](../../Pinwheel/Hardware/Storage/PairedHost.lean) | Supplies execution state and busy from E64, carries the established relation through package edges, and proves the initialized commit/segment theorem. |
| Qualified serial delivery | `PairedHost.session_delivers` connects the actual consumed command stream to the existing `Serial.Session` theorem: idle samplers and an idle receiver, a qualified session, and two final samples deliver exactly its commands among quiet edges. |

The package reference deliberately retains the loader graph's control/status
and speculative read-address interpretation. E64 supplies mode, PC, counters,
pin commands, samples and busy. Loader rejection, active-bank and pending status
are therefore **not new instruction-level E64 claims**. The result mailbox reads
the pre-edge core observation, as the circuit does. Its sample-page selection,
completion delay, oldest-unread retention, overrun, consume and clear behavior
retain their existing semantics.

The theorem supplies the SRAM behavior law as an explicit
`Memory.SinglePort.Contract` parameter. Qualified digital samples are not a
proof of analog sampling margins, metastability behavior or board transport.
There is no new global memory axiom, state register or hardware edit.

## Admission in the subsequent gate

This earlier gate proves what happens **after the actual upload has been accepted**.
It does not yet prove that every certified image offered through a correctly
formed host upload necessarily passes every admission check and reaches that
commit. Delivery and acceptance are different facts: a delivered word may be
rejected by the controller.

The subsequent [admission/session gate](paired-upload-admission.md) now discharges
that premise for the existing paired host workflow: a qualified
begin/290-word/commit session, beginning with a stopped initialized controller
and a certified image, establishes the complete staged transcript and accepted
commit. This theorem then supplies execution and result observation. The receipt
below retains this earlier gate's original scope.

## Validation and reproduction

```sh
python3 scripts/check-paired-formal.py --tag paired-host-fresh \
  --retained-manifest physical/experiments/paired-validation-mapping.json
```

Use a fresh tag; the retained manifest is optional when historical mapping
artifacts are unavailable. Schema 5 adds the package/lifecycle gate while
preserving previous report identities. The runner checks the default library
build, complete import reachability, whole-library axiom audit and injected
unapproved-axiom rejection. It reruns existing graph, upload, runtime, timed and
schedule controls and checks fresh core/package MLIR and assembly metadata
against the retained mapping artifacts.

The new [controls](../../test/PairedHost.lean) prepare two complete images with
actual accepted decoded writes, then drive serial commit and start frames into
the actual retained package. They check initialization from dirty state,
commit/start without reset, both banks, immediate decoded start, capture pages,
unread-result retention across replacement, halt-only completion, overrun,
consume/clear and restart. Three corruptions are executed through another edge:
mailbox sample data, drive enables and page-pipeline state. The finite harness
does not replay all 290 upload words bit by bit; qualified delivery is proved
separately. These controls support, rather than define, the theorem's scope.

The `paired-host-01` receipt passes in **199.413 seconds**. It covers
**229 reachable modules** and audits **16,736 declarations / 8,696 theorems**
with standard Lean axioms only. The injected axiom is rejected; all existing
contract, graph, upload, runtime, timed and schedule controls pass. The new test
checks **794 package pin-edge pairs** and rejects all **three executed
corruptions**, in 69.357 seconds. This includes two serial commit frames and
three serial start frames across both banks, with no extra reset after commit.

Fresh core/package MLIR and assembly metadata are byte-identical to the retained
mapping artifacts. The report binds **250 source inputs / 17 artifacts** and
confirms inputs did not change during validation. The earlier timed manifest,
report, proof modules and test remain unchanged; root imports and the runner
have a new source freeze. The full protocol executable suite was not rerun.
All work remains local.

## Remaining physical boundary

The [SRAM component proposal](../../physical/fixtures/sram-trust/contract.json)
remains unchanged and unqualified. The source/layout resistor-width disagreement
and incompatible delivered fast operating conditions remain open. RTL emission,
CIRCT, synthesis and complete source-to-GDS correspondence are separate from
this typed-circuit proof. Resident SHIFT/KEEP extensions remain outside the
canonical E64 certificate. A/B acceptance and clean-source physical replay remain
open.

There are zero CAD calls. Campaign usage remains 8,412.163 CAD seconds, with
three A routes used and two B routes reserved. No additional chip route follows
from this formal result.
