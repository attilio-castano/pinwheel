# Design A acceptance and blocker audit

Milestone 0 executed **2026-09-26** under the
[complete-design-iteration plan](complete-design-iteration.md). The audit is
complete; **design A is not yet accepted**. This page binds the requirements to
the retained paired implementation and separates missing evidence from extra
optimization preferences. [Status](status.md) owns subsequent allocation.

**Execution follow-up:** the [second A layout](../physical/balanced-detailed-experiment.md)
now has positive extracted setup/hold and passing routing/full-rule Magic DRC,
LVS, antenna, power-connectivity and final-circuit checks. **A is not accepted:**
one cap and 14 antenna-induced fanout failures remain; both allocated A routing
attempts are used. The [paired image certificate](../storage/paired-image-certificate.md)
closes source-bytes/upload/dispatch correspondence, while full timed-controller/
package refinement, fast-corner qualification, accepted A/B and clean-source
physical replay remain open. The tables below preserve the initial audit before
these follow-ups; [status](status.md) owns the current decision.

## Frozen design brief

A supports 256 logical positions and 32 distinct canonical E64 records, two
atomic banks, the paired controller's existing operation set and exact pin,
capture, branch, reset, loading and result behavior. Its experimental upload
format has 290 words. The clock is 20 ns; input/output maximum and minimum
delays remain 4.0/0.2 ns, output load 0.010 pF and clock uncertainty 0.2 ns.
No extra execution cycle, hidden timing exception or program restriction is
introduced by the audit.

The first platform is the pinned 6×4 footprint, 1,289.28 × 710.64 µm, its actual
43-pin template and existing macro/power geometry. An expanded footprint needs
a separately declared platform under the plan. A cell-area repair allowance is
not the same quantity as a die-area constraint.

The starting checkpoint is `route-import-fix-01/candidate/repaired.odb`, bound
by the [retained manifest](../../physical/experiments/route-import-fix-results.json).
The new evidence lives under `build/validation/design-iteration-01/`. Its
`audit.json` has SHA-256
`af5f63557c38d549557a489f75fec28068cc2649c316f0b71e197d656c6c4b9b`.

## Acceptance table at the initial audit

| Requirement | Present evidence | Verdict and remaining work |
| --- | --- | --- |
| Declared capacity and edge behavior | Paired model, emitted core/package tests and retained mapped comparison | Substantial checked behavior; complete refinement is open below. |
| Current source produces the retained circuit | Fresh core/chip MLIR, SystemVerilog and assembly regenerate byte-identically | Passed fresh generation identity. This is not a proof of circuit meaning. |
| Exact implemented circuit is identified | Candidate ODB, mapped artifacts, readbacks, recipes and retained inputs match recorded hashes | Passed retained-artifact audit; physical edits still require their scoped equivalence evidence. |
| Complete routing | Current checkpoint has 25 Metal3 coarse overflow units; minimum pin access passes | Open. A detailed-route continuation is the next discriminator. |
| Extracted setup/hold and electrical limits | Coarse-route estimates report positive slack and zero actual electrical violations | Open. Require fresh extraction on final wires and qualified corners. |
| Qualified cell/SRAM timing assumptions | Typical 1.20 V/25°C and slow 1.08 V/125°C metadata agree; fast is 1.32 V with cells at −40°C and SRAM at −55°C | Fast-corner qualification blocked by a missing compatible view or justified conservative bound. Metadata agreement alone does not qualify other corners. |
| Layout, antenna and connectivity | Magic DRC, Netgen LVS, antenna and disconnection stages exist in the pinned flow | Available but not passed for A. Disabled KLayout DRC/XOR are not evidence of success. Check deck scope, macro coverage and actual outputs. |
| Power implementation | Bound macro rails and earlier geometry checks | Complete routed continuity and appropriate power checks remain open. |
| Final implemented-netlist behavior | Earlier mapped and physical-edit checks exist | Require the post-route netlist and the external-pin oracle on that artifact. |
| Host use of A | Host workflow exists for earlier formats | Integrate paired 290-word encoding/admission and preserve explicit format identity. |
| Reproducible design iteration | Generation reproduced; old physical dependencies are identified | A complete replay and the 64-record B change remain open. |
| Original competition allocation | Starting rectangle/template retained | Final acceptance in that allocation remains open. Oversized exploration must retain its overage label. |

The four remaining 20%-reserve shortfalls and the old 0.3% incremental
cell-area allowance are **comparison preferences**, not new functional or
electrical requirements. The historical +0.367343/+0.079278 ns setup/hold floors
remain useful comparison witnesses; final operation requires the actual declared
timing constraints to pass. No old verdict has been rewritten.

## Evidence identity and replay readiness

The audit independently checked four top-level identities, 2,411 retained input
versions, 2,542 physical artifacts, 24 prepared design inputs, 78 mapped/controller
artifacts, 402 installed PDK files and 142 PDK symlinks. All those checks pass.
It hashed 3,551 unique input files; the printed audit-file hash adds a further
file. The report retains exact paths, counts and mismatches.

Three of the 262 old paired source bindings have changed in both the old and
current checkouts: `Pinwheel.lean`, `scripts/host_demo.py` and
`scripts/pinwheel_host.py`. Five old generated prerequisites are absent from this
checkout but exist in the earlier checkout. These facts make the old source
receipt historical, not a current-source success receipt.

`current-source/report.json` closes the narrower generation question: a fresh
Lean build and controller axiom audit followed by CIRCT emission reproduce
`core.mlir`, `chip.mlir`, `core.sv`, `chip.sv` and `assembly.json` byte for byte.
The current source stays unchanged throughout that check. This took 10.939 s,
including 1.969 s of CIRCT work. It does not regenerate all old test fixtures or
establish the still-missing refinement theorems.

The prepared physical design is still in worktree `33a5`; the installed PDK and
some tool binaries are in `fc40`. Both are present and are used read-only. They
are explicit dependencies, not a self-contained deliverable. Capture required
inputs or a verified regeneration path before retiring those checkouts.

The local CAD image matches the pinned ARM64 filesystem layers/runtime settings.
Its actual flow contains detailed routing, antenna/disconnection checks, RC
extraction, multi-corner STA, Magic DRC and Netgen LVS. Tool presence and enabled
flags do not establish a passing layout. The saved configuration disables
KLayout DRC/XOR and whole-flow EQY; equivalence must be supplied by the actual
artifact checks, not assumed from a successful flow exit.

## Proof obligations identified by the initial audit

| Connection | Existing owner | Obligation still needed |
| --- | --- | --- |
| Source program → uploaded image | `scripts/paired_execution.py` | A sound image certificate or compiler theorem covering token fields, parameters, successors, boot/idle and capacity. |
| Image → dispatch schedule | `test/PairedSchedule.lean` | Discharge `Closed` from the actual encoded image. Existing `step_related`/`trace_related` preserve dispatch state under this premise; they do not cover complete E64 execution. |
| Dispatch → complete controller behavior | `Pinwheel/Hardware/Storage/PairedController.lean` | Relate actual state updates, waits, terminal/entry captures and payload behavior to the reference machine. |
| Upload → initialized closed memory | Existing atomic-loader contracts and paired admission expressions | Prove the paired 290-word admission/bank relation, reset, malformed upload, interrupted replacement and commit/start behavior. |
| Controller → external package observations | Existing sampler, serial receiver, result observer and paired wrapper | Compose the actual selected components under explicit environment/initialization assumptions. |
| Lean circuit → actual emitted RTL | Earlier `scripts/backend_readback.py` approach and fresh generation identity | Adapt artifact interpretation/correspondence to paired state and memory interfaces. The earlier 607-register backend proof does not transfer automatically. |
| Emitted RTL → mapped logic | Paired arbitrary-state SAT checks and exact macro terminals/state census | Retain exact artifact identities and the independent-SRAM-Q boundary; compose with the closed memory model. |
| Mapped logic → physical netlist | Checked buffer contraction, cell functions and actual netlist/geometry checks | Cover all post-route changes and final external behavior; timing/layout evidence remains separate. |

## Initial blocker ranking and first discriminator

1. **Physical routing feasibility is unmeasured at the required stage.** Run the
   unchanged retained A candidate through the pinned detailed-routing continuation
   and downstream checks, with empty initial metrics and a 90-minute cap. This
   directly tests whether small coarse overflow prevents actual wiring. It uses
   the first of at most two A full-flow attempts; no extra reserve repair is
   required merely to try the experiment.
2. **Fast-corner qualification is unresolved.** The pinned inventory supplies
   no same-temperature fast cell/SRAM pair for this macro. Both Liberty nominal
   and operating-condition fields confirm the mismatch. No conservative bound
   has been established. Routing can answer an independent question, but cannot
   remove this final timing blocker.
3. **The image/compiler and complete refinement chain are missing.** Work on a
   sound checked image and its schedule premise while physical feasibility is
   being tested; reuse the existing model and importer. Do not rename a finite
   simulation or conditional schedule theorem as full refinement.
4. **Host-format and reproducibility handoffs are incomplete.** Integrate paired
   images with the existing host and capture the declared dependencies. Keep the
   A regression before parameterizing the 64-record B design.

The first route is explicitly diagnostic while the corner obligation remains
open. It changes neither the circuit nor the declared timing boundary at entry.
Normal downstream flow repairs, if any, must be recorded and checked as changes
to the implemented artifact. Failed routing, nonzero layout checks and disabled
checks remain visible; none is waived to complete this milestone.

The [upstream SRAM documentation](https://ihp-open-pdk-docs.readthedocs.io/en/latest/contents/reference_libraries/sram.html)
was consulted on 2026-09-26 for the delivered-view/datasheet organization. It
does not supply a mixed-temperature qualification used by this audit. Library
availability and the numerical mismatch above come from the hashed pinned files.
