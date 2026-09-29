# One implementation, one acceptance report

The conditional digital proof and the retained physical circuit now have a
single reproducible evidence intake. **Design A remains unaccepted.** The report
now includes the checked paired RTL interpretation. Three requirements remain
open: exact-version SRAM qualification, compatible fast timing conditions and
package power qualification. The formal correspondence row passes under the
explicit interpretation boundary; physical acceptance still requires all three.

The subsequent [power sensitivity study](../physical/power-boundary-results.md)
adds measured source/resistance effects and three completely annotated finite
workloads on this same chip. Its contacts and impedances are diagnostic;
package qualification remains blocked. The retained acceptance selection and
report below are unchanged.

[Research status](status.md) owns the next decision. The
[current selection](../../physical/experiments/design-acceptance-readback-inputs.json)
pins ten evidence roots. The
[result manifest](../../physical/experiments/design-acceptance-readback-results.json)
binds the refreshed report and checker. The [initial selection](../../physical/experiments/design-acceptance-inputs.json)
and [initial assessments](../../physical/experiments/design-acceptance-results.json)
preserve the earlier four-blocker checkpoint; the CLI default still selects
that historical v1 intake. Use the explicit v2 selection below for the current result.

## Reproduce the decision

```sh
python3 scripts/check-design-acceptance.py --tag design-acceptance-fresh \
  --selection physical/experiments/design-acceptance-readback-inputs.json \
  --require-accepted
```

Use a new tag. Outputs are `build/validation/<tag>/report.json` and `report.md`.
The JSON contains exact input hashes, individual requirement verdicts, program
certificates, implementation connections, timing values and explicit proof
premises. The Markdown gives a readable requirement table with local links.

Exit **2** means that evidence was assessed but A is not accepted. Exit **1**
means evidence was missing, changed, inconsistent or could not be checked.
Without `--require-accepted`, a completed assessment returns 0 even when A is
blocked; consumers must read `A_accepted`, not infer acceptance from process
success. An existing run directory is never overwritten.
This intake targets the pinned experiment. New qualification evidence needs a
corresponding intake with its exact artifact identities and scope.

This command runs no CAD. It rereads selected retained evidence, reproduces
structural and timing conclusions, and freshly kernel-checks the eight captured
host certificates. It does not rerun host simulation, routing, extraction or
the full Lean library gate. The preceding admission receipt supplies that
library audit and is checked against all of its frozen sources and artifacts.
The interpretation receipt supplies the two additional compiled-environment
audits and actual RTL fault controls; its sources, tools and artifacts are also
checked. These earlier proofs are consumed by identity, not rerun by this intake.
Referenced build outputs and external worktree library files must be present;
missing dependencies are refused. The subsequent
[current-A recovery workflow](current-a-replay.md) inventories every dependency,
preserves the original checker/source bytes and relocates exact retained inputs
into a movable bundle. It uses this v2 selection explicitly and freshly checks
the eight certificates; physical observations remain retained reuse. This is
not a clean-source physical replay.

## The connection that the report checks

The host demonstration used the original paired RTL. The formal session proof
covers `PairedValidation`, whose upload validation lookup is isolated from the
execution lookup. Treating their names or shared upload format as identity
would leave a gap. The report instead checks these connections:

| Connection | Evidence and scope |
| --- | --- |
| Captured host program → concrete image certificate | Re-render the actual source and 290 upload words, require exact equality with the retained certificate, then recheck those captured certificate bytes with the Lean kernel. All eight programs are required. |
| Certified image → typed package behavior | `PairedSession.retained_initialized_session` derives upload acceptance, commit and timed E64 package observations under its explicit memory and digital-delivery premises. The full proof receipt's source freeze still matches. |
| Typed package → retained MLIR and assembly | Fresh emission identity pins the selected artifacts; the readback gate separately proves all 45 shared equations and total typed-component correspondence. |
| Typed components → interpreted retained RTL | Both modules' complete register updates and outputs agree for arbitrary represented state and two-state inputs. The package interpretation inherits the certified session theorem. The Yosys frontend/lowering and restricted adapter remain trusted. All six RTL faults and two injected axioms are rejected. |
| Original host RTL ↔ validation-isolated RTL | The host MLIR and RTL match the original side of the recorded arbitrary-state core/package SAT comparison. The isolated side matches the proof's emission. |
| Isolated RTL → balanced mapped circuit → implemented circuit | Recorded mapping SAT checks and the physical circuit's own SAT comparison consume the selected mapped readback. Their scopes include arbitrary defined state and independent SRAM response pins, with pinned cell functions trusted. |
| Implemented circuit → routed, repaired and filled circuit | Input hashes connect the routed identity check. Fresh comparisons of retained readbacks bridge filler removal and later finishing, preserving clocks and all signal connections. The five-buffer repair is freshly checked by contracting pinned noninverting buffers and checking its one declared input-only protection diode and receiver. |
| Final circuit → physical measurements | Timing identifies the selected ODB, netlist, SDC and SPEF. The SRAM interface study identifies the same exported GDS and candidate. Numerical timing is recomputed from the measured metrics. Library operating conditions are reread from the pinned Liberty bytes. |

The report preserves **three different kinds of evidence**: kernel proofs,
tool/structural implementation checks, and component/physical qualification.
The [artifact-interpretation proof](../storage/paired-rtl-interpretation.md) now
supplies the typed-circuit-to-RTL connection; subsequent implementation SAT and
cell-function checks retain their stated scope. A 351-pin SRAM boundary comparison does not
establish the macro's internals or stored behavior. Positive fast-screen hold
does not qualify a −40°C standard-cell / −55°C SRAM pair.

## What remains required

| Requirement | Current reason for refusing A |
| --- | --- |
| SRAM internal and behavioral qualification | The supplied source/layout resistor widths remain 0.260/0.200 µm. Exact-version internal qualification is absent; the digital SRAM law remains a theorem parameter. |
| Compatible timing conditions | Fast cells and SRAM use different temperatures. No applicable conservative bound or compatible delivered pair is established. |
| Package power delivery | Continuity passes. IR-drop uses default voltage-source locations and modeled activity, without qualified package assumptions. |

The declared proof envelope is canonical E64, 256 positions, 32 records, two
atomic banks and 290 upload words on the retained 20 ns, 6×4 platform. Resident
SHIFT/KEEP and analog board operation remain outside that certificate. The
historical area overage remains recorded; it is not silently converted into a
new rejection threshold. The 64-record B experiment and clean-source physical
replay are additional complete-iteration requirements.

The earlier host and final-netlist pin replays are retained observations,
explicitly labeled as not replayed by this command. There is no new silicon,
analog sampling or production-admission claim.

## Validation

```sh
python3 -m unittest discover -s test -p 'test_design_acceptance.py' -v
```

The focused controls reject missing/changed/conflicting artifacts, disconnected
candidate identities, receipts that did not consume their selected input,
incomplete executed checks, missing/duplicate requirements, source/certificate
mismatches, wrong image formats, signal-bearing filler cells, changed clocks
and hidden state. They also check late source edits, duplicate/nonfinite JSON,
Liberty condition disagreements, output preservation and rejection under
optimized Python. New controls refuse partial interpreted interfaces,
unapproved proof dependencies, missing session composition and relabeled or
omitted fault checks. A passing formal row cannot waive physical requirements.

The current `design-acceptance-readback-01` intake completes in **80.463 seconds**,
checking **740 input files**, **75 evidence connections** and **eight fresh kernel
certificates**. Its 11 rows have seven scoped passes, one conditional digital
proof and three blockers. The retained RTL receipt separately passes in
**315.149 seconds** with 1,082 local equivalences, total component/session
correspondence and fault rejection. All **20 acceptance tests** pass normally
and under `python -O`; all seven importer tests also pass in both modes.

The historical `design-acceptance-03` intake completed in **111.130 seconds**, checking
**572 input files**, **58 identity/measurement connections**, and **eight fresh
kernel certificates**. Its 11 requirement rows contain six scoped passes, one
conditional proof and four blockers. `--require-accepted` returns **2**, as
required. All inputs remain unchanged during assessment; 16 captured certificate
and log artifacts are retained. All **17 focused tests** pass normally and under
`python -OO`; the optimized run has its own frozen receipt.

The first intake is retained as `design-acceptance-01`: it refused the electrical
repair because the initial consolidation used buffer contraction without its
declared protection-diode check. The corrected intake verifies the one
input-only diode and its actual protected receiver before contraction. Wrong
receiver, extra diode and output-capable master controls reject. No physical
artifact or earlier verdict changed to obtain the completed assessment.

The second intake completed with the same verdict. The final source audit added
the indirectly loaded execution grammar to the explicit checker freeze and
host-source comparison; the third intake independently repeated all eight
kernel checks. Both completed receipts are retained.

The original nine selected manifests, preceding formal receipt, component
proposal and candidate artifacts retain their recorded hashes. The new selection
adds the interpretation manifest without overwriting earlier assessments. There are **zero CAD calls**;
campaign usage remains **8,412.163 CAD seconds**, three A routes used and two B
routes reserved. The report's `campaign` object preserves the last SRAM study's
ledger; the new intake's own `cad_seconds` is zero. Work remains local.

## Next useful step

The [physical qualification assessment](../physical/physical-qualification-assessment.md)
identifies two provider dependencies: authoritative SRAM interpretation and
qualification, and compatible fast characterization or an applicable bound.
Its local follow-up is a saved-layout power experiment after source geometry,
external impedance and activity become declared inputs. The assessment leaves
this acceptance intake and all three blockers unchanged. A remains unaccepted;
the capacity-B change and clean-source physical replay retain their own gates.
