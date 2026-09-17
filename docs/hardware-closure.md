# Hardware correspondence closure

This batch closes the countdown artifact slice, the complete Lean refinement
of one composed dense cached netlist, and Lean-checked read-back of that backend's
emitted RTL. The separate physical comparison
still misses 20 ns; its one-hour attempt ends during layout checking.

## Scope and fixed contracts

Authorized on 2026-09-15: preserve the reference instruction/loader semantics,
close the countdown artifact slice, compose one exact general backend, develop
the external timing contract, and continue physical feasibility separately.
The selected composed backend is the 32-entry dense cached design, with its
existing 322-word upload and capacity rejection. The command-split candidate is
the separate physical experiment; neither choice promotes a new default.

Local proofs, generation, tests, and one offline matched physical attempt are
within this batch. No publication, deployment, or remote execution is involved.
The physical attempt uses four CPUs, a 6 GiB container limit, one hour maximum,
the pinned PDK/container, F2 controls, the unchanged 20 ns clock/I/O constraints,
and the diagnostic 6x4 floorplan. Historical cumulative resource use is unknown;
this is one newly bounded attempt. Stop on a failed identity/check, memory/time
limit, or completed run, and retain the result. Do not hide failures by changing
the physical contract. Proof/emission checks run locally, without parallel Lean
builds; inspect any long generation attempt before increasing its allocation.

## Countdown: artifact interpretation rather than a compiler proof

`scripts/check-hardware.py` now reads the actual CIRCT-generated SystemVerilog
through the pinned Yosys Verilog frontend and `proc; opt_clean`. The restricted
`scripts/countdown_import.py` interpreter accepts only the exact ports, two
positive-edge registers, unsigned same-width combinational primitives, and
fully driven acyclic wiring. Unsupported cells, clocks, widths, initial values,
and unknown bits are rejected.

The interpreter writes a Lean transition/observation definition from that JSON.
Lean proves `Pinwheel.Artifact.Countdown.model_correct` for every input and
nine-bit register state. `trace_correct` derives equality of every pre/post-edge
observation for arbitrary finite input histories. The theorem uses the existing
`Countdown.circuit`; reset/load priority and duration conventions are unchanged.
Both theorem audits allow only the standard Lean axioms. Three corrupted RTL
fixtures must fail their correspondence theorem.

Yosys separately checks generated RTL against the synthesized generic netlist
with `equiv_make`, `equiv_simple`, and `equiv_status -assert`. All 19 comparison
points (state plus outputs) must be proved. A corrupted decrement must fail that
same gate. Initial state correspondence equates the two copies' register bits;
it does not assume independently arbitrary power-up values agree. A synchronous
reset establishes the defined countdown state. This is two-state digital
evidence, complemented by the existing uninitialized-RTL simulation.

The trusted boundary includes Yosys's Verilog/process interpretation, the small
JSON-to-Lean adapter, and the Yosys equivalence engine. CIRCT/emission errors are
checked for this artifact; this is not a universal theorem about either tool.
Generic gates are the endpoint, not technology-mapped gates or physical timing.
Receipt: `build/hardware/report.json`, with exact source/artifact hashes and logs.

The completed check matches all 38,026 independent deadline edges, rejects three
corrupted RTLs in both simulation and Lean correspondence, rejects eight invalid
import shapes, and rejects the corrupted decrement in the gate-equivalence check.
The final import guards also reject a constant or multiply driven clock. Earlier
successful evidence is retained in `build/hardware-before-clock-guards/`.

## Composed backend

`Hardware/Storage/Backend.lean` defines the physical register widths, wiring,
functional interpretation, and complete refinement. `BackendNetlist.lean`
introduces two typed combinational bindings for successor data and next PC.
`Netlist.lean` gives these bindings an explicit meaning: inputs extend in order,
all expressions see the same pre-edge registers, and only the final circuit
updates state. Its types exclude forward references and combinational cycles.
`BackendEmit.lean` supplies only port/register names to the generic netlist
emitter. It emits the exact `Backend.netlist` covered by
`netlistCompleteRefinement` and `netlist_initialized_trace`.

This representation change was necessary for practical emission. Expanding every
shared expression into a tree exceeded five minutes both in the Lean interpreter
and a compiled generator. Both attempts were stopped and retained as failed
generation attempts. The compiled version with explicit bindings emitted in
1.66 seconds on this host (one diagnostic observation, not a benchmark study).
The binding-to-reference proof preserves every register update and output;
there are no additional registers or execution edges.

The state relation expands both 55-bit dictionaries, zero-extends both five-bit
index banks, supplies canonical upper padding, and relates the current-word
cache to the active program when running. Initialization establishes the cache
invariant without assuming initialized memories. `initialize_machine_next`
explicitly equates the initializing transition with the reference machine's own
transition from the corresponding prior state, without a prior cache invariant.
For arbitrary power-up state, the trace guarantee begins after that edge; it
does not constrain pre-initialization observations. `trace_correct` and
`initialized_trace` preserve all existing outputs before and after every edge
for arbitrary host commands and input histories. The reference includes the
existing capacity adapter: rejecting an oversized push is part of this backend's
contract. The unrestricted 64-entry reference remains available separately.

`scripts/check-backend.py --tag NAME` builds and audits the library, emits the
composed and existing dense cached designs, and checks their RTL equivalence.
It separately synthesizes the new RTL and checks generic-gate equivalence, then
reuses the existing independent loader/storage/cache regression and two mapped
corners. Each fresh tag retains sources, artifacts, commands, logs, and hashes.

The direct RTL/gate check initially left 172 comparison points unresolved.
One-step induction discharged them: all 6,309 points were proved. This result
assumes the recorded matching state/comparison relation, including constants
for eliminated register bits; it does not equate independently arbitrary power-up
values. It is tool-checked sequential equivalence, not a Lean theorem or bounded
simulation. The full-backend artifact proof below supplies the separate Lean
connection to the emitted RTL. No default or physical
baseline changes follow from an equivalence pass alone.

Completed receipt: `build/backend/closure-initialized/report.json` (105.018 seconds
on this host). Old/new RTL passes all 6,315 comparison points; RTL/generic gates
passes all 6,309. The independent regression passes 21,409 loader edges and
13,151,052 physical storage observations, with held-cache corruption rejected.
The circuit declares 607 register fields / 6,233 bits; both mappings retain
6,226 flip-flops after eliminating unused/constant bits.

| Composed mapping | Cell area (µm²) | ABC delay (ns) | Cells |
| --- | ---: | ---: | ---: |
| Typical | 553,659.0570 | 7.72774 | 28,281 |
| Slow | 554,753.1402 | 9.96433 | 28,319 |

These are mapping estimates for the composed emission, separate from the frozen
command-split physical candidate below. They establish no routed timing result.
The failed direct gate check remains under `build/backend/closure/`; the successful
inductive run has its own identity and does not erase that attempt.
The earlier initialized run strengthens startup correspondence and audits 9,125 declarations /
4,665 theorems. Its MLIR, RTL and generic netlist are byte-identical to the earlier
`closure-inductive` artifacts used by the supplemental gate regression.

The synthesized generic netlist also passes the frozen command-split workload:
21,864 edges and 3,585,618 defined output-bit comparisons, including continuous
one-cycle branches. Reference-X bits are excluded. This is a supplemental
regression against retained fixtures, not fresh fixture generation or a new
universal proof. Its receipt is
`build/physical/composed-gates-validation-check/report.json`.

The initial supplemental run's positive simulation passed but its mutation
failed to compile: the checker changed `r_levels[0]` while trying to invert
`levels[0]`. That attempt remains under `build/physical/composed-generic-gates-check/`.
The corrected checker mutates only the output and rejects a compilable corruption
for both generic and implemented netlists, with fresh successful receipts.

## Portable validation and next formal boundary

`build/validation/hardware-closure-final/report.json` passes all 109 reachable modules,
9,125 declarations / 4,665 theorems under the standard-axiom audit, and all 20
executable suites. Counts include generated declarations/theorems. The injected
untrusted axiom is rejected. Elapsed time was 588.878 seconds on this host.
The reference engine, compilers, protocol models, and atomic-loader definitions
are unchanged by this batch. Physical preparation/timeout/provenance tests pass
in disposable directories without running CAD tools.

CI selects all 16 physical preparation/checkpoint/timeout tests; its exact command
passes locally. That portable gate includes the strengthened startup theorem
and its recorded CI configuration. Every source hash matched at that run. The earlier
successful gate remains separately under `build/validation/hardware-closure/`.

| Receipt | SHA-256 |
| --- | --- |
| `build/hardware/report.json` | `00a4ebca19cdc606a371da66e1da2655365b3cf61778e4af7c635e6f8a13a052` |
| `build/backend/closure-initialized/report.json` | `2bf8a87a208e8a845fe832722ad905cf791475e8dd11aeff752cbfbe72d23f19` |
| `build/validation/hardware-closure-final/report.json` | `dd8526507f36928232931f1e2c26e215f02a92aaad4515fe3454c383e543356f` |
| `build/backend/readback-closure/report.json` | `9ecd3345406e107b64ac5f3657ac204d8f452415fce993d8b503276f03e8bf24` |
| `build/backend/readback-equivalence/report.json` | `b2b98b366fbf5b57d7bacc9a8094bcaefb10f7c75e85bdaacebc33658f7dd7c6` |

The receipts contain source/artifact identities and logs. These ignored local
files must be retained to recover their contents; the digests are not backups.

The practical method selected here is artifact validation. The full-backend
extension below checks the emitted transition against the composed Lean circuit.
Technology-mapped sequential equivalence remains another endpoint, separate from
the generic gates checked in this batch.

## Full-backend RTL read-back

`scripts/check-backend-readback.py --tag NAME` regenerates the selected backend,
reads its actual SystemVerilog through Yosys `proc; opt_clean`, and writes a
restricted Lean interpretation of the resulting word-level JSON. The importer
requires all 607 named registers / 6,233 bits and all 33 output ports. It rejects
unmodeled clocks, state, initial values, signed/implicitly resized operations,
unknown bits, multiple drivers, incomplete ports and combinational cycles.

The generated `Proof.lean` proves:

- `Pinwheel.Artifact.Backend.model_next`: every imported register update equals
  `Backend.netlist.step`, for every corresponding register state and input.
- `model_output`: every imported output equals `Backend.netlist.observe` on the
  same cycle, including loader status, samples and read addresses.
- `initialized_trace`: after an initializing edge, every pre/post-edge output
  in any finite input history equals the capacity-adapted reference machine.

This covers uploads, capacity rejection, commit/start, execution, faults, resets,
capture and cache updates through the same total transition relation. It retains
the existing 322-word upload contract and initialization relation. It assumes
two-state signals, positive clock edges, simultaneous register updates and the
modeled memory timing. It does not assert defined pre-initialization observations
for independently arbitrary physical power-up values.

The proof is divided into 3,209 local equalities for the current artifact. Matching
signatures and Z3 suggest cuts; Lean proves each accepted equality with ordinary
proof tactics. The largest local expression has 212 nodes. Explicit congruence
proofs reconnect the cuts to the actual imported expressions. Separately,
`Storage/BackendReadback.lean` supplies index/dictionary read stages, and generated
proofs connect every source hint to `Backend.netlist`. The emitted MLIR supplies
untrusted hints; it is not accepted as an independently trusted reference.

The final theorem audit permits only `propext`, `Classical.choice` and `Quot.sound`.
No native-evaluation axiom or solver result discharges a theorem. Yosys's
Verilog/process interpretation and the restricted JSON adapter remain trusted.
This validates the recorded emission and CIRCT result; it is not a universal
correctness theorem for either translator.

The gate independently reimports unchanged RTL and requires its checked
certificate to pass. It then compiles and imports corrupted initialization,
upload-cursor, capture, PC-output, rejection and cache-update fixtures; Lean must
reject the original certificate for each. Portable tests reject 23 invalid import
shapes and check 280 comparison/reduction truth-table cases.

Every fresh tag retains generated Lean sources, RTL/MLIR/JSON, commands, logs,
tool versions and source/artifact hashes in `build/backend/NAME/report.json`.
To bind the proof to a fresh downstream equivalence/regression run:

```sh
python3 scripts/check-backend-readback.py --tag readback-closure
python3 scripts/check-backend.py --tag readback-equivalence \
  --readback-report build/backend/readback-closure/report.json
```

The second command verifies the read-back receipt's hashes and requires the
regenerated MLIR and RTL to match it exactly. Its generic-gate equivalence remains
tool-checked under the recorded matching-state relation. Technology-mapped
sequential equivalence, external integration and physical closure remain separate.

Completed receipts: `build/backend/readback-closure/report.json` (975.757 seconds)
and `build/backend/readback-equivalence/report.json` (92.752 seconds). The artifact
audit checks 65,076 declarations / 40,037 theorems, including generated proof
declarations; the library alone checks 9,194 / 4,690. Both permit only standard
axioms. All six corruption checks pass. The matched downstream run proves all
6,315 old/new RTL and 6,309 RTL/generic-gate points, and passes 21,409 loader edges
and 13,151,052 storage observations. Source/artifact identities match across both
receipts. The composed MLIR and RTL are byte-identical to `closure-initialized`.

## Separate physical discriminator

Freeze the exact command-split RTL identified by
`physical/experiments/command-split-results.json` using
`prepare-physical.py --validated-command-split PATH`. A mismatched hash or an
existing prepared design is rejected. This imports a previously validated
artifact; it does not claim that current sources regenerated it.

Run identity: `command-split-closure`, starting at synthesis, with
`physical/experiments/fanout-repair.json`. The composed emission is not substituted
into this experiment. Resolved controls match F2 apart from run/RTL paths.

Final three-corner extraction gives −5.049 ns worst setup, versus F2's −5.055 ns.
Cell area excluding fill falls about 0.91%, while setup violations increase to
1,426 and worst hold margin shrinks to about 2.9 ps. Electrical violations remain.
The worst path now starts at loader cursor bit 5 and ends in the current-word
cache. The implemented-netlist regression passes all 21,864 edges and 3,585,618
defined output-bit comparisons, with output corruption rejected.

The attempt exits **124**, with `stop_reason = wall_time_limit`, during Magic DRC.
Its last completed step is `63-odb-checkdesignantennaproperties`. Routing and final
STA completed; OpenROAD routing DRC and antenna checks report zero violations.
Magic DRC, LVS and later flow checks are incomplete. The runner stopped the named
container at the one-hour cap, and no additional physical attempt was started.

The [physical result manifest](../physical/experiments/command-split-physical-results.json)
pins receipts/artifacts, matched controls, launch-family timing and incomplete
checks. [The physical study](successor-fetch-study.md#matched-command-split-physical-comparison)
owns the detailed comparison. The candidate is not promoted. Diagnose the
registered loader-control dependency before another screen; completing layout
checks would not repair the measured timing failure.

See [external timing](external-interface.md), [research status](research/status.md),
and [processor verification](processor-verification.md) for the surrounding boundaries.
