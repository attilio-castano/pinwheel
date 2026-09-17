# Cache-update enable experiment

Closed on 2026-09-15. The control and candidate pass complete Lean circuit and
emitted-RTL proofs, equivalence, independent regressions and corruption checks.
The candidate reduces typical/slow mapped delay estimates by 9.11% / 1.31% and
cell area by 0.38% / 0.45%. Direct control dependencies leave the enable; an
indirect cursor path remains through the shared instruction read. Retain the
experimental variant. No physical run or default promotion follows from this
implementation-and-mapping batch. The
[result manifest](../physical/experiments/cache-enable-results.json) pins the evidence.

## Scope and hypothesis

Authorized on 2026-09-15 as a follow-up to the
[program-bank selection screen](bank-selection-study.md). Test a local
cache-update decision on the proved composed command-split control. The selected
instruction read, storage capacity, reference execution semantics, all register
fields and all external cycles remain fixed. The late bank-selection candidate
is not part of this experiment.

The original cache decision is `!running || next_pc != pc`. The retained physical
critical path enters its update selector. Idle already implies an update; while
running, commit and start are disabled. The hypothesis is that making those facts
explicit and calculating a one-bit address-change decision directly can shorten
the control path without duplicating the instruction lookup.

`Storage/CacheEnable.lean` distributes the comparison through the scheduler's
choices, so each leaf decides whether its address differs from the old PC. Hold
compares the old PC with itself; halt, fault and reset compare zero; an ordinary
entry compares the selected target. The running case uses raw reset/init/valid
inputs and active-bank length metadata, with start fixed to zero. Idle always
enables the update. Full register-update and initialized-trace equalities are
proved against the existing backend, for arbitrary corresponding state values.

The successor word remains a shared input to the decision. Its validity and halt
decoding can therefore retain an indirect cursor path through the unchanged bank
lookup. The screen must report that residual path rather than treating local
command isolation as removal of every loader dependency. No false-path exception
or physical closure claim follows from the logical proof.

## Evidence gates

1. Build the whole Lean library with warnings as errors; accept only standard
   axioms. Check all register updates, outputs and initialized traces.
2. Reimport actual emitted RTL into the restricted word-level model and check
   complete correspondence in Lean. Retain unchanged and corrupted reimports.
3. Bind each artifact to its proof receipt; check legacy/variant and generic-gate
   equivalence, independent loader/storage regressions and both mapping corners.
4. Check exact cache contents on hold, same/different-address branches, halt,
   faults, reset from PC zero/nonzero, and a full pending upload during execution.
5. Compare area and complete cache data/control paths under matched settings.
   Advance physically only with a useful slow-corner gain and viable area cost.
   Any physical comparison needs a fresh composed control with the original
   constraints; prior routed timing belongs to different RTL bytes.

Commands use fresh tags/output paths to retain earlier attempts:

```sh
python3 scripts/check-backend-readback.py --variant command-split --tag CONTROL_PROOF
python3 scripts/check-bank-select.py --readback-report build/backend/CONTROL_PROOF/report.json --tag CONTROL_CHECK
python3 scripts/check-backend-readback.py --variant enable-split --tag CANDIDATE_PROOF
python3 scripts/check-bank-select.py --readback-report build/backend/CANDIDATE_PROOF/report.json --tag CANDIDATE_CHECK
python3 scripts/check-cache-enable-cases.py --control build/backend/CONTROL_CHECK/composed.sv --candidate build/backend/CANDIDATE_CHECK/composed.sv --testbench build/backend/CONTROL_CHECK/measured/tb.sv --output build/backend/CACHE_CASES
python3 scripts/check-bank-select-cases.py --control build/backend/CONTROL_CHECK/composed.sv --candidate build/backend/CANDIDATE_CHECK/composed.sv --testbench build/backend/CONTROL_CHECK/measured/tb.sv --output build/backend/BANK_CASES
python3 scripts/report-bank-select.py --control build/backend/CONTROL_CHECK/measured --candidate build/backend/CANDIDATE_CHECK/measured --output build/backend/CONES.json
python3 scripts/report-cache-enable.py --control build/backend/CONTROL_CHECK --candidate build/backend/CANDIDATE_CHECK --output build/backend/ENABLE_DEPENDENCIES.json
```

## Validation development

The new SystemVerilog contains `!=`, which Yosys represents as `$ne`. The
restricted importer initially rejects it. The adapter now translates equal-width
unsigned `$ne` into one-bit inverted equality, with 344 exhaustive small-width
comparison/reduction cases and 27 unsupported-shape checks. Signed operands,
unequal operand widths and multi-bit comparison results remain rejected. This is
an explicit extension of the trusted JSON interpretation boundary.

The first generated congruence proof fails on `pc == pc`: simplification reduces
one side to true while the source definition remains folded. A narrowly scoped
fallback unfolds that source definition in Lean. An intermediate attempt to
unfold every source node triggers unused-rewrite errors and is retained. Local
proof instantiation also needs the same reflexive-comparison normalization as a
fallback. None of these failed attempts is a successful RTL proof receipt.

The exploratory positive proof reaches all register/output endpoints, but its
final audit rejects native-evaluation axioms introduced by the default bit-vector
tactic in two new lemmas. Explicit one-bit cases and bit-vector rewrite lemmas
replace those proofs. The rebuilt library audit passes 9,408 declarations /
4,825 theorems using only standard axioms. The old compiled generated proofs
retain the rejected dependencies; fresh full runs must regenerate them.

The initial focused case receipt is `build/backend/enable-cases-initial/report.json`.
Both RTLs pass 5,910 edges, including 5,585 exact cache checks. Always-hold,
always-refresh and reset-retains-cache mutations compile and fail the oracle.
This check observes cache contents on stopped edges as well as the original
running-state invariant. Initial RTL checks use the retained control artifact;
the final comparison will bind the fresh receipts.

An exploratory source-graph check confirms that the cache update decision no
longer consumes the complete next-PC wire. With the shared successor word treated
as an abstract input, cursor and command dependencies disappear and no dictionary
or index register is read outside that input. The complete graph still contains
cursor/command paths through the shared lookup and successor decoding. This
distinguishes removal of the direct control dependency from the remaining
indirect path; the abstracted view is not a physical timing exception.

The first exploratory mapping call stops on a relative-output path before
simulation. The helper now normalizes its output directory to an absolute path;
the final downstream gate checks this version. A direct exploratory cone-report
call also stops because it lacks the required downstream receipt. Only reports
bound to the complete downstream checks count as final comparison evidence.

## Functional validation

`build/backend/enable-candidate-proof/report.json` checks all 607 register fields /
6,233 bits and 33 outputs. Its 3,230 local equalities have at most 213 expression
nodes. The audit covers 65,605 declarations / 40,375 theorems and permits only
standard axioms. Unchanged reimport passes and all six compilable corruptions
are rejected. The complete run takes 1,057.938 seconds.

`build/backend/enable-candidate-check/report.json` binds that proof to the same
emitted bytes. All 6,315 legacy/variant and 6,309 RTL/generic-gate comparison
points pass, along with 21,409 independent loader edges and 13,151,052 storage
observations. The cache corruption is rejected. This gate, including both
technology mappings, takes 101.293 seconds.

The refreshed control proof is `build/backend/enable-control-proof/report.json`:
3,209 local equalities, a largest expression of 213 nodes, and an audit of 65,301
declarations / 40,174 theorems using only standard axioms. Unchanged reimport and
all six corruption checks pass. It takes 996.059 seconds. Its MLIR and RTL remain
byte-identical to the earlier proved command-split control.

`build/backend/enable-control-check/report.json` completes the same downstream
gate in 101.633 seconds: all 6,315 / 6,309 equivalence points, 21,409 loader edges,
13,151,052 storage observations and both technology mappings pass. Both variants
use matching tool versions and settings. The whole library build, six portable
importer/receipt tests and two bank-cut/sequential-boundary tests pass.

The final focused receipts are `build/backend/enable-cases-final/report.json`
and `build/backend/enable-bank-cases-final/report.json`. Each design passes 5,910
cache-focused edges with 5,585 exact cache checks, plus 2,090 bank-switch/branch
edges. Always-hold, always-refresh, reset-retains-cache, wrong-bank, early-commit
and stale-cache fixtures all compile and fail the independent oracle. These
receipts use the fresh control emission and the candidate gate's independently
generated testbench; their RTL hashes match the final matched receipts.

## Matched mapping and dependency screen

| Metric | Control | Candidate | Change |
| --- | ---: | ---: | ---: |
| Typical cell area (µm²) | 546,109.9056 | 544,060.5786 | −0.375% |
| Slow cell area (µm²) | 546,547.1760 | 544,075.0938 | −0.452% |
| Typical ABC delay (ns) | 7.10618 | 6.45893 | −9.108% |
| Slow ABC delay (ns) | 9.95550 | 9.82485 | −1.312% |

Both variants retain 6,226 mapped flip-flops. Total mapped cell count rises about
2.2% despite the smaller cell area. These are full-core mapping estimates, without
routed parasitics or full physical STA.

The full mapped cache cones improve for every measured launch family. Logic
depth excludes buffers; cell depth includes them. Traversal stops at every
Liberty-declared flip-flop. Loader data reaches no cache input; every other family
reaches all 57 retained cache input pins. Maximum combinational fanout remains 10.

| Launch family | Control typical/slow cell depth | Candidate typical/slow cell depth | Logic depth, both corners |
| --- | ---: | ---: | ---: |
| Loader cursor | 47 / 47 | 40 / 40 | 32 → 28 |
| Protocol inputs | 48 / 49 | 45 / 45 | 35 → 32 |
| Commands | 45 / 45 | 40 / 40 | 32 → 29 |
| Reset/init | 45 / 45 | 39 / 39 | 32 → 28 |

`build/backend/enable-dependencies.json` confirms that the new enable no longer
uses the full next-PC wire. With the shared successor word abstracted, cursor
and command dependencies disappear and no dictionary/index register is read
outside that input. In the complete source graph, cursor/command paths remain
through that shared read; cursor-to-enable expression depth falls from 51 to 46.
This is a partial result for the original removal hypothesis, with no physical
path exception. `build/backend/enable-cones.json` owns the mapped graph counts.

**Decision:** retain `enable-split` as a verified experimental variant. Both
corners improve without an area penalty, and the complete measured cache paths
get shallower. This supports a fresh matched physical comparison, while the slow
gain remains modest. A fresh composed control is needed: its RTL differs from
the legacy routed artifact. No new physical run was consumed, and no routed
timing, electrical closure or default promotion is claimed.

## Artifact identities

The control RTL is
`318930699f99e92eae489eee05c0ad2cdca9f8e34d6aeb2f7a07fe0fc6c6f764`;
the candidate RTL is
`ac7b8617254320fd8f249c0871a3cb1617a2d1a8bb75896782e1bd2c8492ee79`.
The unchanged legacy physical RTL remains
`1a1fd62b6e17bcdf584abaf7b9733c3e28eab1ab7ce565057588139504cc5a42`.

The [result manifest](../physical/experiments/cache-enable-results.json), SHA-256
`31db9ddf62ce3bb257f624a8f8f06145a5abb9e457554a10e0eeb1238a1913a8`,
pins both fresh proof/check pairs, the two focused regressions, the mapped cone
report and the source dependency report. All eight receipts and 914 recorded
source/artifact hash entries match current bytes, including both focused suites'
positive RTLs. Earlier failed attempts remain separate from these completed
receipts. All changes remain local and uncommitted.
