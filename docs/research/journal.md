# Research journal

Concise reconstruction index. [Results](results.md) owns interpretations and
[status](status.md) owns current priorities. Detailed commands and hashes stay
with the technical study and run artifacts. Append decisive receipts; do not
replace a failed attempt with its successful retry.

## 2026-09-15 — Research records consolidated

This is a retrospective index, reconstructed from existing documentation and Git
history through `2aa281c`. Dates below are commit dates, not asserted run start or
finish times. No experiment was registered prospectively by this backfill, no
historical resource total was inferred, and no hardware suite was rerun for it.
Missing historical timestamps and budgets remain unrecorded.

Consolidation validation checked 124 local documentation links, 23 historical
commit identities, preservation of every former README study link, and 15
receipt hashes across the fetch and targeted-timing manifests. All passed,
as did the documentation whitespace check. This verifies reconstruction links
and receipt identities, not a fresh execution of their experiments.

| Commit date / identity | Milestone and outcome | Reconstruction path |
| --- | --- | --- |
| 2026-09-13 / `145ce99`, `034915a` | Counted I²C equivalence and binary-image comparison completed | [Loop study](../looped-i2c.md), [binary record](../binary-images.md); `build/binary/`, `build/binary-explicit/`, `build/binary-looped/` |
| 2026-09-13 / `1ef8196`, `f8d557d`, `8c20d44` | Bounded register reads, E64 lowering, and frontend hardware comparison | [Read record](../i2c-register-read.md), [E64 decision](../execution-records.md), [frontend record](../execution-hardware.md) |
| 2026-09-14 / `696a6d6`, `a493b06`, `2780f1d` | Integrated reactive core, atomic loader, and mapped area pressure | [Core](../reactive-core-hardware.md), [loader](../atomic-loader.md), [mapping](../technology-mapping.md); `build/reactive-core/report.json`, `build/loader/report.json`, `build/technology/report.json` |
| 2026-09-14 / `2dacc2a`, `7a66c08`, `fd6db7d`, `c368fac`, `4a8a06a` | Smaller store, cache, dense records, bounded repetition, and primitive review completed | [Storage study](../storage-study.md), [primitive review](../storage-primitives.md); `build/storage/` and its candidate-specific receipts |
| 2026-09-14 / `a0e2fb9`, `7dcd064` | Initial routed baseline; timing fails, DRC/LVS evidence retained | [Physical record](../physical-validation.md); `build/physical/core/runs/routed4/` |
| 2026-09-14 / `2946f20`, `e3bfbbb`, `6aac575`, `ae61ff2` | Timed refinement and checked interfaces; baseline emission preserved | [Contract record](../timed-components.md); `build/contracts/` is regenerable and may now describe a later source snapshot; recover the historical source with these commits |
| 2026-09-14 / `d9d76d2`, `820187c` | Two architectural screens and both final flow controls completed; no timing closure or promoted architectural candidate | [Fetch study](../successor-fetch-study.md), [committed result manifest](../../physical/experiments/fetch-results.json) |
| 2026-09-14 / `5c0b03c` | Unaffected-command predicate proved; decoder follow-up identified | [Study rationale](../successor-fetch-study.md#command-decoder-experiment); `Pinwheel/Hardware/Storage/Small.lean` at that commit |
| 2026-09-15 / `2aa281c` | Targeted STA shows protocol and loader paths remain nearly tied; decoder-only cleanup cannot establish closure | [Timing study](../successor-fetch-study.md#targeted-launch-family-timing), [pinned launch-family receipts](../../physical/experiments/fetch-launch-families.json) |

Earlier UART/SPI and I²C foundations remain indexed by the [technical catalog](../README.md)
and their original study records; this table is a milestone index, not a complete
attempt ledger.

The fetch manifest pins retained receipts for `fetch-fanout-route`,
`fetch-repair-route`, `late-index-screen`, and `late-record-screen`, with source
and artifact identities. Both physical flows ended with setup-check failure.
The earlier `late-index-initial` attempt passed its comparisons but stopped on a
mutation-harness assumption; its artifacts remain distinct from the completed
screen. These failures are part of the history.

## 2026-09-15 — Command-decoder screen closed

The decoder work was still underway during the initial consolidation above. Its
validated implementation is now `1a0c960`, with the closeout committed in `5d89d95`.
Run identity: `command-split-screen`. This receipt incorporates that completed work;
it does not rerun the experiment or replace the earlier reconstruction snapshot.

- **Change:** capacity validation no longer feeds commit/start decoding; push
  rejection and other adapted uses retain their behavior.
- **Proof/checks:** exact structural pre/post-edge trace preservation; 102 audited
  declarations using standard Lean axioms; 21,864 independent edges, 13,444,072
  storage observations, and 3,585,618 defined output-bit comparisons. Capacity-bypass
  and output-inversion mutations fail as intended. Default emitted bytes are unchanged.
- **Mapping:** about 1.1% less cell area, unchanged 6,226 flip-flops, about 9.8%
  better typical ABC delay, and only about 0.19% change in the slow estimate.
- **Connectivity:** loader data reaches none of the 57 retained cache-register
  data inputs in either candidate mapping, versus all 57 in the baseline. Protocol
  inputs still reach all 57. This is a within-cycle connectivity result, not
  extracted timing or a claim that loaded data never affects execution.
- **Verdict/allocation:** dependency-removal hypothesis supported; proceed to one
  matched physical comparison within the applicable task authority. The candidate
  is not routed or promoted. The −4.928 ns protocol slack belongs to the previously
  routed F2 implementation, so decoder isolation alone does not establish closure.
- **Evidence:** [detailed closeout](../successor-fetch-study.md#command-decoder-experiment)
  and [committed manifest](../../physical/experiments/command-split-results.json),
  with retained source/artifact hashes under `build/successor-fetch/command-split-screen/`.
  The manifest pins the screen, connectivity, and contract-audit receipts.
  Resource totals are not recorded in this concise closeout.

The proof concerns structural two-state circuit semantics. Dense emission/CIRCT
remain independently tested translation boundaries. [Current status](status.md)
records the physical comparison and its acceptance gates.

## 2026-09-15 — Hardware correspondence batch

The authorized ordering preserves reference execution semantics, closes the
countdown artifact slice, composes one selected backend, specifies external
timing, and measures physical feasibility separately. Implementation starts from
`c133af9`; the new proof and validation receipts pin the working source hashes.
The physical candidate remains the previously validated RTL from `1a0c960`.

- **Countdown:** actual emitted RTL read-back has Lean transition/trace proofs;
  38,026 independent edges match, eight invalid import shapes and three corrupted
  RTLs are rejected, and all 19 RTL/generic-gate comparison points pass.
- **Composed backend:** the 32-entry dense cached netlist has a full state
  relation, including the reference machine's initializing transition from an
  arbitrary corresponding prior state. Explicit typed wires make successor/PC
  sharing part of the proved object. Old/new RTL and generic gates pass all
  comparison points; independent storage and mapped-corner checks pass.
- **External contract:** two-edge digital input-pipeline latency and ideal
  open-drain interpretation are proved. No wrapper or serial transport is
  implemented, and no analog detection-time bound is claimed.
- **Supplemental gates:** both the composed generic netlist and frozen
  command-split implemented netlist pass 21,864 edges / 3,585,618 defined output-bit
  comparisons and reject output corruption. The first generic-netlist attempt
  passed behavior but exposed an invalid mutation caused by substring replacement;
  its failed attempt and corrected fresh receipts are retained separately.
- **Failed attempts retained:** tree-expanded emission exceeded five minutes
  in both interpreted and compiled execution. Typed shared bindings resolved
  the generation cost. A direct gate check left 172 points unresolved; one-step
  induction discharged them in a fresh run. None of these earlier attempts is
  relabeled as a full pass.
- **Physical measurement:** matched F2 controls reproduce the same constraint
  boundary. Worst setup remains about −5.05 ns; loader-cursor-to-cache becomes
  critical. Area falls about 0.91%, setup violations increase and hold margin
  decreases. The one-hour attempt exits 124 during Magic DRC, after routing and
  final extracted STA. OpenROAD routing/antenna checks report zero violations;
  Magic DRC, LVS and later checks are incomplete. No default promotion follows.

[Hardware closure](../hardware-closure.md) owns exact proofs, trusted boundaries,
suite counts, current receipt hashes and elapsed validation times.
[The matched physical study](../successor-fetch-study.md#matched-command-split-physical-comparison)
owns the extracted comparison and final flow receipt. The new candidate-specific
physical staging rejects wrong artifact hashes and reused preparations; the
runner bounds the named offline container to four CPUs, 6 GiB and one hour.
Sixteen disposable-file provenance/staging/timeout tests pass and are selected
by CI. Historical aggregate resource use remains unknown.

The final portable receipt is `build/validation/hardware-closure-final/report.json`
(588.878 seconds, 109 modules, 9,125 declarations / 4,665 theorems, all 20 suites).
The final backend receipt is `build/backend/closure-initialized/report.json`
(105.018 seconds); its emitted bytes match the earlier inductive run.
The [physical result manifest](../../physical/experiments/command-split-physical-results.json)
has SHA-256 `6bba2ca232bc2af62da9f8730eedbda0c0ddcb082c301d02746dd80e7991f2bf`
and pins the timeout, completed timing and netlist evidence, and incomplete checks.

The resulting next discriminator is full-backend artifact interpretation, with
technology-mapped equivalence and external integration still distinct. For the
physical track, diagnose the registered loader-control dependency before a new
screen. [Status](status.md) owns that allocation.

## 2026-09-15 — Full-backend RTL read-back

The follow-up closes artifact interpretation for the selected 32-entry dense
cached backend. Lean checks all 607 register updates / 6,233 bits and all 33
outputs against the typed netlist, then composes its initialized reference trace
theorem. The reference execution and capacity semantics remain unchanged.

The method uses the actual CIRCT-emitted SystemVerilog, Yosys word-level
read-back, and a restricted JSON adapter. MLIR expressions, sampled signatures
and Z3 answers propose proof boundaries; every accepted equality must pass Lean.
There are 3,209 local equalities for this artifact, with a largest expression of
212 nodes. Explicit congruence and read-stage proofs connect them to the composed
circuit. The final audit permits only the standard Lean axioms.

Oversized direct reductions were stopped. Splitting the index and dictionary
reads, retaining their padding relationships, and proving control identities
locally made the check practical. The rejected attempts remain under
`build/backend/readback-explore/`; they are not successful proof receipts.

The unchanged RTL reimport passes. Lean rejects six compilable corrupted RTL
fixtures covering initialization, uploading, capture, PC output, rejected commands
and cache updates. Portable tests reject 23 unsupported import shapes, check 280
comparison/reduction cases, and reject altered source/proof/RTL receipt identities.

The fresh read-back receipt is `build/backend/readback-closure/report.json`
(975.757 seconds, 65,076 declarations / 40,037 theorems including generated
proofs). `build/backend/readback-equivalence/report.json` binds that receipt to
byte-identical MLIR/RTL and passes all 6,315 / 6,309 equivalence points plus the
21,409-edge / 13,151,052-observation independent regression (92.752 seconds).
The library audit alone passes 9,194 declarations / 4,690 theorems. All current
source hashes match the receipts; no reference execution semantics changed.

[Full-backend read-back](../hardware-closure.md#full-backend-rtl-read-back) owns the
reproduction commands, exact receipts and remaining trusted frontend/adapter
boundary. Technology-mapped sequential equivalence, external integration and the
separate failed physical-timing comparison retain their own obligations.

## 2026-09-15 — Program-bank selection screen

The approved experiment retains reference semantics and selects between two
complete bank reads to shorten the registered loader-cursor dependency. A new
composed command-split control makes both variants explicit typed Lean netlists.
The whole transition and initialized trace refinement are proved for each, and
the existing restricted RTL read-back method checks both actual emitted artifacts.

- **Proofs:** 607 register fields / 6,233 bits and 33 outputs per variant; 3,209
  control and 3,214 candidate local equalities. All six compilable RTL corruptions
  are rejected for each. Audits accept only standard Lean axioms. Full read-back
  takes 1,004.539 and 923.856 seconds respectively.
- **Independent checks:** each passes all 6,315 legacy/variant and 6,309
  RTL/generic-gate equivalence points, 21,409 loader edges and 13,151,052 storage
  observations. A focused 2,090-edge oracle covers four bank alternations,
  consecutive last-upload/commit/start, reset and 128 live-input branches; wrong
  bank, early commit and stale cache corruptions are rejected. Downstream checks
  take 92.361 and 96.801 seconds.
- **Mapping:** typical/slow area rises 2.073% / 2.067%; typical ABC delay worsens
  6.599% and slow improves 0.153%. All mappings retain 6,226 flip-flops. Cursor
  logic depth drops 32 → 25, protocol depth grows 35 → 38, and loader data reaches
  none of the 57 cache inputs. These are structural/mapping observations, not STA.
- **Disposition:** the candidate misses the useful slow-corner improvement gate.
  Retain it and stop before routing; no default promotion. None of the conditional
  two-run allocation (four CPUs / 6 GiB / one hour per run) was used.
- **Evidence:** [study](../bank-selection-study.md) and
  [manifest](../../physical/experiments/bank-selection-results.json), SHA-256
  `67edb492f0f4067912dc5a89b03c7d492ea3b2c813cde14f989d2f335ea820bc`.
  The manifest pins both proof/check receipts, initial/final focused cases and
  the cone report. The initial cone-report invocation failed on naming a
  symlinked tool library and published no receipt; the completed report records
  its configured path and actual hash. The source and generated artifacts remain
  local and uncommitted.

The legacy physical RTL hash is reproduced exactly, but the composed control has
different bytes. Prior routed timing is therefore not assigned to either new
variant. The next hypothesis concerns factoring the cache update selector by
idle/running state; no enable-independence proof or second candidate is claimed.

## 2026-09-15 — Cache-update enable screen

The approved follow-up changes the cache update decision on the proved
command-split control. It compares PC alternatives at their leaves and exposes
the running case's reset/start/metadata rules. The shared instruction read,
storage format, capacity, reference semantics and every register update stay
fixed. The late bank-selection candidate is not combined with this change.

- **Functional evidence:** both full emitted-RTL proofs, initialized reference
  traces, standard-axiom audits and six corruptions per variant pass. The control
  checks 3,209 local equalities and audits 65,301 declarations / 40,174 theorems;
  the candidate checks 3,230 and audits 65,605 / 40,375. Read-back takes 996.059 /
  1,057.938 seconds. Both downstream gates pass 6,315 / 6,309 equivalence points,
  21,409 loader edges and 13,151,052 storage observations, in 101.633 / 101.293
  seconds respectively.
- **Focused cases:** each RTL passes 5,910 cache-focused edges / 5,585 exact-cache
  observations and 2,090 bank-switch/branch edges. The six focused compilable
  mutations are rejected. Stopped cache contents, same/different-address branches,
  halt/fault/reset from PC zero/nonzero and busy commit rejection are covered.
- **Mapping:** typical/slow cell area falls 0.375% / 0.452%; ABC delay falls
  9.108% / 1.312%. Cursor/protocol logic depth falls 32 → 28 / 35 → 32; command
  and reset paths also get shallower. Both retain 6,226 mapped flip-flops and
  maximum combinational fanout 10. These are mapping/graph results, not STA.
- **Hypothesis boundary:** the full next-PC wire and direct cursor/command paths
  leave the enable. An indirect path through the shared successor read remains.
  The result therefore establishes partial structural isolation, with no timing
  exception or duplicated instruction lookup.
- **Failed attempts:** the strict importer first rejects unsigned inequality;
  the added adapter rule passes 344 truth-table cases and rejects 27 unsupported
  shapes. Generated congruence fallbacks handle reflexive comparisons. The first
  positive proof's audit rejects two native-evaluation dependencies; explicit
  kernel-checked cases replace them before both fresh full runs. Exploratory
  path/receipt invocation failures remain separate from completed receipts.
- **Disposition and identity:** retain the verified experimental variant; the
  matched screen supports a fresh physical comparison, with a modest slow gain.
  No new physical run or default promotion occurs. The
  [study](../cache-enable-study.md) and
  [manifest](../../physical/experiments/cache-enable-results.json), SHA-256
  `31db9ddf62ce3bb257f624a8f8f06145a5abb9e457554a10e0eeb1238a1913a8`,
  pin eight completed receipts and 914 verified source/artifact hash entries.
  The fresh composed control remains byte-identical to its earlier proved RTL;
  legacy routed timing stays attached to the different legacy artifact.

All source and evidence changes remain local and uncommitted. The next formal
obligation remains technology-mapped equivalence; physical measurement and
external interface integration retain their separate contracts.

## Future receipt shape

Record the actual date, study/run identity, source commit or candidate digest,
evidence location and digest, completion/interruption state, concise result,
resource accounting when available, and link to the result or current status.
For outside research, link the source interpretation and adoption decision in the
owning study. Interpretation-only updates need no fabricated run identity.
