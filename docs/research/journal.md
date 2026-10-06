# Research journal

Dated reconstruction record. [Results](results.md) owns interpretations and
[status](status.md) owns current priorities. Detailed commands and hashes stay
with the technical study and run artifacts. Append decisive receipts; do not
replace a failed attempt with its successful retry.

## Find a receipt

Choose a topic or date to jump to the sequence of attempts, including failed
or interrupted work.

### By topic

| Topic | Entry points |
| --- | --- |
| Local iteration and retained replay | [Portable A, fresh-source interpretation and power request](#2026-09-29--portable-a-fresh-source-interpretation-and-power-request) |
| Protocols and pin timing | [Bounded I²C writes and bus clear](#2026-09-29--bounded-i2c-writes-and-bus-clear), [Four-mode SPI and resolved package wires](#2026-09-29--four-mode-spi-and-a-resolved-package-interface), [continuous UART with unequal clocks](#2026-09-15--continuous-uart-reception-with-unequal-clocks), [input-latency contract](#2026-09-17-input-latency-as-a-contract-parameter) |
| Artifact proof and composition | [Paired RTL interpretation](#2026-09-28--retained-paired-rtl-interpretation-and-refreshed-acceptance), [Hardware correspondence](#2026-09-15--hardware-correspondence-batch), [whole chip in Lean](#2026-09-18-the-whole-chip-in-lean--feeders-serial-loader-upload-theorem) |
| Storage and fetch | [Memory abstraction](#2026-09-17-memory-abstraction), [complete SRAM comparison](#2026-09-19-complete-sram-chip-comparison), [closed-loop execution](#2026-09-21--verified-placement-corridors-and-closed-loop-sram-execution) |
| Map and execution architecture | [Complete map slice](#2026-09-21--complete-map-slice-and-read-tree-tile-costs), [tiled chip](#2026-09-22--complete-chip-tile-integration-passes-function-fails-structural-screen), [paired controller](#2026-09-22--complete-paired-controller-exact-mapped-replay-and-macro-timing) |
| Physical correlation and placement | [Estimate/extraction diagnosis](#2026-09-17-estimateextraction-correlation-diagnosis), [placement corridors](#2026-09-21--verified-placement-corridors-and-closed-loop-sram-execution), [exact mapping and hold repair](#2026-09-22--preserve-the-mapping-through-placement-and-hold-repair) |
| Repair and admission | [Whole-chip signal repair](#2026-09-23--whole-chip-qualification-of-the-27-buffer-signal-repair), [rejected shared-edit route](#2026-09-23--shared-physical-edits-and-a-rejected-whole-chip-qualification), [timing and organization comparison](#2026-09-23--timing-obligations-and-complete-organization-comparison), [saved-route import controls](#2026-09-26--saved-route-import-controls) |

### By date

| Date | Start of that day's entries | Main threads |
| --- | --- | --- |
| 2026-09-15 | [UART stream clocks](#2026-09-15--continuous-uart-reception-with-unequal-clocks) | Protocols, compilers, decoder and backend screens |
| 2026-09-17 | [Physical correlation](#2026-09-17-estimateextraction-correlation-diagnosis) | Sampler, structural timing, input latency, memory policies |
| 2026-09-18 | [Fetch organizations](#2026-09-18-fetch-organizations-as-a-parameter-the-one-port-backend) | One/two-port backends and whole-chip composition |
| 2026-09-19 | [Branch review](#2026-09-19-local-branch-review-and-submission-plan) | SRAM comparison, integration and routing diagnosis |
| 2026-09-21 | [Placement corridors](#2026-09-21--verified-placement-corridors-and-closed-loop-sram-execution) | Closed-loop SRAM, hybrid/direct costs and tile boundaries |
| 2026-09-22 | [Complete-chip tile](#2026-09-22--complete-chip-tile-integration-passes-function-fails-structural-screen) | Mapping, library load, placement, compact/paired execution |
| 2026-09-23 | [Paired local repair](#2026-09-23--paired-local-repair-with-fresh-coarse-wire-estimates) | Full-route requalification, organization and timing diagnosis |
| 2026-09-26 | [SRAM distribution and write timing](#2026-09-26--sram-distribution-and-write-timing), [competing read paths](#2026-09-26--control-distribution-and-competing-read-paths), [coordinated placement](#2026-09-26--coordinated-status-and-decode-placement) | Complete watchlist, matched coarse routes, rejected regional placement and clock/hold diagnosis |
| 2026-09-29 | [Portable continuation](#2026-09-29--portable-a-fresh-source-interpretation-and-power-request), [four-mode SPI](#2026-09-29--four-mode-spi-and-a-resolved-package-interface), [bounded I²C](#2026-09-29--bounded-i2c-writes-and-bus-clear) | Replay portability, power-request boundary and established-protocol capabilities |

## Future receipt shape

Record the actual date, study/run identity, source commit or candidate digest,
evidence location and digest, completion/interruption state, concise result,
resource accounting when available, and link to the result or current status.
For outside research, link the source interpretation and adoption decision in the
owning study. Interpretation-only updates need no fabricated run identity.

## 2026-09-15 — Continuous UART reception with unequal clocks

Closed the [continuous clock milestone](../protocols/uart-stream-clocks.md), based on
`c133af9` plus the previously validated receive/link/buffered-stream work.
The strengthened sufficient bound reserves two additional RX ticks for rearm
and an idle-high observation between adjacent frames. It preserves the entire
ideal shared-period domain of 8–256.

- **Proofs:** continuous-wire prefix and suffix agreement, preserved timing
  conditions after rearm, and exact completion pulses for any finite payload
  list under unequal constant clocks and varying bounded observation age.
  The theorem composes through the existing compiled RX supervisor, leaving
  consumer controls, initial buffer contents, and spare input history arbitrary.
- **Validation:** `build/validation/uart-stream-clocks-01/report.json`, SHA-256
  `4c37c8bfffb9b7664564f58bf024172de510c044680498d9424cb63c84de22e5`.
  All 24 suites and both independent oracles passed in 1,012.316 seconds.
  The default import reaches 125 modules; 10,058 declarations and 5,254
  theorems pass the standard-axiom audit. The injected axiom is rejected;
  all 179 source hashes stayed unchanged during validation and at closeout.
- **Stream coverage:** 392 streams, 38,808 frames, 10,531,120 RX edges, and
  13,056 candidate detection windows across three successive frames. The
  independent timing/wire/queue checks retain four failing-assumption examples
  and one successful excluded phase. The study owns the stream receipt and
  exact delivery/drop/pending balance. Its concrete Lean example compiles.
- **Decision:** adopt the sufficient continuous clock contract. The prior
  single-frame-safe rearm failure is excluded by it. Receiver lifecycle during
  atomic replacement is the next proposed Lean integration question. Physical
  sampling, repeated TX launches, supervisor/buffer circuitry, and concurrent
  TX/RX still need their own designs and evidence. No CAD run was added.

The first focused attempt failed at the exploratory successful-excluded example:
start time 301 left no idle-high observation after rearm. Moving it to 300
produced the intended example. The failed command, output, and source hash remain
in `build/uart-stream-clocks/focused-attempt-01.json`. A later test improvement
held TX start fixed while varying RX phase; the final focused check passed.
Neither correction changed the numerical proof.

All 173 prior baseline source hashes matched before work. Only the library import
and gate registration changed among those sources; five new library modules and
one new regression suite implement this milestone. The receiver, buffer, engine,
and earlier compilers retain their source identities. Source hashes identify the
uncommitted work; ignored receipts are not a durable backup.

## 2026-09-15 — Continuous UART receive and result ownership

Closed the [continuous receive milestone](../protocols/uart-stream.md), based on `c133af9`
plus the previously validated receive/link work. The one-entry buffer retains
the oldest unread outcome, supports same-edge consumption and arrival, reports
sticky overrun, and explicitly flushes on reset. Automatic rearm is independent
of consumer readiness.

- **Proofs:** occurrence ordering and complete loss accounting for arbitrary
  buffer histories; receiver independence from consumer controls; exact finite
  ideal back-to-back result pulses at every shared period 8–256; and complete
  state/receipt correspondence through the existing compiled RX and Lean supervisor.
- **Validation:** `build/validation/uart-stream-01/report.json`, SHA-256
  `666fa5a60e9052c9d2b64322d7e5acce1d38e26c750fb6b533cc1d16fb441f66`.
  All 23 suites and both independent oracles passed in 882.133 seconds.
  The default import reaches 120 modules; the audit covers 10,015 declarations
  and 5,221 theorems with standard axioms only. The injected axiom is rejected,
  and all 173 source hashes stayed unchanged during validation and at closeout.
- **Stream coverage:** all 65,536 ordered byte pairs, 11,844,449 RX edges, 128
  buffer combinations, and 37 reset/error/rearm boundary cases. The study owns
  the stream receipt and count balance. Its public Lean example also compiles.
- **Decision:** adopt the receive ownership and rearm contract at the Lean level.
  A retained counterexample satisfies single-frame clock bounds but misses the
  next start during rearm, without buffer overrun. The next Lean discriminator
  is continuous unequal-clock reception with an explicit rearm/idle-high bound.
  Supervisor/buffer circuitry, physical sampling, loader composition, and
  concurrent TX/RX remain separate. No CAD or physical-closure result was added.

The prior 164 baseline source hashes were verified before work. Only the library
import and gate registration changed among those sources; eight new library
modules and the stream suite hold this implementation. Source hashes identify
the uncommitted work; ignored receipts are not a durable backup.

## 2026-09-15 — UART link timing and compiler roundtrip

Closed the [one-frame UART link proof](../uart-link.md), based on `c133af9` plus
the prior UART receive work. Numerical conditions on independent clocks and
bounded digital observation age imply start detection, every sample value,
and recovery of the transmitted byte. Both compiler paths compose with this
result. The ideal theorem covers every byte and shared bit period 8–256.

- **Validation:** `build/validation/uart-link-01/report.json`, SHA-256
  `349f049c242dcfa3bee4bf00c858b6cabdcde2a2759f11d69e1cf3748771f138`.
  All 22 suites and both independent oracles passed in 757.769 seconds.
  The default import reaches 112 modules; 9,434 declarations and 4,949 theorems
  pass the standard-axiom audit, and the injected custom axiom is rejected.
- **Link coverage:** 3,872 frames, 5,614,752 RX edges, and 1,136 safe timing
  combinations. Four failing-assumption cases and one successful excluded case
  preserve the distinction between sufficient and necessary timing bounds.
  The technical record owns the focused report digest and complete coverage.
- **Decision:** adopt the digital link contract and compiler composition.
  The next Lean question is successive frames, delivery ownership, buffering,
  and overrun. A concrete physical sampler must justify its age contract;
  simultaneous TX/RX remains separate. This run used local Lean/model checks
  and added no RTL, mapping, routing, or physical-closure result.

The gate retained source hashes and verified source stability during its run.
The documented unequal-clock example compiles. Earlier RX receipts below remain
historical evidence for their own source snapshot.

## 2026-09-15 — One-byte UART receive

Added the [digital receive contract and compiler](../protocols/uart-receive.md) in the
working tree based on `c133af9`; validation identities are source hashes rather
than an implementation commit. The receiver confirms start, samples eight bits
and stop, and retains either a byte or a framing error. Existing reactive
instructions, E64, the atomic loader, and dense cached storage provide execution.

- **Proofs:** armed byte recovery, exact compiler state/step/run correspondence,
  and decoded-store composition. The whole-library audit admits only the three
  standard Lean axioms; the injected custom axiom is rejected.
- **Portable gate:** `build/validation/uart-rx-01/report.json`, SHA-256
  `e1604250db30252bb8ef22fe68dce5c058420c2a4857aaef593cb314b6dec1c8`;
  21 suites and both independent Python oracles passed in 708.568 seconds.
  All 13,298 supported period/input configurations fit, with maxima of 250
  instructions and 16 dictionary records. Four corrupted receive programs fail.
- **Hardware integration:** `build/uart-rx/hardware/uart-rx-01/report.json`, SHA-256
  `66c7c37dc8d659939dc9666b94c11c7d4130cd34aeb1a0ab357270acf518a496`;
  direct/indexed structural and RTL checks, atomic structural checks, and atomic
  indexed/default dense cached RTL passed. Each backend includes nine new RX
  scenarios within the existing protocol/loader suite. The cache mutation fails.
  Runtime was 247.881 seconds; the portable gate ran concurrently.
- **Decision:** the existing engine can express this receive capability without
  a new opcode or circuit. The next receive obligation is the asynchronous-input
  latency contract; buffering, overrun and concurrent TX/RX need separate design.
  No synthesis, routing, operating-frequency qualification, or physical default
  promotion was performed. Frozen timed-contract fixtures were not replaced.

The detailed study owns exact coverage, commands, timing assumptions and remaining
boundaries. Both tagged validation runs passed. Ignored local receipts are not a
durable backup; the source runners regenerate new evidence.

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
| 2026-09-13 / `145ce99`, `034915a` | Counted I²C equivalence and binary-image comparison completed | [Loop study](../protocols/looped-i2c.md), [binary record](../storage/binary-images.md); `build/binary/`, `build/binary-explicit/`, `build/binary-looped/` |
| 2026-09-13 / `1ef8196`, `f8d557d`, `8c20d44` | Bounded register reads, E64 lowering, and frontend hardware comparison | [Read record](../protocols/i2c-register-read.md), [E64 decision](../storage/execution-records.md), [frontend record](../storage/execution-hardware.md) |
| 2026-09-14 / `696a6d6`, `a493b06`, `2780f1d` | Integrated reactive core, atomic loader, and mapped area pressure | [Core](../engine/reactive-core-hardware.md), [loader](../storage/atomic-loader.md), [mapping](../physical/technology-mapping.md); `build/reactive-core/report.json`, `build/loader/report.json`, `build/technology/report.json` |
| 2026-09-14 / `2dacc2a`, `7a66c08`, `fd6db7d`, `c368fac`, `4a8a06a` | Smaller store, cache, dense records, bounded repetition, and primitive review completed | [Storage study](../storage/storage-study.md), [primitive review](../storage-primitives.md); `build/storage/` and its candidate-specific receipts |
| 2026-09-14 / `a0e2fb9`, `7dcd064` | Initial routed baseline; timing fails, DRC/LVS evidence retained | [Physical record](../physical/physical-validation.md); `build/physical/core/runs/routed4/` |
| 2026-09-14 / `2946f20`, `e3bfbbb`, `6aac575`, `ae61ff2` | Timed refinement and checked interfaces; baseline emission preserved | [Contract record](../engine/timed-components.md); `build/contracts/` is regenerable and may now describe a later source snapshot; recover the historical source with these commits |
| 2026-09-14 / `d9d76d2`, `820187c` | Two architectural screens and both final flow controls completed; no timing closure or promoted architectural candidate | [Fetch study](../storage/successor-fetch-study.md), [committed result manifest](../../physical/experiments/fetch-results.json) |
| 2026-09-14 / `5c0b03c` | Unaffected-command predicate proved; decoder follow-up identified | [Study rationale](../storage/successor-fetch-study.md#command-decoder-experiment); `Pinwheel/Hardware/Storage/Small.lean` at that commit |
| 2026-09-15 / `2aa281c` | Targeted STA shows protocol and loader paths remain nearly tied; decoder-only cleanup cannot establish closure | [Timing study](../storage/successor-fetch-study.md#targeted-launch-family-timing), [pinned launch-family receipts](../../physical/experiments/fetch-launch-families.json) |

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
- **Evidence:** [detailed closeout](../storage/successor-fetch-study.md#command-decoder-experiment)
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

[Hardware closure](../engine/hardware-closure.md) owns exact proofs, trusted boundaries,
suite counts, current receipt hashes and elapsed validation times.
[The matched physical study](../storage/successor-fetch-study.md#matched-command-split-physical-comparison)
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

[Full-backend read-back](../engine/hardware-closure.md#full-backend-rtl-read-back) owns the
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
- **Evidence:** [study](../storage/bank-selection-study.md) and
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
  [study](../storage/cache-enable-study.md) and
  [manifest](../../physical/experiments/cache-enable-results.json), SHA-256
  `31db9ddf62ce3bb257f624a8f8f06145a5abb9e457554a10e0eeb1238a1913a8`,
  pin eight completed receipts and 914 verified source/artifact hash entries.
  The fresh composed control remains byte-identical to its earlier proved RTL;
  legacy routed timing stays attached to the different legacy artifact.

All source and evidence changes remain local and uncommitted. The next formal
obligation remains technology-mapped equivalence; physical measurement and
external interface integration retain their separate contracts.

## 2026-09-17: estimate/extraction correlation diagnosis

- **Scope:** read-only analysis of the retained `command-split-closure` run plus
  one scratch pair of synthesis-only container runs (about 38 s each, two CPUs,
  no network). No place-and-route run, Lean change or RTL change.
- **Result:** the resizer's final slow-corner view is +0.055 ns against −5.049 ns
  extracted. Fitted extracted capacitance is 0.161 / 0.192 / 0.139 fF/µm on
  Metal2–4 versus about 0.092 fF/µm estimated. Hold repair contributes 6,423
  delay cells. Clock gating reduces mapped area 578,449 → 505,878 µm² in the
  unrecorded screen.
- **Disposition and identity:** the [study](../physical-correlation-study.md)
  owns the measurements; routed DEF SHA-256 `e668da67060aca2bc12d57651229cdfe97cbf95c58d1674bce1b5f0fd5db6a04`,
  nominal SPEF `6d4df224254d646f6a117353b5df429d3e261c250ee5dbd499117bd972b2b536`.
  `scripts/fit-wire-rc.py` and its unit test reproduce the fit. The screen has no
  retained receipt and supports only a recorded follow-up.

## 2026-09-17: calibrated-estimate physical run `rc-calibrated-01`

- **Scope:** one user-authorized bounded run (four CPUs, 6 GiB, one-hour cap,
  stop after `OpenROAD.STAPostPNR`), command-split RTL
  `1a1fd62b6e17bcdf584abaf7b9733c3e28eab1ab7ce565057588139504cc5a42`, unchanged
  constraints/floorplan, overlay `physical/experiments/rc-calibrated.json`.
  Tools and PDK are symlinked from the foundation worktree; the PDK identity
  check passed. Exit 0, about 35 minutes of step time.
- **Result:** extracted slow setup −0.153 ns (was −5.049 ns), 56 violating
  endpoints (was 1,426), no slew/capacitance violations, 25 fanout violations.
  Magic DRC/LVS not run. Worst path now launches from the `incoming[1]` port.
- **Disposition and identity:** config SHA-256
  `7ffe348d4ecf9295d9f86ffdda6581a7ca74f14076b14dace3751cf99c2fc0cc`; final STA
  summary `2d195b98c0ec085a3dbeb9ffef06f5a0ddddf96104398293884ed87983f2cd10`.
  Adopt calibrated estimates as the control for further flow comparisons; no
  default promotion or closure claim. The [study](../physical-correlation-study.md)
  owns the table.

## 2026-09-17: clock-gated physical attempt `clock-gated-01` (failed)

- **Scope:** second bounded run under the same authorization and limits;
  calibrated control plus Yosys clock gating with `sg13cmos5l_lgcp_1`.
- **Result:** exit 2 at `OpenROAD.GlobalRouting` (`GRT-0116`, overflow 526, 515 on
  Metal3) after about 13 minutes. Post-CTS-repair cell area 604,627 µm² versus
  742,324 µm²; utilization 67.0% versus 82.3%. No routed design or final timing.
- **Disposition:** retain the failed evidence. A retry needs its own allocation
  and one stated change; see the [study](../physical-correlation-study.md).

## 2026-09-17: clock-gated retry `clock-gated-02` (failed)

- **Scope:** one authorized retry; only `PL_TARGET_DENSITY_PCT` 70 → 62 added to
  the clock-gated overlay. Same limits, RTL, constraints and floorplan.
- **Result:** the first three global routes pass with zero overflow. Exit 2 at
  `OpenROAD.ResizerTimingPostGRT` (`GRT-0116`): after antenna repair the global
  route overflows by 3 on Metal3 (70.0% of derated capacity). No routed design
  or final timing.
- **Disposition:** retain the failed evidence under
  `build/physical/core/runs/clock-gated-02/`. The area result (−18.5% after
  clock-tree and hold repair) stands; routability is unresolved. See the
  [study](../physical-correlation-study.md).

## 2026-09-17: pin-sampler proofs, artifact checks and physical attempts

- **Scope:** Lean wrapper/refinement work, emitted-artifact checks, and bounded
  physical runs under the user's authorization to carry the input pipeline into
  the physical design (four CPUs, 6 GiB, one-hour cap each, calibrated flow).
- **Proof/artifact result:** `Netlist.extend`, pair traces, `PinSampler.trace_eq`,
  `Sampled.trace_correct`/`initialized_trace`/`reference_registered` and the UART
  `Safe.delayed`/`pipelined_observe` lemmas build with warnings as errors.
  Foundation gate `build/validation/pin-sampler-01/report.json`: 142 modules,
  10,927 declarations / 5,683 theorems, standard axioms only, 25 suites,
  1,093 s. `build/sampled/cs-02/report.json` (re-run as `cs-03` on final sources
  with identical artifacts): inner RTL identical to the read-back-proved control
  `318930699f99e92eae489eee05c0ad2cdca9f8e34d6aeb2f7a07fe0fc6c6f764`; sampled RTL
  `3e6cf6bea9a4435ffcbc7fcbde57f255f68a28ce3bf3093533a865994a9442a1`; 6,319 / 6,313
  equivalence points; 28,165 oracle edges; four rejections.
- **Physical result so far:** `composed-control-01` exits 0 with slow setup
  −0.797 ns, all 67 violating paths launched from `incoming` ports and the next
  family at +3.380 ns. `pin-sampled-01` exits 2 at the first global route with
  overflow 1 on Metal3. `pin-sampled-02` retries with `GRT_ALLOW_CONGESTION`.
- **Disposition:** the [study](../pin-sampler-study.md) owns measurements and the
  trust boundary; the identity manifest is
  `physical/experiments/pin-sampled-results.json`. No default promotion.

## 2026-09-17: sampled candidate routes and meets extracted timing (`pin-sampled-02`)

- **Scope:** one further bounded run (same limits); only `GRT_ALLOW_CONGESTION`
  added to the calibrated overlay (`physical/experiments/rc-calibrated-tolerant.json`),
  inert for the zero-overflow control.
- **Result:** exit 0. Slow setup +0.090 ns with no violating endpoints (control
  −0.797 ns, 67, all launched from `incoming`); typical/fast +5.912/+8.204 ns;
  worst hold +0.052 ns; 4 slew, 1 capacitance and 17 fanout violations; functional
  area 732,103 µm² (control 743,469). Global routes tolerated overflow of
  1, 1, 3, 75 and 41; detailed routing and the antenna check finish with zero
  violations. Implemented-netlist regression: 28,165 edges, 4,618,982 defined
  output-bit comparisons, mutant rejected. Magic DRC/LVS not run.
- **Disposition and identity:**
  [physical manifest](../../physical/experiments/pin-sampled-physical-results.json);
  the [study](../pin-sampler-study.md) owns interpretation. One run, no margin
  against the observed spread between equivalent RTLs; no promotion or claim.

## 2026-09-17: clock-gated design routes (`clock-gated-03`)

- **Scope:** one user-authorized bounded run (same limits); `GRT_ALLOW_CONGESTION`
  added to the 62%-density clock-gated overlay. Follow-up gate simulations and one
  scratch synthesis-only screen; no further physical run.
- **Result:** exit 0; global overflow 0, 0, 0, 3, 0; zero detailed-routing and
  antenna violations. Functional area 608,454 µm² versus 748,353 (−18.7%),
  utilization 67.4%, wirelength 1.670 m. Slow setup −0.617 ns / 16 endpoints, all
  launched from `incoming`; worst hold +0.0034 ns; 11 slew and 18 fanout
  violations. Netlist regression passes with the original (28,165 edges) and
  extended (29,062 edges) vectors. Stuck clock-gate enables rejected: 84/134
  with the original vectors, 134/134 with the extended ones.
- **Disposition and identity:**
  [manifest](../../physical/experiments/clock-gated-physical-results.json);
  the [study](../physical-correlation-study.md#third-attempt-clock-gated-03-routes)
  owns interpretation. `scripts/measure-storage-variant.py` now exercises every
  dictionary word, so fresh regression counts differ from earlier receipts.
  No promotion or claim; Magic DRC/LVS not run.

## 2026-09-17: combined sampler and clock-gating attempts `combined-01`/`-02`

- **Scope:** user-authorized combined run: pin-sampled RTL
  `3e6cf6bea9a4435ffcbc7fcbde57f255f68a28ce3bf3093533a865994a9442a1` with
  `physical/experiments/combined.json` (calibrated estimates, width-8 clock gating,
  62% density, tolerated global overflow, hold-repair margins 0.15/0.10 ns).
- **`combined-01` (infrastructure failure):** exit 125; the Docker client lost its
  connection (`error waiting for container: unexpected EOF`) during the 11th
  detailed-routing iteration. No cause found; the daemon and image were intact
  afterwards. This is not a flow result.
- **`combined-02` (wall-time limit):** identical configuration; its first ten
  detailed-routing iterations reproduce `combined-01` exactly. Exit 124 at the
  one-hour cap in the 39th iteration with five Metal2/Metal3 spacing violations
  left (21,548 initially). All five global routes finish with zero final
  overflow (208 transiently). Pre-route: 607,329 µm², 67.3% utilization; hold
  repair reaches its 0.10 ns target; the resizer's setup estimate ends at
  −1.118 ns. Ungated designs need 17–19 detailed-routing iterations (22–24 min),
  `clock-gated-03` 35 (28.5 min): gated designs are markedly harder to
  detail-route despite lower utilization.
- **Disposition:** `combined-03` resumes at `OpenROAD.DetailedRouting` from the
  verified `combined-02` step-45 checkpoint
  (`build/physical/combined-02-step45-checkpoint.json`) with a 90-minute cap for
  this one run; detailed routing restarts from its first iteration.

## 2026-09-17: combined run completes (`combined-03`) and corrects a launch-family claim

- **Scope:** resume of the authorized combined run from the verified `combined-02`
  step-45 checkpoint, 90-minute cap for this run; per-family extracted STA on four
  retained designs; gate-level functional checks.
- **Result:** exit 0; detailed routing 58 iterations / 71 min to zero violations.
  608,058 µm², 67.4% utilization, worst hold +0.059 ns, slow setup −2.251 ns (40
  endpoints), 30 slew and 29 fanout violations. Families (slow, worst ns):
  `incoming` +14.496, `command` −2.251, `data` +0.116, `init`/`reset` −2.053,
  registers −2.054 (38 negative); all worst paths end at the `r_cached_word` clock
  gate. Regression 29,062 edges; 134/134 clock-gate mutants rejected.
- **Correction:** the earlier statement that no register-launched path violated
  in `composed-control-01` was wrong: the default report shows only the worst
  launch point per endpoint. Per-family STA gives registers −0.294 ns (64
  negative) there and +0.090 ns in `pin-sampled-02`. Study, status, results and the
  sampler manifest are corrected.
- **Disposition and identity:**
  [combined manifest](../../physical/experiments/combined-physical-results.json);
  the [study](../pin-sampler-study.md#combined-with-clock-gating) owns
  interpretation. `check-targeted-timing.py` now takes `--design`.

## 2026-09-17: structural timing model in Lean

- **Scope:** Lean definitions, theorems, a compiled report and a comparison with
  tracked manifests. No CAD tool, mapping or physical run.
- **Result:** `Hardware/Structure.lean` and the pin-isolation theorems build with
  warnings as errors; `test/StructuralTiming.lean` passes.
  `build/structure/validation-02/report.json`: 13 exact source depths, mapped-cone
  r = 0.954 over 12 points, 8 of 8 candidate directions, port-family ranking
  equal to extracted slack, deepest endpoint the cached word. Loop stages from
  registers (gate levels): address 22, successor 50, next address 91, enable 99,
  cached word 101. Recirculating bits 6,172 of 6,233.
- **Disposition:** the [study](../engine/structural-timing.md) owns the model, its
  boundary and the suggested abstractions. One early version of the report
  repeated wire evaluation inside a launch function and did not finish in ten
  minutes; wire arrivals are now computed as values first.

## 2026-09-17: certified register enables and Lean-chosen gating plans

- **Scope:** Lean definitions and proofs, report extension, a Yosys gating step
  with gate-level simulation and mapping. No placement or routing.
- **Result:** `Hardware/Enable.lean` and `Storage/EnabledBackend.lean` build with
  warnings as errors and standard axioms; `test/Enables.lean` passes. Shapes hold
  by `rfl` for both bodies. Plans: dictionary 66 gates / 3,536 bits, storage
  580 / 6,108, cached word never gated (SHA-256 `254d768dd0cadfc3…`,
  `c4cccf8bf225e359…` in `build/structure/validation-03/`). On RTL
  `318930699f99e92eae489eee05c0ad2cdca9f8e34d6aeb2f7a07fe0fc6c6f764`:
  `build/gated/none-02`, `dictionary-01`, `storage-01` match their plans, pass
  29,062 oracle edges with 18,079,584 storage observations, reject 132/132 and
  1,160/1,160 stuck-enable mutants, and map to 546,149 / 497,263 / 457,577 µm²
  (typical) with slow ABC delay 9.964 / 9.974 / 9.970 ns.
- **Disposition:** the [study](../physical/register-enables.md) owns the construction,
  boundary and open physical questions. A `clockgate` selection converted
  nothing in the pinned Yosys; the step unmaps the enables of unplanned registers
  instead. An empty-plan control first failed on an invalid `select -none`
  combination and is retained as `build/gated/none-01`.

## 2026-09-17: input latency as a contract parameter

- **Scope:** Lean definitions, theorems and one executable suite. No CAD tool.
- **Result:** `Pinwheel/Latency.lean`, `Hardware/InputLatency.lean`,
  `SPI/Latency.lean`, `Compile/SPILatency.lean`, `I2C/Latency.lean` and the UART
  corollary build with warnings as errors and standard axioms.
  `test/Latency.lean`: 600 SPI transfers correct inside `d + tco ≤ halfCycles`
  and `0xAA` misread one cycle beyond; 58 closed-loop I²C runs — the specified
  controller reports `busFault` after a complete wire transaction for
  `1 ≤ d ≤ phaseCycles`, the revised controller succeeds (also stretched, and with
  both NACKs), `d = phaseCycles + 1` faults before any clock pulse, wait budget
  `d` times out and `d + 1` succeeds.
- **Disposition:** the [study](../input-latency.md) owns the contracts and the
  open I²C recompilation. The premature-high hazard was found by the closed-loop
  suite (a `d = 3`, two-cycle-phase case faulted with no clock pulses) and then
  stated as a theorem.

## 2026-09-17: I²C recompiled for input latency

- **Scope:** both I²C reference controllers, the explicit, counted and
  register-read programs with their correspondence proofs, the independent
  vector generators, and the RTL regressions by simulation and equivalence.
  No place-and-route; no instruction-set or RTL change.
- **Result:** bus-free time after STOP is qualified like the interval before
  START (`I2C/Controller.lean`, `I2C/RegisterRead.lean`). Address 77, counted
  template 13 and read address 153 became the existing `qualify` record, identical
  to address 0; `advance_stopFree` and the read lift were re-proved and every
  downstream theorem builds unchanged. `I2C/Latency.lean` keeps the hazard as
  `guarded_stop_echo_faults` and adds `stop_echo_is_waited_out`,
  `blocked_prefix`, `rise_behind_pipeline` and `stop_completes_behind_pipeline`
  (also for the register read). Library audit: standard axioms only.
  `test/Latency.lean`: 111 write and 64 register-read closed-loop runs, reference
  and compiled. Images: 713 and 203 bytes (were 715 and 205); distinct E64 records
  for the write 13 (was 14), read 25; capacity sweep maxima 3/11/13/25.
  Gates rerun: `check-i2c`, `check-compiled-i2c`, `check-i2c-read`,
  `check-binary`, `check-reactive`, `check-execution`, `check-reactive-core`
  (40,881 direct and 45,297 indexed edges), `check-loader` (33,858 edges).
  `check-sampled --tag i2c-02`: 6,319 reference and 6,313 gate equivalence
  points; 35,824 edges with pins presented two edges early, among them eight
  closed-loop I²C runs behind the two registers and the former guarded record
  faulting after a complete wire transaction; unshifted and inner-shifted replays
  rejected; `sampled.sv` byte-identical to the routed candidate.
  `check-foundation --tag i2c-qualify-01`: 150 modules, 11,319 declarations,
  5,933 theorems, 28 suites, untrusted axiom rejected, 1,045 s. 38 Python unit
  tests pass.
- **Disposition:** the [study](../input-latency.md) owns the contract, the
  `d = 0` behaviour change (a line held low after STOP now ends in `timeout`, not
  `busFault`) and the remaining obligations. `check-reactive-core.py` had been
  failing on `main` since the fetch-choice and interface modules were added: its
  audit list lacked their 14 theorems and its rule assumed one namespace. Both were
  repaired so the gate could run; the theorems were already covered by the
  library-wide audit.

## 2026-09-17: memory abstraction

- **Scope:** Lean definitions, theorems and one executable suite. No CAD tool,
  no RTL change.
- **Result:** `Hardware/Memory.lean` (contract, `registered_refines`,
  `read_untouched`), `Memory/Flops.lean` and `Memory/Registered.lean`
  (refinements of latency 0 and 1, certified enables), `Storage/MemoryView.lean`
  (the loader image and the routed backend's words as instances) and
  `Storage/Prefetch.lean` (the reference machine against latency one:
  `refinement`, `trace_correct`, `initialize_valid`, `fetched_reads`). All build
  with warnings as errors; library audit standard axioms only (three cursor
  decode lemmas were first proved by `bv_decide`, whose native fallback adds an
  axiom the audit rejects, and are now arithmetic). `test/Memory.lean`: 400
  requests through both implementations against the specification; the prefetch
  machine closed-loop against the atomic reference on 4,754 edges (I²C write with
  ACK, address NACK and data NACK, register read for three bytes, UART, SPI, an
  image staged around a run and committed after it, resets, rejected commands),
  24 taken branches, no difference; a variant reading only the untaken candidate
  agrees until the first taken branch and then diverges. About 96 s interpreted.
  `check-foundation --tag memory-01`: 155 modules, 11,641 declarations,
  6,085 theorems, 29 suites, untrusted axiom rejected, 1,140 s.
- **Disposition:** the [study](../memory-abstraction.md) owns the contract, the
  prefetch machine and the boundary. It discharges the scheduling gate of the
  [primitive review](../storage-primitives.md) at the functional level: two read
  ports, next-state addresses, the map or the dictionary combinational. Whether
  to build the structural machine is a fit question for
  [status](status.md#next-discriminators).

## 2026-09-17: decoupled prefetch machine, structural backend, levels

- **Scope:** Lean machine and proofs, structural netlist and emission, the
  structural report, the independent RTL regression and generic mapping. Then
  one routed comparison against the pin-sampled candidate (below).
- **Result:** the prefetch machine's first structural form put the fetched
  registers at 103 gate levels (`build/structure/prefetch-01`): its addresses
  wait for the next-state decode. `Storage/Decoupled.lean` computes them from
  the dispatch decision (`advancing`, `dispatching`) and the target, with a
  start word loaded on commit; `step_structure` and `candidate_correct` carry
  the invariant, `refinement`/`trace_correct` reach the reference.
  `Storage/PrefetchBackend.lean` is its netlist on the general backend (three
  wires, 610 fields, 6,425 bits) with `netlist_next`, `netlist_output`,
  `reference_next` and `completeRefinement`; `PrefetchEmit.lean` emits it alone
  and behind the pin sampler. `build/structure/prefetch-02`: deepest register
  endpoint 63 levels (composed 101), cached word 38 (101), core state 59 (91),
  fetched words 63; from `incoming` 60 (99). `test/Memory.lean`: both machines
  match the reference on 5,161 edges, 12 transactions, 24 taken branches.
  Library audit standard axioms only (6,235 theorems).
  `check-prefetch --tag prefetch-03`: RTL/gate equivalence 6,373 (inner) and
  6,377 (sampled) points, oracle 35,824 edges on both, unshifted sampled trace
  rejected; mapped typical 636,986 µm² inner and 654,086 µm² sampled (sampled
  candidate 547,995), ABC delay 5,815 ps (6,803), 233 s. Identity manifest
  `physical/experiments/prefetch-results.json`.
  `prefetch-sampled-01` (calibrated tolerant overlay, 90-minute cap): exit 2 at
  `OpenROAD.ResizerTimingPostCTS`, detailed placement failed on 157 instances
  after clock-tree synthesis; 732,201 µm² of instances at 81.1% utilization before
  timing repair, so the 6×4 core has no room for the repair buffers. No routing,
  no extracted timing. `prefetch-sampled-02` (`combined.json`: calibrated RC,
  sampler, width-8 clock gating; 90-minute cap): placement and clock tree
  complete, 40,878 instances and 728,416 µm² at 80.7% utilization after
  post-CTS repair (the same-overlay control `combined-02`: 31,482, 604,090 µm²,
  66.9%); `OpenROAD.GlobalRouting` logged 858 congestion-removal iterations in
  84 minutes without clearing overflow (control: 29) and hit the wall-time limit
  (exit 124). Synthesis 32,182 instances, 618,435 µm² against 24,346 and
  507,042. No routing, no extracted timing. Manifest
  `physical/experiments/prefetch-physical-results.json`.
- **Disposition:** the [memory abstraction](../memory-abstraction.md) owns the
  machine, the levels and the boundary. Gate equivalence needs two-step
  induction because synthesis drops the constant top bit of each fetched word;
  no Yosys sequential equivalence to the composed RTL is claimed, the register
  sets differ. The routed comparison is negative by capacity, not a timing
  result: the decoupled backend does not fit the diagnostic floorplan with this
  flow's time budget, so the levels gain is unconfirmed after routing and the
  next physical question is area, not depth.

## 2026-09-17: one read port under a per-program rule

- **Scope:** Lean machine and proof, executable checks; no netlist, no mapping.
- **Result:** `Storage/SinglePort.lean` reads the untaken candidate on the entry
  edge and the taken one on the following edge (`readTaken`, `second`). The
  rule `Ready` (no branching `checked` record with a zero duration) is carried
  as an invariant on every pushed word (`ReadyImages`, `read_ready`); the taken
  word is owed only once `second` is false, and a branching word one edge after
  entry has not counted down (`branching_dispatch`). `trace_correct` gives trace
  equality with the atomic reference on every input history whose data words
  are ready, stated on traces (`trace_cons`) since the refinement is conditional
  on inputs. `test/Memory.lean`: the one-port machine matches the reference on
  the full scenario, 5,161 edges, 12 transactions, 24 taken branches; the four
  fixture programs have no unready word, the one-cycle-phase I²C write one and
  read three, the UART receiver two at any bit period; on the one-cycle-phase
  write the machine agrees under an address ACK and diverges on the address
  NACK's unready taken branch. 271 s interpreted. Library audit standard axioms
  only (6,281 theorems).
  `check-foundation --tag prefetch-single-01`: 159 modules, 11,990 declarations, 6,281 theorems, 29 suites, untrusted axiom rejected, 1,286 s.
- **Disposition:** the [memory abstraction](../memory-abstraction.md) owns the
  rule and the boundary. A one-port structural backend (one read tree instead of
  two) is a fit question; the receiver's zero-duration branching records are a
  compiler question.

## 2026-09-18: fetch organizations as a parameter; the one-port backend

- **Scope:** Lean theory and instances, one new structural backend with emission,
  the structural report, the independent RTL regression and generic mapping. No
  physical run.
- **Result:** `Storage/FetchPolicy.lean`: a `Policy p σ` (registers, `p` read
  ports, fed from registers only) and `Correct` (invariant, rule, `covers`,
  `preserved`, `initial`), from which `step_eq`, `machine_next`,
  `cache_valid_next`, `ruleRefinement` and `trace_correct` are proved once;
  `Hardware/TimedRule.lean` is refinement under a rule on inputs, with trace and
  pair-trace equality and composition below an unconditional refinement.
  `Storage/Dispatch.lean` collects the scheduler-decision facts and expressions,
  `Storage/ImageRule.lean` a rule on program words carried by the loader.
  Instances: `Decoupled` (three ports — its start word is a third read tree;
  obligations about 40 lines, the hand-written proof was about 190; the flat
  machine is identified with the generic one by `next_toPolicy`, and the emitted
  backend is byte-identical to `prefetch-03`), `TwoPort` (63 lines, start word on
  port 0 on commit edges, `covers` reused), `SinglePort` (one port, `Ready`).
  `test/Memory.lean`: all four machines match the reference on 5,161 edges, 12
  transactions, 24 taken branches; readiness and divergence checks as before;
  363 s (the generic step shares its feed, and the driver forces the fetched
  words each edge — as first written the interpreter re-derived the feed inside
  the words' closures and did not finish).
  `Storage/OnePortBackend.lean`: 611 fields, 6,426 bits, wires for the fed
  successor, the port address and the port word; `netlist_next`,
  `netlist_output`, `reference_next`, `completeRefinement` (a rule refinement),
  `trace_correct`; `OnePortEmit.lean` with `sampled_trace_correct`
  (`PinSampler.delayed_data`). `build/structure/oneport-01`: fetched words 65
  gate levels (decoupled 63, composed 101), port address 35, core state 60.
  `check-prefetch --variant oneport --tag oneport-03`: RTL/gate equivalence
  6,508 and 6,506 points with three-step induction (`oneport-01`: two steps
  leave 107 points unproven; the untaken-word register can skip a load for one
  edge, never two in a row); oracle in ready mode 29,898 edges on both
  emissions (`oneport-02` failed in the generator: with the UART receiver
  exercise merely skipped its live-replacement check found no captured samples,
  so a register read now stands in); unshifted sampled trace rejected; the inner
  RTL on the unrestricted vectors rejected, as the rule predicts. Mapped typical
  566,746 µm² inner and 576,805 µm² sampled (sampled candidate 547,995,
  decoupled 654,086), ABC delay 5,272 ps sampled (6,803; 5,815), slow 8,343 ps
  (9,945; 9,269). 343 s. Identity manifest
  `physical/experiments/oneport-results.json`.
  `check-foundation --tag fetch-policy-01`: 166 modules, 12,365 declarations, 6,456 theorems, 29 suites, untrusted axiom rejected, 1,409 s.
- **Disposition:** the [memory abstraction](../memory-abstraction.md) owns the
  theory, the instances, the backend and the boundary. The one-port backend
  passes the mapped gate; one routed comparison under the clock-gating overlay
  is the next physical discriminator and is not allocated. A policy-parametric
  backend is the next Lean step; `TwoPort`'s backend would follow from it.

## 2026-09-18: policy-parametric backend, two-port backend, rules enforced and proved

- **Scope:** Lean factoring of the backends, one new backend with emission, the
  structural report, RTL regressions and generic mapping; a correction to the
  gate-equivalence harness; the program rule as a filter and as compiler
  theorems. One routed run of the one-port backend (below).
- **Result:** `Storage/PolicyBackend.lean`: `core`, the general backend with the
  successor as a wire input, proved against the functional step (`core_step`,
  `core_observe`); `Realization` and `Realization.twoWires`; from a realization
  and `Correct`, `netlist_next`, `netlist_output`, `reference_next`, the rule
  refinement of the reference with the capacity contract and the trace
  theorems, once; `PolicyEmit.lean`: emission and `sampled_trace_correct` once
  (`PinSampler.delayed_rule`). `PrefetchBackend` 379 → 135 lines,
  `OnePortBackend` 473 → 226, `Decoupled`'s flat machine and bridge removed;
  both re-based backends emit byte-identical MLIR to `prefetch-03` and
  `oneport-03`, alone and sampled, with unchanged level reports
  (`build/structure/policy-01`). `TwoPortBackend.lean` (148 lines, compiled at
  the first attempt): port 0's word is a shared wire; fetched words 63 levels,
  start word 65 (`build/structure/policy-02`).
  `check-prefetch --variant twoport`: `twoport-01` left 148 points unproven at
  two and at three steps — synthesis had narrowed the three word registers to
  63 bits, name matching dropped them, and the start word loads on commits only.
  The harness now re-exposes narrowed registers at full width in a copy used
  for the comparison. `twoport-02`: 6,501 and 6,511 points with two-step
  induction, unrestricted oracle 35,824 edges on both emissions, unshifted
  sampled trace rejected; mapped typical 618,244 µm² sampled (+12.8% over the
  sampled candidate), ABC delay 5,027 ps (−26.1%), slow 8,150 ps (−18.1%).
  `prefetch-05`: the decoupled RTL, identical to `prefetch-03`, now compared at
  6,501 and 6,505 points (the two fetched registers had been left out of the
  6,373; they reload every edge, so that result stood). `prefetch-04` was
  invalidated by my editing sources during the run. The explanation given on
  2026-09-18 for the one-port backend's three-step induction ("the untaken-word
  register can skip a load for one edge") is withdrawn: every register is
  matched there and the cause was not isolated.
  `Storage/Admission.lean`: `admit`, `admit_rule`, `admit_of_rule`, `discharge`
  (`Timed.RuleRefinement.precompose`); the one-port rule now reads
  `command = 2 → Ready data`; `SinglePort.admitted`, `Backend.OnePort.admitted`;
  the capacity check is `admit (Small.capacity cursor)` by `rfl`.
  `Storage/Readiness.lean`: `ready_encode`, `upload_ready`, `i2c_write`,
  `i2c_read` (every request, `phaseMinusOne ≠ 0`), `embedded` (UART and SPI
  transmission), `uart_receiver` (never). Library audit standard axioms only
  (6,480 theorems). `check-foundation --tag policy-backend-01`: 172 modules, 12,450 declarations, 6,480 theorems, 29 suites, untrusted axiom rejected, 1,483 s.
  `oneport-sampled-01` (`combined.json`, 150-minute cap, no stop after
  `STAPostPNR`): the flow ran to its end in about 100 minutes, 51 detailed-routing
  passes to zero violations, Magic DRC 0, LVS 0, antenna 0; exit 2 for the one
  deferred error, slow-corner setup. Slow setup −0.187 ns (9 endpoints, TNS
  −1.168 ns), typical +5.730, fast +8.602; hold +0.361 / +0.168 / +0.054;
  624,825 µm² of functional cells, 69.2% utilization, 1,663,828 µm of wire,
  6,116 repair buffers (73,235 µm²); 10 slew and 20 fanout violations.
  Per-family query `oneport-sampled-01-families`: registers −0.053 ns (3 paths;
  `combined-03` −2.054, `pin-sampled-02` +0.090), loader command +0.473 (−2.251,
  +0.175), loader data −0.187 (+0.116, +1.996), protocol +14.506, reset +0.228.
  The worst register path ends in `r_fetched_taken[52]` and `r_start_word[52]`
  through the port's read — the level model's deepest endpoint; all nine
  violating endpoints launch from `data[35]` through the capacity check on the
  command, the commit select and the port's address. Implemented-netlist
  regression on the ready-mode vectors: 29,898 edges, 4,903,194 comparisons,
  mutant rejected. Manifest `physical/experiments/oneport-physical-results.json`.
- **Disposition:** the [memory abstraction](../memory-abstraction.md) owns the
  backends, the rule, the routed comparison and the boundary. The one-port
  organization is the first variant to fit with clock gating and come within
  0.2 ns of the slow corner; the command-split form inside `Backend.Policy.core`
  is the next Lean step, and a routed repeat and a two-port run are separate
  allocations.

## 2026-09-18: command split in the generic backend; the data port as a theorem; two routed runs

- **Scope:** one Lean change in the generic policy backend with its proofs, a
  structural theorem file, an extension of the structure check, re-validation
  of the three emitted backends, and two routed runs approved as such: a repeat
  of the one-port backend and a first run of the two-port backend, both under
  the contract of `oneport-sampled-01` (`combined.json`, 150-minute cap, whole
  flow), stated before the runs.
- **Result:** `Backend.Policy` lifts with `BankSelect.lift` (`feedW`,
  `BankSelect.circuit` for the loader's registers and outputs, `liftC`); new
  lemmas `BankSelect.lift_correct`, `circuit_next_eq`, `circuit_output_eq`; no
  policy file changed. Level report `build/structure/split-01`, then
  `check-structure --tag split-02` with the new policy-backend section: data
  port into fetched words 71 → no path, into core state 61 → no path, loader
  control 42 → 41; cursor into fetched words 65 → 50; registers into the
  dispatch decision 33 → 20, cached word 38 → 25, fetched words 65 → 64
  (two-port 64, decoupled 62). The earlier report (`policy-02`) already ranked
  the data port deepest; I had not read that row before `oneport-sampled-01`.
  `Storage/DataPort.lean`: `dataPort`, leaf facts by `rfl`
  (`base_data_free`, `commit_lift_data_free`, `branch_lift_data_free`,
  `chosen_data_free`, and `plain_commit_sees_data` by `decide`), generic
  `sched_data_free`, `sched0_data_free`, `readAt_data_free`, `core_data_free`,
  `core_output_data_free`, `DataFree`, `DataFree.next`, `DataFree.output`,
  `DataFree.step_independent`, instances `Prefetch.dataFree`,
  `TwoPort.dataFree`, `OnePort.dataFree`. A section variable mentioning `next`
  resolved to `DataFree.next` once that existed and elaborated to `sorry`
  without an error; written `Policy.next`.
  `check-prefetch`: `oneport-04` (6,508 and 6,506 points, three-step induction,
  29,898 ready-mode edges on both emissions, both rejections), `prefetch-06`
  (6,501 and 6,511, 35,824 edges), `twoport-03` stopped on the mapped
  flip-flop assertion of the sampled emission with everything before it passed
  — 6,425 where 6,419 was expected: bits 3–8 of the cached word, deleted as
  unread in `twoport-02`, are kept — and `twoport-04` passed with the count
  recorded (6,507 and 6,505 points, 35,824 edges). Mapped typical, sampled:
  one port 557,736 µm² (+1.8% over the sampled candidate; was 576,805), ABC
  5,167 ps; two ports 628,939 µm² (+14.8%; was 618,244), 5,431 ps; decoupled
  637,827 µm² (+16.4%; was 654,086), 5,601 ps. Manifests
  `physical/experiments/{oneport,twoport,prefetch}-split-results.json`.
  `check-foundation --tag command-split-policy-01`: 173 modules, 12,519
  declarations, 6,528 theorems, 29 suites, untrusted axiom rejected, 1,494 s.
  `oneport-split-01`: exit 0, the whole flow in 55 minutes; 17 detailed-routing
  passes to zero violations (13, then 4 after antenna repair); slow setup
  +0.602 ns with no violation, typical +6.325, fast +8.815; hold +0.379 /
  +0.152 / +0.060; 625,727 µm² of functional cells, 69.3% utilization,
  1,617,478 µm of wire, 6,026 repair buffers (70,119 µm²); 5 slew and 15 fanout
  violations; Magic DRC 0, LVS 0, antenna 0. Families
  (`oneport-split-01-families`): registers +1.100 (`cached_word[39]` →
  `start_word[1]`), loader command +0.602 (`command[0]` → `start_word[1]`),
  loader data +4.383 (`data[2]` → `loader_rejected`), protocol +14.459, reset
  +0.874. Implemented-netlist regression on the ready-mode vectors: 29,898
  edges, 4,903,194 comparisons, mutant rejected. Manifest
  `physical/experiments/oneport-split-physical-results.json`.
  `twoport-split-01`: exit 124 at the 150-minute limit. Utilization 75.2%
  (678,368 µm²) entering global routing, which ran from 17:45:52 to 19:49:17
  container time — 71 `GRT-0273` rounds, each disabling the non-default rule of
  one clock net and re-running 50 overflow iterations — and completed with
  3,386,282 µm of estimated wire and 66 antenna violations (one port at the same
  step: 2,156,400 µm); `RepairDesignPostGRT` re-entered the loop (8 more rounds)
  until the limit. Last completed step `40-openroad-checkantennas`; no detailed
  routing, no extracted timing; mid-flow estimates are omitted from the manifest
  `physical/experiments/twoport-split-physical-results.json`.
- **Disposition:** the [memory abstraction](../memory-abstraction.md) owns the
  change, the theorem and both routed results.
  The one-port organization with the command split is the first design here
  to meet setup at all corners with clock gating, in one run; the two-port
  organization does not route on the test rectangle under this overlay. Both
  conclusions are about the test boundary — a core rectangle with stand-in
  pins — and the [whole chip](../engine/whole-chip.md) is now a Lean object whose
  routed run has not been made.

## 2026-09-18: the whole chip in Lean — feeders, serial loader, upload theorem

- **Scope:** Lean only, plus emission and one mapped screen. No simulation of the
  emitted chip and no physical run. Direction set by the user the same day: the
  Lean specification should cover the whole stack, the serial loader first.
- **Result:** `Hardware/Feeder.lean`: `Feeder` (expressions for the inner inputs
  and for the layer's own registers), `wrap`, `wrap_step`, `wrap_observe`,
  `wrap_pairTrace` (any netlist behind any feeder takes the edges of the fed
  history), `Model` with `pairTrace_eq`, `history_fst`, `history_append`,
  timing laws `wrap_arrivalNext`, `wrap_shields`, the generic two-register
  `sampler` with `samplerModel` and `sampler_consumed`, `Netlist.mapOutputs`.
  A component built from unapplied `n.step` left goals in an eta form that
  `rw` could not match; `Netlist.component` uses explicit lambdas.
  `Hardware/Serial/Receiver.lean`: five registers (76 bits), `receiver` as a
  feeder, `model` (circuit = functions, through three Bool/BitVec bridge
  lemmas and `rfl`; `simp` with a Bool hypothesis on a BitVec literal did not
  rewrite, as before), `no_path_from_host`. `Serial/Frame.lean`: `IsBit` (clock
  low at least once, high at least twice, data at the first high sample),
  `run_bit`, the shift invariant `Partial` on `c ++ d`, `frame_delivers`,
  `Session`, `session_delivers`. `Loader/Delivery.lean`: `Quiet`, `Carries`,
  `Delivers`. `Hardware/Chip.lean`: `pinMap`, `outputs`, `netlist`, `trace_eq`,
  `consumed_delayed`, `session_delivers`, `advance`, `history_append`,
  `pins_shielded`. `Storage/ChipBackend.lean`: `Policy.chip_trace`,
  `OnePort.chip_trace`, `TwoPort.chip_trace`, `chipText` (module
  `tt_um_pinwheel` with the template's ports). `Loader/Upload.lean`: `admitted`,
  `stepWith`, `runWith`, `imageOf`, `idle_next`, `quiet_next`, `begin_next`,
  `pushed_next`, `complete_commits`, `Staging`, `Loaded`, `staged_run`,
  `upload_loads`, `Delivers.pushes`. `Loader/Program.lean`: `Holds`,
  `scheduler_holds`, `core_next_holds` (through `Reactive.step_refines`),
  `Running`, `runs_program`, `runs_program_with`, `Loaded.running`.
  `Storage/ProgramUpload.lean`: `upload_holds`, `upload_good`, `Fits`,
  `upload_fits`, `program_loads`. `Storage/ChipUpload.lean`:
  `chip_program_loads`, `chip_upload_ready`, `TwoPort.chip_runs_upload`,
  `OnePort.chip_runs_upload`. Inside `theorem DataFree.next`-style names a
  section variable mentioning `next` had elaborated to `sorry` earlier in the
  day; the same trap was avoided here by qualifying names.
  `test/SerialUpload.lean` (suite 30): the compiled I²C write's upload and a
  start as 325 frames, 70,855 Tiny Tapeout pin samples through `Chip.consumed`,
  delivered in order; longer and uneven phases; garbage on the data pin except
  at the first high sample; command 7 as reset; inverted and
  least-significant-first drivers, a frame cut by the select line and a missing
  two-sample tail rejected; 322 words, at most 32 distinct records, all ready
  and within capacity; the UART receiver's stream not ready. Under one second.
  `chip_emit` → `build/chip/chip-01`; CIRCT export; mapped typical: one-port
  chip 562,152 µm², ABC 5,364 ps (test-boundary core behind the sampler
  557,736); two-port chip 614,555 µm², 5,391 ps (628,939).
  `check-foundation --tag whole-chip-01`: 183 modules, 13,322 declarations, 6,873 theorems, 30 suites, untrusted axiom rejected, 1,423 s.
- **Disposition:** [the whole chip](../engine/whole-chip.md) owns the stack, the
  theorems and the boundary. The proved object is now the chip's netlist, from
  a host's serial session to the instruction-level engine running the uploaded
  program. The emitted RTL of that netlist has no independent check yet and no
  physical run; both are separate steps, the second needing an allocation and
  an outline decision.

## 2026-09-18: the competition's outline is now 6×4

- **Source:** the [announcement](https://blog.janestreet.com/protocol-emulator-asic-competition/),
  reread 2026-09-18 after a note from the project owner. It now says: set the
  tile size to `6x4`; the current maximum is 6×4 tiles (24 tiles, about 0.7 mm²
  of nominal tile area, about 1,000 logic cells per tile as a budget); 8×4
  (about 30% more) is being worked on, with updates by page and email. Deadline
  (2027-01-18) and shuttle target (March 2027) unchanged. First read
  (2026-09-12): `8x4`.
- **Pinned files:** support commit `da63c99` has the 6×4 tile entry
  (1,289.28 × 710.64 µm) and the official template
  `tech/ihp-sg13cmos5l/def/tt_block_6x4_pgvdd.def`
  (SHA-256 `b46d9a0ee8352160e48dbc8312f092f985629061df736c7f46d58686535a76f4`):
  186 rows × 2,674 sites = 902,417 µm² of core, the `design__instance__area` of
  the routed runs; 43 pins, all Metal4, top edge, x from 29.76 to 191.04 µm.
  No 8×4 entry, consistent with the announcement. The flow already has an
  `Odb.ApplyDEFTemplate` step (step 27 of the routed runs), unused so far.
- **Disposition:** no run. The "diagnostic" rectangle was the official die area;
  the outline decision recorded as blocking a whole-chip run is resolved. On
  this outline the one-port organization is the candidate (69.3%, met) and the
  two-port one is not (75.2%, did not route), so a UART receiver inside the
  one-port rule is required, not optional. [Competition brief](../competition.md#the-outline-and-the-pinned-files),
  [status](status.md#the-official-outline-2026-09-18) and
  [the whole chip](../engine/whole-chip.md#the-outline) updated;
  `tools/physical-toolchain.json` records the allocation. Older studies keep
  their wording about an 8×4 outline as written at the time.

## 2026-09-19: local branch review and submission plan

- **Scope:** review of `claude/physical-fit`, starting at `4d5de85`, followed by
  bounded script, test and documentation fixes. No Lean definitions or proofs
  changed; no new mapping, physical run or default-backend promotion.
- **Fixes:** physical preparation now requires the manifest's HEAD, index and
  working-tree bytes to agree. Netlist receipts use portable logical paths;
  clock-gate mutation checks bind retained inputs and require the unmodified
  baseline to pass. Sampled/prefetch checks bind their full oracle dependency
  chain and terminate timed-out process groups with retained diagnostics.
  DEF parsing follows logical route segments and excludes patch rectangles
  from via counts; the [dated correction](../physical-correlation-study.md#parser-correction-2026-09-19)
  preserves the original physical results and records the changed resistance
  fits on two retained input pairs. The original calibration pair is absent.
- **Validation:** the clean-source foundation gate passed all 30 suites and
  audited 183 modules, 13,322 declarations and 6,873 theorems with standard axioms
  only; the injected untrusted axiom was rejected. It took 1,521.681 s, and all
  250 recorded inputs match the working tree. Receipt:
  `build/pr-review-20260919/source/build/validation/pr-review-20260919/report.json`
  (SHA-256 `707af9088f0e50abb3628a539c5904740fcaa4858a9c7c3113f85139b997fd0a`).
  All 56 Python tests passed, with all script/test source hashes unchanged
  during the run. Fresh emission of one-/two-/three-port cores, their
  sampled variants and both chip variants matched all eight retained MLIR/RTL
  pairs. This is emission identity, not new simulation, equivalence or physical
  evidence. Local receipts are under `build/pr-review-20260919/`.
- **Disposition:** the [submission plan](../submission-plan.md) names the next
  implementation gates: a ready UART receiver and emitted admission rule, host
  result transfer, independent chip RTL validation and the actual chip physical
  boundary. Current status no longer treats a two-port timeout as an absolute
  utilization cutoff. Host documentation now states the three-edge idle
  preparation and separates upload commitment from a later start.

## 2026-09-19: shared contracts, early SRAM study and host result checks

- **Scope:** local `codex/chip-contract-consolidation` work from `a256e7847dc3`.
  Moved generic upload encoding out of readiness, compiler certificates out of
  storage, and common timed/netlist operations out of the feeder. Added generic
  input admission preserving commit/start decoding, an output observer and the
  35-bit retained host result interface. Historical one-/two-port chips and
  sampled/inner core MLIR reproduce byte for byte. Validation runners now share
  command capture, timeout cleanup and reasoned rejection checks.
- **Early SRAM discriminator:** public pinned macro models pass 1,979 storage
  edges and 1,000 branch fetches across four consecutive-branch runs. Expanded
  uploads retain all 322 push edges, two atomic banks and immediate commit/start
  via a Q bypass followed by retained start data. Collapsing the read responses
  is rejected. `build/storage/feasibility/schedule-05/report.json`, SHA-256
  `b73f06937bfab326a61fd985d72db552281f22d72d76213eacdce01b435f74bc`,
  binds all 13 selected views and the scenario formulas. Two-read whole-chip
  scenarios are 445,327–503,560 µm² hybrid and 509,854–585,117 µm² direct;
  these include banks, buffering/control and repair allowance, but exclude
  routing space/halos and physical integration. They are not measured bounds.
- **Independent result-chip gates:** two ports pass 365,966 edges / 1,672 serial
  frames in both RTL and generic gates, with all 6,580 equivalence points proved.
  Admitted one-port passes 294,514 edges / 1,346 frames and 6,575 points.
  Each positive baseline passes before a real result-bit corruption is rejected.
  Receipts `build/chip/twoport-result-check-02/report.json` (464.373 s, SHA-256
  `dc8d79e8a79a0e13bdad967f781316b7ea5d3efbcbf640ace4fd6cccdbc7b604`)
  and `build/chip/oneport-result-check-01/report.json` (356.297 s, SHA-256
  `6fc401bef8fa70f380ff6c974945d7f15f460f8917a00635aa8f89092fbc471a`)
  bind exact sources/artifacts and the external-pin oracle. Both cover retained
  captures, upload failures, replacement, halt-only completion and a stretched
  I²C read. Two ports also cover UART receive with good/bad stop bits.
- **Cleanup regression:** `build/sampled/contracts-cleanup-01/report.json`
  (175.576 s, SHA-256
  `4956b493569033ebb15fc73cceace9efbcde489f01f9e31d8dafa48f159abd6d`)
  confirms historical inner RTL identity, 6,319 reference-pipeline and 6,313
  generic-gate equivalence points, 35,824 atomic edges / 22,434,312 storage
  observations, both mapped corners and rejected wrong sampling depths.
  Python checks pass 76 tests with two platform-specific skips (7.280 s).
- **Foundation:** `build/validation/contracts-cleanup-02/report.json` passes all
  31 suites and audits 191 modules, 13,755 declarations and 7,084 theorems with
  standard axioms only; the injected untrusted axiom is rejected. All 259
  recorded inputs match the working tree. Elapsed 1,437.784 s; receipt SHA-256
  `b50d37b321f6fd8d9d4217bd1b92caa7bd13c618b33a95ed0f5ef5ddf2213321`.
- **Disposition:** the [SRAM study](../storage-primitives.md#bounded-sram-scheduling-study-2026-09-19)
  supports keeping unrestricted two-read execution available. The next storage
  experiment is the complete direct wrapper, compared with the hybrid's lower
  area estimate. Physical SRAM views are not integrated; no SRAM backend or
  final storage choice follows. UART timing is unchanged. The [whole-chip
  record](../engine/whole-chip.md#independent-result-chip-checks-2026-09-19) owns the
  result-interface validation; actual RTL read-back and the official-template
  physical experiment remain separate gates. No new physical run or default
  promotion occurred.

## 2026-09-19: complete SRAM chip comparison

- **Implementation:** `test/SramChipEmit.lean` emits direct and hybrid controllers
  from the shared Lean loader/scheduler/transport/result expressions; only
  storage and synchronous fetch binding change. A small Verilog binding connects
  two real macro instances. Both variants retain two atomic banks, independent
  successor reads, broadcast writes, commit/start bypass and retained start data.
  Direct uses 32×55 scratch; hybrid retains two 256×5 combinational maps. This is
  an experimental emitter, outside the promoted library and without an SRAM
  refinement theorem. The existing library is unchanged; its fresh audit still
  reports 13,755 declarations / 7,084 theorems with standard axioms only. The
  prior foundation receipt differs only in the newly added Lake executable target.
- **Complete functional/mapping comparison:**
  `build/storage/sram-chip/comparison-01/report.json`, 515.390 s, SHA-256
  `927551be871e7bb9587129809ff0ce1e5173954567a6a1e24aa3347b529628e6`,
  binds 212 source inputs, tool/view identities and regenerated vectors. Each
  of direct SRAM, hybrid SRAM and matched two-port FF passes 365,966 external-pin
  edges / 1,672 serial frames at RTL and both mapped CMOS5L corners. Each SRAM
  also passes 11,840 core edges, every address in both banks, 1,000 consecutive
  branches, immediate commit/start and aborted-upload restart. Collapsed-read
  and disabled-broadcast mutants compile and fail behaviorally for both SRAMs.
- **Cost:** typical complete mapped totals are 479,596 µm² direct, 393,558 hybrid
  and 622,897 FF; mapped FF counts are 2,095 / 2,895 / 6,544 respectively. Macro
  areas are 300,205 / 100,978 / 0 µm². No placement, clock tree or repair area is
  included. The study separately applies the earlier 10–20% standard-cell repair
  allowance, retaining its estimate boundary. Hybrid is 36.8% smaller than the
  matched FF chip and 17.9% smaller than direct.
- **Compatibility:** all 13 selected macro views match Git blobs in the physical
  PDK revision `2bbec755dc67ca3db0261c3d6163e15735d66710`; both mapping Liberty
  files match the installed PDK. LEF routing uses Metal1–Metal4. GDS/CDL/fast
  views exist in the pinned inventory but are not installed. LEF power pins use
  `!` suffixes absent from Liberty groups; explicit power integration remains.
- **Pre-layout timing:** `build/storage/sram-timing/comparison-01/report.json`,
  3.528 s, SHA-256
  `a67570c75a64687d059a3161bedfea8aad1f2a43372d6e0ba86a481c9e6e88a6`,
  binds the mapped comparison and verified OpenSTA container snapshots. Each
  invocation is capped at two CPUs, 2 GB and 120 s, with no network or writable
  host mounts. At 20 ns, ideal clocks/no wires, macro-aware slow setup/hold is
  +9.97/−0.53 ns direct, +10.26/−0.86 ns hybrid, +10.38/+0.02 ns FF. Fanout
  violations are 800 / 1,300 / 3,048; no slew, capacitance, minimum-period or
  pulse-width violations were reported in these two corners. This is a timing
  screen, not closure; fast-corner and extracted checks remain open.
- **Decision:** select hybrid SRAM with two reads for the complete adapter proof
  and macro-aware physical experiment. Retain the current capacity/UART contract;
  no duration restriction is needed by the tested schedule. Fix hold/fanout in
  the physical flow and validate power, placement and the official chip template.
  The [storage study](../storage-primitives.md#complete-chip-comparison-2026-09-19)
  owns the detailed comparison. No place/route run, backend promotion, commit,
  push, PR or submission was made by this follow-up.

## 2026-09-19: integrated chip workflow and early physical diagnosis

- **Decision/authority:** proceed with the approved shared-contract, focused
  SRAM-proof, host-demonstration and bounded physical work. Licensing remains
  pending by explicit user decision. The September 19 reread of the
  [announcement](https://blog.janestreet.com/protocol-emulator-asic-competition/)
  retains 6×4 and the emphasis on programmability, verification and early routing.
  Local implementation and experiments do not promote a backend or publish a
  submission.
- **Response model:** `Storage.Sram` proves initialization, invariant
  preservation and trace refinement for held synchronous responses and delayed
  start-word ownership. The experimental emitter shares its bypass expression;
  direct/hybrid chip/core MLIR remains byte-identical to `comparison-01`.
  Physical arrays, bank/address wiring and emitted-adapter composition remain
  proof obligations. There are no unfinished proof placeholders.
- **Host workflow:** the pin-only interactive client runs nine cases on one
  unchanged chip: UART TX, SPI mode 0, stretched I²C read, two UART RX frames,
  high/low/timeout custom triggers and malformed-upload recovery. Hybrid and FF
  reference each pass 855,975 edges / 2,925 serial frames. A full upload costs
  94,629 edges, versus the TX example's 40 execution edges. This motivates a
  resident-program variable-payload workload before data/FIFO/ISA expansion.
  `build/host/integrated-hybrid-03/report.json` (88.637 s) has SHA-256
  `a6e599a543ef979e0526cde95959d49eda8a726ec0ec3085ad85f23523e825bf`;
  `build/host/integrated-reference-02/report.json` (98.229 s),
  `844acafcd1931fe1edf0fe073d2a855d55cf1b35674b1b6c2c9b961a4db84304`.
  Reusing an exported trigger image through `run` passes 94,991 edges / 325
  frames; `build/host/integrated-custom-02/report.json` (16.827 s),
  `b015255c3444f2a217a0e9c743e2e299a59fd5a13d09a85e7d0319d7f69b0ad3`.
- **Whole-chip regression:** the independent oracle now includes UART TX/SPI
  pin peers. Two ports pass 508,252 edges / 2,324 frames and 6,580 equivalence
  points; admitted one-port passes 436,800 / 1,998 and 6,575 points. Each passes
  RTL/generic gates and rejects the syntactically valid result corruption.
  `build/chip/integrated-twoport-01/report.json` (571.670 s),
  `48a828227ba686655c01c4bf74c33e4df4879089c8b2003f53946093b5f54329`;
  `build/chip/integrated-oneport-01/report.json` (465.534 s),
  `47534896430e29e04cc617db061af240cba880abc19dfb77aadb85b94964e986`.
- **SRAM refresh:** all three chips pass the expanded 508,252-edge trace at RTL
  and typical/slow mapped corners. Both SRAMs pass 11,840 core edges, 1,000
  seeded consecutive branches, all addresses/banks and both mutation controls.
  Mapped area and pre-layout slack are unchanged. `build/storage/sram-chip/integration-02/report.json`
  (775.901 s), `535b20efe796f762f218d37a72e82db3fef936e1e4ffaf0c66e8f925551da097`;
  `build/storage/sram-timing/integration-02/report.json` (3.701 s),
  `d36d557ddebb7db5925d4cd7e0accc6dfca047b12c276c49ccd265c0bc205d17`.
  Hybrid slow pre-layout setup/hold remains +10.26/−0.86 ns with 1,300 fanout
  violations; this screen is not extracted timing. The fresh hybrid RTL matches
  each frozen physical attempt exactly. Preparation from this fresh receipt
  succeeds at `build/physical/hybrid-validated-01/inputs.json`.
- **Physical integration:** chip-specific SDC/config, the official 43-pin DEF,
  all pinned macro views and read-only PDK snapshots now exist. Initial lint
  required extracting the vendor black-box interface. Subsequent attempts find
  disconnected array supply at 50 µm power pitch, clear the connectivity report
  at 16 µm, and reduce global overflow from 5,021 to 1,668 by moving both macros
  near the bottom. Attempt 04 costs 483,185 µm² after repair, above the earlier
  allowance. Attempt 05 continues its verified checkpoint for at most 2,700 s,
  with four CPUs / 6 GiB and no network, allowing global congestion solely to
  diagnose detailed routing. The [physical study](../chip-physical-study.md)
  owns its final outcome and the grid/corner/layout qualification limits.
- **Portable checks:** 90 Python tests pass, with two Linux-specific skips.
  New checks cover host pre-I/O rejection, nondestructive readback, bounded
  polling, complete macro-view snapshots and rejection of stale sources,
  changed RTL/GDS and mismatched downloads. The first parallel fresh runs
  exposed missing `Pinwheel` build dependencies in the host/comparison runners;
  both now build the library explicitly. Failed tags retain their logs and
  have no success receipts. Final review also reproduces and fixes a pipe
  read-ahead timeout when vendor diagnostics and a reply arrive together; the
  current host receipts above follow that fix. The new regression sends both
  lines in one OS write.
- **Foundation:** `build/validation/integrated-chip-01/report.json` passes all
  31 suites in 1,474.135 s and audits 192 modules, 13,824 declarations and 7,112
  theorems with standard axioms only; the injected unapproved axiom is rejected.
  Receipt SHA-256: `a0a630b089c9d0cb91ec209569ca6144ccf87f45bee099bcfceda35d1b296f12`.
- **Physical netlist behavior:** `check-chip-physical.py` validates a completed
  report's exact netlist view against the fresh comparison's pin vectors and
  pinned cell/macro models, then requires a compiled public-output corruption to
  fail. Attempt 04's step-37 clock/hold-repaired netlist passes 508,252 edges.
  `build/physical/chip-check/repaired-hybrid-01/report.json` (103.838 s), SHA-256
  `b6807e6ef92f3c64d9311c4e0bdf1178de108da6fe793d1536b1adae9c959ad0`.
  This is zero-delay evidence for that exported netlist, not the later routing
  database, timing simulation or sequential equivalence.
- **Bounded physical outcome:** `hybrid-chip-05` exits 124 at 2,700 seconds;
  `docker stop` succeeds and the receipt confirms the container stopped. The
  last complete step-log iteration (58) reports 168 detailed-route violations;
  stdout records iteration 60 underway. No detailed-route state completes, so
  the final retained state is `05-openroad-stamidpnr-3`, not a routed result.
  It reports 483,806 µm², estimated typical setup/hold +7.57528/+0.0419088 ns,
  24 slew, 222 fanout and 14 capacitance violations. Older fast/slow metrics are
  inherited. No extracted multi-corner timing or final DRC/LVS result exists.
  `build/physical/hybrid-chip-05-report.json`, SHA-256
  `6af820485c0dde78a373829f367cdca323bda7b61afe77327c8290de35148d4f`.
  The [tracked manifest](../../physical/experiments/hybrid-chip-physical-results.json)
  retains all four substantive attempts and links the functional receipts.
  Per-iteration detailed-route geometry was not retained; enable its capture
  before the next bounded attempt so remaining locations can guide changes.
  Keep SRAM experimental, preserve UART/capacity semantics, and finish the
  physical-array/address proof alongside targeted physical diagnosis. Licensing,
  backend promotion and publication remain pending.

## 2026-09-19 — Routing diagnosis and replicated SRAM contract

- **Geometry capture:** `hybrid-chip-06` resumes the verified pre-detailed-route
  checkpoint, enabling snapshots and per-iteration DRC reports without changing
  RTL, placement, pins or timing. It is stopped deliberately after diagnosis;
  exit 137 is not a timeout or completion. The last completed log iteration, 38,
  agrees with the retained report's 196 markers: 141 shorts, 55 spacing failures,
  all Metal4 and fully inside SRAM footprints; 136 involve power/ground.
  `build/physical/hybrid-chip-06-report.json`, SHA-256
  `e9ae69a0781adc6f85baa661947196825207216966cc07ed2749502ef627e161`.
  `build/physical/diagnosis/baseline-final/report.json`, SHA-256
  `e3947f59477c1ec977e3d3ee7df8381b08411516ead7d16545d27ea9045237b8`.
- **Controlled negative result:** a separate checkpoint adds two Metal4 routing
  obstructions over SRAMs, exempting power nets, with unchanged placement and
  connectivity. `hybrid-chip-07` has 240 markers at iteration 38: 236 shorts,
  four spacing failures, all Metal4 and intersecting SRAM footprints. Global
  guides are byte-identical: 470 Metal4 rectangles overlap SRAMs on 228 nets.
  The keepouts are not adopted. Both containers are confirmed absent in
  `build/physical/routing-termination.json`. The comparison is of intermediate
  routing markers, not foundry DRC or closure; the prior 168-marker result used
  a longer run and a different iteration.
  `build/physical/hybrid-chip-07-report.json`, SHA-256
  `ecc8d6b95a7151624328dca7aa49fc7b37161fbec5a1485ced42168ae75b18ac`.
  `build/physical/diagnosis/keepouts-final/report.json`, SHA-256
  `56d29676bc113a1810f1cbb6a7463518bd96bbb97f99321ce269f7d5ea0659b6`.
- **Reusable proof:** `Memory.Sram` proves partial-model preservation for
  replicated single-port arrays, arbitrary initial contents and finite request
  histories, plus broadcast initialization, held Q, defined reads and bank
  isolation. Actual controller request/address correspondence and complete
  emitted-adapter refinement remain open. Fresh library build, whole-library
  axiom audit and `test/Memory.lean` pass: 193 modules, 13,878 declarations and
  7,132 theorems, including generated declarations, with standard axioms only.
  This is a targeted gate, not a rerun of the earlier full 31-suite foundation.
  `build/validation/sram-contract-01/report.json`, SHA-256
  `20360034af6f14736fb38c193863304fc3676f62467f32299b5db8eecb84433c`.
- **Fresh artifact checks:** direct/hybrid/FF chips pass 508,252 edges at RTL
  and both mapped corners; SRAM core stress and both mutations pass their
  expected outcomes. All four SRAM emissions are byte-identical to the previous
  comparison. `build/storage/sram-chip/routing-03/report.json` (753.825 s), SHA-256
  `c653cb41ffd62b527afb7041611a706eb3cb28a1c9605defa12f604eb5c3b39c`.
  The baseline's inherited step-37 repaired netlist again passes 508,252 pin
  edges and rejects compiled output corruption. This exercises the reporter's
  first-resumed-step checkpoint fallback; it does not validate a later routed
  layout. `build/physical/chip-check/routing-baseline-02/report.json` (108.402 s),
  SHA-256 `408b38e810dfc9523daaf0bde91c293753e0eb2d9ae78687d8e1e8b2604a5ffd`.
  Python: 97 tests run, 95 passed, two platform skips.
- **Decision:** investigate macro orientation/placement and regenerated global
  guides before another long detailed-route run or a storage change. Preserve
  capacity/UART semantics and leave licensing pending. The
  [physical study](../chip-physical-study.md#routing-diagnosis-2026-09-19) owns the
  annotated layout and interpretation; the
  [manifest](../../physical/experiments/hybrid-chip-physical-results.json)
  binds both runs, the keepout derivation, diagnoses and validation receipts.

## 2026-09-19 — Mirrored macro screen and emitted SRAM request bridge

- **Controlled screen:** a separate prepared configuration mirrors both SRAMs
  vertically, keeping the same macro boxes, RTL, views, clock, grid and package
  pins. The pinned LEF permits the orientation; OpenDB confirms `MX` and all 342
  signal shapes per macro on its north edge. `hybrid-chip-08` starts before
  placement/clock repair and stops successfully after global routing. Total
  overflow falls 1,668→1,255, Metal4 overflow 758→208 and Metal4 body-overlapping
  guide rectangles 470→129. Metal2 overflow rises 566→785 and estimated wire
  length grows 4.8%. This is a screening improvement, not routing closure.
  The base profile is unchanged. `physical_floorplan.py` freezes/verifies only
  existing instance placements; `report-routing-guides.py` verifies same-step
  database/context/guide identity and coordinate scale.
- **Bounded continuation:** `hybrid-chip-09` resumes the verified global checkpoint
  at `OpenROAD.CheckAntennas` with four CPUs, 6 GiB and a 2,700-second limit.
  Exit 124, confirmed stopped and independently absent. Last completed step:
  `04-openroad-stamidpnr-3`; detailed routing and extracted timing incomplete.
  The matched iteration-38 comparison is 196→174 markers (11.2% lower).
  Last completed logged iteration 59 has 126 markers: 90 shorts, 36 spacing,
  all Metal4 and fully inside SRAM footprints, 84 involving power/ground.
  Reports/snapshots through 61 exist, but completions 60/61 are not in the step
  log and are excluded from the final diagnosis. Matching geometry locates
  terminals of 70/76 implicated non-power nets in the 49.64 µm inter-macro gap,
  which contains 858 standard cells. This supports screening increased macro
  separation next; it does not prove root cause. After 231 antenna diodes, the
  last pre-route typical STA is setup +8.409 ns / hold −0.611 ns, with 16 hold,
  67 slew, 30 cap and 229 fanout violations; instance area 484,675 µm².
- **Proof integration:** controller expressions move from the test emitter to
  `Storage.SramController`. Thirteen explicit lemmas connect accepted hybrid
  write enables, physical address mux/truncation, selected-bank index lookup,
  commit reads, broadcast host data and active-bank preservation to the reusable
  array model. Complete upload coverage, response-definedness/ownership in every
  reachable state and full emitted-chip composition remain open. Direct SRAM's
  request/expansion proof remains separate. The four emitted MLIR files and the
  hybrid RTL are byte-identical to the earlier comparison and frozen experiment.
- **Validation:** fresh build and whole-library audit cover 194 modules, 14,073
  declarations and 7,212 theorems with standard axioms only. Targeted memory
  checks pass in 388.053 s. The first attempt's 300-second limit was too short;
  its process group was confirmed stopped before the 900-second retry.
  This is not a rerun of all 31 foundation suites. Python: 102 tests, 100 passed
  and two platform skips; the final empty-guide rejection additionally passes
  the two guide-parser tests. Full SRAM comparison `orientation-05` passes
  all three chips at RTL and both mapped corners in 745.679 s, with the 508,252
  pin-edge oracle, SRAM branch stress and both expected mutation rejections.
  An initial build attempt caught the new root import after declarations; moving
  it into the import block fixed it before the successful fresh comparison.
- **Implemented netlist:** `orientation-repaired-03` passes 508,252 edges and
  rejects compiled output corruption in 112.248 s. It validates the exact
  `hybrid-chip-08/37-openroad-resizertimingpostcts/tt_um_pinwheel.nl.v` view,
  not a later routed database or extracted timing. The continuation inherits
  these same netlist bytes through its frozen checkpoint; diode-insertion ODB
  and later routing snapshots are not covered by that netlist regression.
- **Resident payload:** the host proposal uses START's existing data word to
  initialize a byte shift register, with one shift per instruction entry and
  explicit host result consumption. The serial budget becomes one 292-edge
  frame per byte after initial upload, compared with 325 frames / 94,900 edges
  for reupload-plus-start, excluding status/results and execution in both cases.
  Instruction encoding, hardware cost, proof and implementation remain future
  work dependent on physical headroom. No ISA or host protocol changes are made.
- **Receipts:** `build/validation/controller-contract-03/report.json`, SHA-256
  `603d36fc0a2f60684d7996649038153fd17212147d7a040ca95ccb4395de961c`;
  `build/storage/sram-chip/orientation-05/report.json`, SHA-256
  `689f826d3ba04628ba486cc9627d16d5816842d65b173d2c16e6e55de651ecec`;
  `build/physical/chip-check/orientation-repaired-03/report.json`, SHA-256
  `95ceda8ca19ea299949bcf3e1da54ac511c2976424fbf69f2c7ae5709588f62a`.
  The global-screen comparison is
  `build/physical/hybrid-chip-north/diagnosis/orientation/screen-comparison.json`,
  SHA-256 `51b2cc117aa560143a11148791a7109580f85e695394924426d6d2b47071fef9`.
  `build/physical/hybrid-chip-09-report.json`, SHA-256
  `2936573505709d36425e62e7f8dd8e7adcd27c197e5b154f365ce240870fb9c7`;
  `build/physical/diagnosis/orientation-final/report.json`, SHA-256
  `44accc1fdc04d41e20e8a39b2c948d3dbb7b8fdba678cebf1b6141a61a665bd9`.

## 2026-09-19 — Accepted-cursor coverage and rejected wider-gap screen

- **Controlled placement:** `hybrid-chip-10` changes only `storage1`'s location
  from `(252, 144)` to `(252, 272)` µm relative to the north-facing screen.
  Both macro orientations stay `FS`; the gap grows 49.64→177.64 µm. The move
  is eight horizontal grid pitches. The exact configuration comparison, macro
  geometry, RTL and 43 official signal-pin shapes are checked; power shapes
  regenerate around the moved macro and are not claimed identical. The flow
  exits 0 at `39-openroad-globalrouting` under a 1,800-second cap, four CPUs and
  6 GiB, and the container is independently confirmed absent.
- **Negative result and decision:** global overflow rises 1,255→1,892 (+50.8%),
  Metal4 overflow 208→480, and Metal4 guides overlapping SRAM bodies 129→276.
  Estimated wire length rises 1,869,386→2,349,619 µm (+25.7%). Cells fully inside
  the gap rise 825→4,201 and their footprint occupancy 30.8→47.5%; instance/repair
  area is essentially unchanged. Both supply-connectivity checks report zero.
  Typical pre-route setup/hold are +10.380/+0.254 ns, with two slew and 207 fanout
  violations. Reject this separation-only screen and allocate no detailed
  route. The next hypothesis is a placement exclusion that actually reserves a
  routing corridor, with fresh placement/guides and verification after repair.
  No unique causal diagnosis, extracted timing or layout signoff follows.
- **Proof integration:** `Memory.Sram.Model.Defined` records initialized words.
  `Storage.SramCoverage` proves the inactive prefix below the accepted cursor
  and all 32 words of a valid bank remain defined through every command history
  after initialization. Commit, abort, reset, rejected commands and interrupted
  uploads reuse the existing loader transition. `SramController.control_next`
  connects actual control-register updates; request/address bridges connect
  usable reads to defined words and the related physical copies' returned
  values. No zero-filled SRAM, initial copy equality or minimum duration is
  assumed. Program-word correspondence, scheduler/current/start ownership and
  full emitted-chip composition remain open; direct SRAM's proof is separate.
- **Validation:** the fresh build and audit pass 195 modules, 14,107 declarations
  and 7,235 theorems using standard axioms only. The targeted memory regression
  passes in 374.033 s. The four experimental MLIR emissions and the staged
  hybrid RTL remain byte-identical. This is not a rerun of the 31-suite
  foundation gate or the preceding Python suite.
- **Fresh chip checks:** `widegap-01` passes all three implementations at RTL
  and both mapped corners in 681.941 s, with 508,252 independent chip edges,
  11,840 SRAM core edges and rejection of both SRAM corruptions. Its 218 source
  hashes match the final sources. `widegap-repaired-01` passes those chip edges
  and compiled output-corruption rejection in 96.458 s. It checks the new
  `37-openroad-resizertimingpostcts` netlist inherited by the global-routing
  state, not a new netlist export of the later layout database.
- **Receipts:** `build/validation/sram-coverage-01/report.json`, SHA-256
  `d2a72a2ed392b4ec23ca48a9200fc0fbafee00a800f7f1bc7979ce36e4753b8f`;
  `build/physical/hybrid-chip-10-report.json`, SHA-256
  `07bc4abf76fa74f29a4b41ee1495309f014aeafeb2b3f9aca8a2263cad4e3114`;
  `build/physical/hybrid-chip-widegap/diagnosis/gap/comparison.json`, SHA-256
  `59fc114c3d5c3cad7ae60a35cc8000c15b195173f4b908f5cbc86ef7b772aadb`;
  `build/storage/sram-chip/widegap-01/report.json`, SHA-256
  `2ba55ffa2d102aa73a46f22538ecc35f3a6d2da126a24d85d46a3acfc1788a9f`;
  `build/physical/chip-check/widegap-repaired-01/report.json`, SHA-256
  `7429a80ef67313f9d40d1ddec5f732627f5a88583516be5884e1ef22bc477f17`.
  The [physical study](../chip-physical-study.md#wider-gap-screen-2026-09-19)
  owns the matched-stage table and annotated layout; the manifest binds its
  sources and validation artifacts.

## 2026-09-21 — Verified placement corridors and closed-loop SRAM execution

- **Controlled screens:** the approved cycle reserves placement sites within
  the original 49.64 µm gap using hard `FP_OBSTRUCTIONS`, created before rows.
  Full-height `hybrid-chip-11` and half-height `hybrid-chip-12` retain the exact
  RTL, macro boxes, 43 official signal-pin shapes, views, grid parameters and
  20 ns clock. Both finish at global routing inside separate 1,800-second caps
  with four CPUs and 6 GiB. After legalization, post-CTS repair and global
  routing, both reservations have zero overlapping rows or instances and the
  matching hard blockage. The full strip has 110 temporary boundary straddlers
  at global placement; legalization removes them. The half strip remains empty
  after antenna repair. Power geometry is regenerated, not claimed identical.
- **Screen decision:** the full strip raises total overflow 1,255→1,686 and is
  rejected despite fewer Metal4 guide overlaps. The half strip lowers overflow
  to 870 (−30.7%), Metal4 body-overlapping guides 129→45 (−65.1%) and estimated
  wire length by 1.7%, with essentially unchanged cell/repair area and zero
  supply violations. It passes the predeclared overflow/area/wire gates.
  Timing remains met at the same pre-route typical stage and electrical counts
  do not regress; small reductions in positive setup/hold margin are reported.
  This interpretation of the timing gate is explicit in the frozen comparison.
  Only the half strip receives the one allocated 5,400-second continuation.
- **Bounded continuation:** `hybrid-chip-13` reaches that limit in antenna
  reroute pass 1; exit 124 and independent absence checks confirm termination.
  Matched first-pass iteration-59 markers improve 126→92 (−27.0%). Pass 0 ends
  at iteration 64 with 73 markers fully inside SRAMs: 68 Metal4 and five Metal3.
  Its antenna check finds 49 net/55 pin violations, adds 82 antenna cells and
  starts a new pass. The final completed logged entry is pass 1, iteration 35,
  with 230 markers; 225 are inside macros and five within 5 µm. The reservation
  remains empty in all matched snapshots. The complete routing/antenna step
  does not finish. Latest completed typical STA is +8.517/+0.063 ns with
  62 slew, 25 capacitance and 219 fanout violations, before the later repair;
  fast/slow metrics are inherited. Retain the half strip; next screen macro-body
  routing obstructions before regenerating global guides. No additional run,
  backend promotion, storage/protocol change or physical signoff is claimed.
- **Proof integration:** `SramContents` relates every defined dictionary word
  to the existing loader image and preserves that relation through accepted
  writes. `SramExecution` composes the actual arrays, controller addresses,
  held Q, start bypass and execution invariant. Every controller register
  matches the shared netlist; one initializing edge establishes trace equality
  with the capacity-adapted atomic reference from arbitrary arrays and Q.
  The retained backend image is specification bookkeeping. No SRAM clear,
  initial copy equality, new interpreter, duration rule or UART change is
  assumed. External macro binding, package composition and emitted-chip
  read-back remain separate; direct SRAM does not inherit the hybrid proof.
- **Validation and correction:** the first audit rejected a native `bv_decide`
  dependency. The comparison in progress was cleanly interrupted before that
  source was changed. The corrected proof uses ordinary bank separation and
  arithmetic; the allowed axiom policy is unchanged. Fresh `sram-execution-02`
  passes all 31 suites in 1,476.691 s and audits 197 modules, 14,217 declarations
  and 7,313 theorems with standard axioms only. The Python suite passes 105 tests
  with two platform skips. Failed/interrupted attempts remain retained.
- **Fresh chip checks:** `corridor-02` passes direct/hybrid/FF RTL and both
  mapped corners in 740.287 s. Each simulation checks 508,252 external-pin edges;
  SRAM cores check 11,840 edges, including 1,000 consecutive branches, and both
  SRAM mutations are rejected. All 220 comparison sources and 266 foundation
  sources match the final checkout. Four experimental MLIR emissions and hybrid
  RTL remain byte-identical to the preceding validated emission and prepared
  physical inputs. `corridor-repaired-01` passes the full external-pin oracle
  and compiled output-corruption control in 108.392 s. It identifies the half
  strip's exported post-CTS netlist, not a later layout-database export.
- **Receipts:** `build/validation/sram-execution-02/report.json`, SHA-256
  `96d484981d55068fce5ea09484e178cd847a935ac53ff9fc028baefe40d1250c`;
  `build/validation/corridor-cycle-01/screen-comparison.json`, SHA-256
  `361277196d6e3998cda0eaa5a503d331ece41a8c2da385f3ed7978c57fdffb77`;
  `build/storage/sram-chip/corridor-02/report.json`, SHA-256
  `e8096258f929b677c578fd733d2a6781a9f70ae7e9797b326307c3ec32ac8353`;
  `build/physical/chip-check/corridor-repaired-01/report.json`, SHA-256
  `c3555b83bb6ef43c0cf5c1e8c02fc8939e07771f503e96c41a74c05a5f5c6a71`.
  The [physical study](../chip-physical-study.md#reserved-corridor-screens-2026-09-21)
  owns geometry, matched comparisons and continuation results; its manifest
  preserves the earlier phase hashes and records this cycle separately.
  `build/physical/hybrid-chip-13-report.json`, SHA-256
  `329a519f6378768f5e92f739a6f48ec503ab93a2d923c7b6df9fb30a227fd852`;
  `build/validation/corridor-cycle-01/continuation-comparison.json`, SHA-256
  `7d796547a50ecde1d2a576ae00876e29a272533aff50cbaf5162352f6389dcc8`.

## 2026-09-21 — Cheap routing diagnostics and rejected early obstructions

The approved diagnostic cycle reads settled artifacts, adds repeatable static
checks, and allocates one global screen with a 900-second cap; it allocates no
new detailed route. Its source baseline is
`build/validation/routing-diagnostics-01/baseline.json` on
`codex/chip-contract-consolidation`, base commit `a256e7847dc3`.
Earlier local work and receipts are retained.

The preceding `hybrid-chip-14` three-hour retry completes detailed routing and
RC extraction but times out before extracted STA completes. Its final antenna
check reports three nets/four pins. Fresh static checks show that retained
73/174/283/384 pass-end marker counts include old and duplicate entries: current
snapshot counts are 75/103/112/103. The completed routing ODB independently
reports 103. The shorter attempt-13 log's 35/230 endpoint is corrected to 38/198
using the consistent outer log and matching report, without overwriting the
earlier snapshot analysis.

`hybrid-chip-15` derives two early Metal4 signal obstructions from the frozen
post-CTS checkpoint and completes its global-routing process in 44.360 seconds.
The objects survive and pin-access checks pass, but global guides and the entire
saved Metal4 capacity/usage map are identical to attempt 12. Reject this
ineffective mechanism before allocating detailed routing. The proposed next
mechanism is explicit regional capacity control; it was not routed this cycle.

The final probes use resolved Metal2–Metal4 limits. Initial probes using an
incomplete configuration's Metal1 default are preserved and superseded; correct
repeats reproduce the same counts. The new report also binds inherited timing to
its source stage: attempt 15's older resizer hold estimate is not comparable to
attempt 12's post-CTS STA. These safeguards prevent false physical conclusions.
The Python suite passes 121 tests with two platform skips; the final receipt
guard change additionally passes all seven targeted evidence-selection tests.
Lean and RTL behavior are unchanged. All diagnostic containers are absent and
the preceding retry heartbeat stays paused.

The [diagnostic guide](../routing-diagnostics.md) owns commands and limitations.
`build/validation/routing-diagnostics-01/completion.json` indexes settled checks,
source identities and the rejection. `gate-final-02/report.json` takes 6.702 s;
resolved static checks take 9.067–9.538 s each, and pin access 3.548/3.559 s.
The tracked physical manifest appends runs 14/15 and this cycle while preserving
all preceding run objects. No foundry DRC, antenna or timing closure is claimed.

## 2026-09-21 — Costed hybrid/direct architecture comparison

Stepped back from routing adjustments to compare the existing organizations at
the same whole-chip mapping boundary. Added `report-chip-architecture.py`, which
reads the saved typical-corner JSON, accounts for every mapped FF and measures
macro ports and structural dependency cones. The pinned Yosys only reads the
already simulated, receipt-hashed Verilog; all named sequential inputs and
package ports match the saved JSON structurally. No synthesis, simulation,
physical experiment or Lean rebuild was run. All 220 original comparison source
hashes still match, and previous routing receipts were preserved.

Hybrid has 2,560 map FF bits; direct has 1,760 upload scratch bits; both have 335
common FF bits. Six unused cached-word bits explain the emitter/mapped-count
difference. Hybrid's macro-address union contains 6,037 combinational cells,
versus 607 for direct. Both responses reach both address ports, including the
same 21 response bits per macro in the union. Direct saves 113,189 µm² of mapped
standard cells and adds 199,227 µm² of macros. Preserve both candidates: this
identifies a structural trade, not a routed winner or a routing-failure cause.

The [architecture study](../physical/chip-architecture-study.md) owns state diagrams,
the complete upload/execution schedule, communication/area tables, source
interpretation and the next assembly-description increment. Its selected
measurements are in `physical/experiments/chip-architecture-results.json`.
`build/validation/chip-architecture-02/report.json` has SHA-256
`f5c87c5e9f6f0d6567aa682347783e7597a51c482fa88f64b61d9b628c6c4ce0`;
its analysis/readback phase takes 1.793 s. `tests.json` and `analyzer-tests.log`
record nine passing tests, including corrupt logic/sequential inputs and invalid
graph/ownership controls. The development report in `chip-architecture-01` is
retained. No generic physical IR or RTL hierarchy was introduced. Status now
allocates the ownership/interface/schedule description before another physical
change; regional capacity control remains a separate deferred diagnostic.

## 2026-09-21 — Shared SRAM assembly and checked edge obligations

Implemented the approved first assembly increment while preserving the existing
circuit. `Storage.SramAssembly` now owns package composition, register lists and
labels formerly in `test/SramChipEmit.lean`. Typed register constructors select
nine state owners; emission and the architecture analyzer consume that one
description. The test emitter serializes MLIR and an assembly JSON manifest.
No pipeline state, generic compiler framework or physical hierarchy was added.

The complete, uniquely named request interface supplies five pre-edge signals;
two macro responses complete seven crossings. The analyzer binds all named state
and ten address/data/enable terminals per variant against both saved JSON and
mapped-Verilog read-back. It checks hybrid nine-to-six-bit address narrowing,
broadcast connections, response direction and interface phase. `SramSchedule`
states ten obligations using existing controller/array/execution definitions:
exclusive access, candidate readiness and renewal, response arrival, start-word
ownership, commit/pending/bypass/save behavior, active-bank isolation and writes
to both replicas. Only the generic access obligation covers both variants;
direct execution does not inherit the hybrid proof.

`build/validation/sram-assembly-check-02/report.json` records the successful
cached library/emitter build, whole-library audit, extended `Interfaces` suite,
four emissions/exports and both mapped read-backs. Its SHA-256 is
`f1e7cce1e8f166a112fe3e124e86a00f4c58eddb872643520e77950b87e46de2`.
All four MLIR and RTL hashes equal the earlier `corridor-02` comparison. Current
source hashes are captured separately: the assembly refactor changes the library
entry point and emitter, and adds two library modules. The audit reports 14,395
declarations / 7,354 theorems with standard axioms only. The gate takes 17.108 s,
including 1.746 s analysis/read-back. Its `tests.json` and `analyzer-tests.log`
record all 13 passing focused tests with missing/duplicate state, wrong ownership,
crossing, phase, width, response-swap and address-bit mutations. Earlier graph
and structural-signature controls remain in the same suite.

The first development gate `sram-assembly-check-01` is preserved: its build and
audit passed, then the interface test failed to elaborate rank-polymorphic local
values. Explicit type annotations fixed that test before the successful repeat.
`sram-assembly-01` retains the pre-edit source hashes and original emitter. All
earlier routing and architecture receipts remain unchanged. No new synthesis,
RTL simulation, placement or routing was run; the full foundation regression
was not rerun for this byte-identical hardware refactor.

The [assembly study](../physical/chip-architecture-study.md#checked-assembly-and-edge-obligations)
and `physical/experiments/sram-assembly-results.json` own the new interpretation
and selected receipt. The remaining structural increment is combinational
producer/consumer ownership and a mapped locality hypothesis. State names and
edge obligations do not assign every gate to a region. External macro behavior,
full package proof/read-back and physical closure remain distinct obligations.

## 2026-09-21 — Computational map and a rejected locality projection

Extended `SramAssembly` with eight width-indexed computations from the existing
controller expressions. The probes reuse the actual emitter cache and reject
any added operation. `SramSchedule` now also checks actual read/write address
cuts for both variants and the hybrid running/read relation. Source analysis
tracks selected bit positions; mapped analysis assigns every combinational cell
by its sequential/package consumers, counting shared producers once.

The hybrid all-mode/read-branch address unions contain 1,312/1,239 unoptimized
source operations; direct contains 260/185. Read branches shed the 64 serial
payload bits, but hybrid retains all 2,560 map bits and direct retains no
scratch bits. This is a read-edge envelope including idle and commit, not a
timing false-path certificate. The hybrid fetch region owns 12,094 of 12,593
mapped combinational cells, too broad for a useful placement constraint.

The saved physical view retains 2,901 FFs versus 2,895 in the typical mapping
and almost entirely different cell names. A new connectivity-based selection
finds 36/34 cells in the final three private address stages, with 58/51 incoming
net incidences (100 distinct nets across both groups). Their mean cell-center
distances from SRAM address-pin envelopes are 314.021/182.863 µm.

Tested an analysis-only projection toward two pin-adjacent windows on existing
rows, outside the macros and verified half corridor. Shorter output connections
do not compensate for longer inputs: the bounding-box half-perimeter estimate
over all 170 incident signal nets grows from 18,503.610 to 34,161.030 µm
(+84.618%). Neither group alone nor any of the 70 individual projections
improves the estimate with neighbors fixed. **Defer this projection before
placement.** The screen permits cell overlap and is not an optimized placement,
routed length, timing result or impossibility proof. Next cost a complete map
bit plane including both atomic banks, both read trees and shared decode nets.

`build/validation/chip-organization-check-03/report.json` records the final gate,
SHA-256 `8872735b6d46cd552d5b5976bcbf18fd0ac42ce84aa24aa35e515f48f28e8cab`.
All four regenerated MLIR and RTL pairs equal the saved `corridor-02` comparison;
mapped boundary signatures and consumer summaries match Verilog read-back.
The audit covers 14,479 declarations / 7,393 theorems using standard axioms only.
`Interfaces` and 21 focused Python tests pass. Cached checks/export take
13.168 s, analysis/read-back/projection 1.942 s, total 15.110 s. Final input hashes
were verified unchanged. `physical/experiments/chip-organization-results.json`
owns selected results; `sram-address-locality.json` preserves the tested windows.

The first gate `chip-organization-check-01` passed Lean and artifact checks but
rejected the saved export's old geometry-helper identity. A read-only OpenDB
export in `chip-organization-01` took 2.810 s and reproduced everything except
that helper hash. The named export container's absence was independently
confirmed. The sandbox-denied initial invocation and the successful retry have
separate receipts. `chip-organization-check-02` completed the computational map;
`-03` adds the reusable projection and its analytical rejection test. Existing
receipts remain unchanged. No new synthesis, RTL simulation, placement or routing
was performed; no hardware behavior, admission or execution edge was changed.
External macro/full package binding, direct proof and physical closure remain
separate obligations.

## 2026-09-21 — Complete map slice and read-tree tile costs

Completed the approved slice study and one bounded comparison of small word
groups. `SramAssembly.indexLocation` now exports bank/word coordinates from
typed constructors; `chip_map_slice.py` assigns data-bearing mapped logic by its
stored-map support and absorbs control only when every consumer is local.
It checks exact per-bit map/read support and accounts for remaining shared
decoding once. Retained Liberty areas sum to the original 292,580.0514 µm²
standard-cell total. No hardware behavior changed.

The complete bit-zero plane contains 512 FFs and 1,986 private gates, costing
48,576.5532 µm². It imports 1,073 nets: 520 for updates, 220 for read zero,
330 for read one and three for both. Of these, 1,062 directly serve at least
two planes. Its outputs are the two index bits delivered to the SRAM replicas.

The source `Execution.readTree` selects low address bits last along the data
path. Its natural 16-entry subtrees therefore share a low nibble, e.g.
0,16,…,240. A consecutive group in bank zero exports 90 nets and keeps only
10/0 gates from the two read cones; the corresponding strided group exports
13 and keeps 76/76. The strided group owns 80 FFs and 294 private gates,
7,662.0978 µm², but still imports 280 nets. Whole-map cut totals are 1,265
for five bit planes, 4,099 for 32 consecutive groups and 1,615 for 32 strided
groups. Different group sizes and graph cuts do not determine a routed winner.

The next [specified experiment](../../physical/experiments/map-tile-plan.json)
is one 16×5 tile with local read/write decoding: 18 functional input bits,
ten output bits and the existing clock, without new pipeline state. This is an
unimplemented interface target, not a measured reduction from 280 inputs.
Prove its two reads and all updates against the existing projection, map the
block with its boundary intact, and measure decoder duplication and remaining
map glue before allocating placement. The [slice study](../physical/map-slice-study.md)
owns the interpretation; `physical/experiments/map-slice-results.json` owns
selected measurements.

`build/validation/map-slice-check-01/report.json`, SHA-256
`ffee1f5c04158c4503f196b6e5b9d484dec3c542f2bbafc4ae1b1470db7987c0`,
passes library/emitter build, the standard-axiom audit, `Interfaces`, four
MLIR/RTL identity checks and both mapped-Verilog read-backs. Selected boundary
signatures, state membership, all partition costs and cell counts match the
independently parsed Verilog. The audit covers 14,484 declarations and 7,393
theorems. All 30 focused Python tests pass, including shared/external consumers,
cross-bit errors, invalid coordinates, read-tree grouping and renumbered artifacts.
The gate takes 17.166 s: 14.827 s build/audit/emission and 2.339 s analysis/read-back.

`build/validation/map-slice-01` preserves the pre-edit hashes, emitted manifest
and two development analyses. Earlier receipts and experiments are unchanged.
No new synthesis, RTL simulation, OpenDB export, placement or routing was run;
the full foundation regression was not repeated for byte-identical hardware.
Macro/full-package proof boundaries, physical closure and licensing remain open.

## 2026-09-21 — Proved local-decoding tile and complete map cost

Implemented the approved 16×5 tile experiment by reusing the existing
`Memory.Flops.circuit 4 5 2`. `Storage.MapTile` proves cursor decomposition,
each store update, both restricted reads, selected full lookup, and correspondence
to actual hybrid controller updates and candidate read addresses. All inputs
and states are covered without cleared memory or an extra execution edge.
The chip itself is not rewired to the candidate.

The compact 18-input-bit/10-output-bit boundary survives typical and slow
mapping. One tile costs 7,664.0256 µm² (80 FFs and 178 combinational cells).
All 32 copies plus 292 glue cells cost 250,189.4304 µm², versus
253,254.9348 µm² for a matched flat map: 1.210442% less. Read gate depths change
14/13→9/9 and next-state depth stays eight. There are 369 distinct signal nets
at tile interfaces, excluding clock. Composed cursor/data fanout reaches 224
versus ten for the flat map, exposing the next missing distribution cost.
Per-module ABC estimates do not include the whole broadcast load and do not
establish an end-to-end timing win.

`build/storage/map-tile/local-decode-03/report.json`, SHA-256
`3c69d92ca85e0d81030bad2b69c0184218e5f0b0273b5f97446fb2b97ac929e3`,
passes in 77.772 s. Nine independent arbitrary-state SAT checks compare both
outputs and every next-state bit at RTL and in both mapped corners for tile,
flat map and tiled map. Mapped checks use Verilog read-back; state, area,
depth and fanout agree with mapped JSON. A joined-reader mutation is rejected.
Six checker tests and the existing 30 architecture tests pass. The library
audit covers 14,526 declarations and 7,421 theorems with standard axioms only.

`build/validation/map-tile-boundary-01/report.json`, SHA-256
`58e1acdde31fc838ec692bcc1e6bbf9ec66d7b415831d7d82973905011c6a021`,
passes in 11.456 s and confirms all four production MLIR/RTL pairs remain
byte-identical to `corridor-02`. Its 239 frozen inputs and the tile experiment's
209 frozen inputs match the validated checkout. `build/validation/map-tile-01`
retains the pre-edit snapshot, initial emission and focused test logs.

Failed attempts are preserved: `local-decode-01` stopped at the axiom audit
and led to replacing native certificate evaluation with kernel arithmetic;
`local-decode-02` stopped when its negative control did not reject and led to
correcting both the mutated JSON port and its same-named net binding. Only
`local-decode-03` is selected. The [tile study](../physical/map-tile-study.md) owns the
interpretation and `physical/experiments/map-tile-results.json` pins the result.
Earlier physical receipts and the original tile plan are unchanged. Next cost
bounded buffer distribution before whole-chip integration or physical work.
No placement, routing, Docker run, protocol change or backend promotion occurred.

## 2026-09-21 — Costed buffer distribution with tile boundaries intact

The approved follow-up inserts explicit IHP `sg13cmos5l_buf_1` trees into the
retained map hierarchy. Every tile, glue and library module stays unchanged.
Actual internal pin loads and glue pass-through aliases determine each tree;
leaf groups stay within logical banks. Seventeen shared bits need 346 buffers,
adding 2,511.1296 µm². The complete map becomes 252,700.5600 µm² versus the flat
253,254.9348 µm²: only 554.3748 µm² (0.2189%) of the original saving remains.
Maximum signal fanout falls 224→10, read gate depth rises 9→10 versus flat
14/13, and next-state depth stays eight. Both library corners agree. No state
or execution edge is added; sink count is a structural budget, not an electrical
limit or proof of improved timing.

`build/storage/map-tile/distributed-02/report.json`, SHA-256
`4a9ad92c4464506580df6f4afc603b7dbdbe722250e04d5ca6052081350a0fb2`,
passes in 37.020 s. Two independent arbitrary-state SAT checks cover both
outputs and every next-state bit at typical and slow corners; a deliberately
inverted distribution buffer is rejected. Flattened JSON and reread Verilog
agree on all cell, state, area, depth and fanout measurements. Every command
has a 180-second cap. Reusing the retained mapped artifacts avoids new synthesis.

The checker verifies the selected baseline, its 102 artifacts, tools and pinned
libraries, and reproduces the original flat/tiled metrics before modifying
the parent wiring. Its 213 current inputs are frozen. Fourteen focused Python
tests pass; the factored SAT helper also proves the saved generic tile and
rejects the original joined-reader mutation. All 239 inputs to the existing
production emission gate are unchanged, retaining its byte-identity and Lean
audit evidence. `build/validation/map-distribution-01` keeps the pre-edit hashes,
test receipts and input-identity verification. No new Lean proof, production
emission or physical run was needed.

`distributed-01` stopped before export because generated cell and wire names
collided in Yosys. Distinct names and a regression resolve that checker defect;
both attempts are preserved. The [tile study](../physical/map-tile-study.md) owns the
interpretation and `physical/experiments/map-distribution-results.json` pins the
selected result. All 43 earlier experiment manifests remain unchanged.

The candidate now has explicit distribution, near-equal area and fewer read
levels. The next discriminator is one experimental whole-chip integration:
preserve actual admission, bank/PC selection and execution edges, then check
complete-chip function and mapped costs before allocating electrical/physical
work. A map-only result does not transfer automatically to the chip. No
production replacement, backend promotion, placement, routing or Docker run
occurred in this step.

## 2026-09-22 — Complete-chip tile integration passes function, fails structural screen

Completed the experimental controller/map split. Shared `TiledMap` owns the
interface and selection glue previously in the probe emitter; all four original
map artifacts remain byte-identical. `TiledController` reuses actual admitted
pushes, inactive write bank, cursor, payload, candidate PCs and selected bank.
Its emitted controller excludes the 2,560 map bits now owned exactly once by
32 tiles. The existing SRAM/serial/sampler/result assembly is reused. General
netlist substitution, remaining transitions, core observations, map reads and
every map update have Lean correspondence results. This adds no execution edge
or new capacity/host protocol, and does not add a complete Lean theorem for the
external macro model and package trace.

`build/storage/tiled-chip/integration-03/report.json`, SHA-256
`b2bd581024355682a5fecc70eb3d05181a3182aa17d76851a6efb25ab59e27d4`,
passes validation in **254.643 s**, with a 180-second cap per command. Four SAT
checks cover core/chip RTL and both mapped chip corners; joining the SRAM
addresses is rejected. Actual package aliases and every macro/control terminal
are checked. The independent pin oracle passes 508,252 edges on chip RTL and
each mapped corner; the core oracle passes 11,840 edges with 1,000 consecutive
branches. Total simulated edges: 1,536,596. Twenty-four focused Python tests also
pass. The audit covers 14,831 declarations / 7,529 theorems with standard axioms.

Both mapped chips prune cached-word bits 3–8: 2,901 generic state bits become
2,895 FFs. The comparison excludes only those absent slots' next values while
keeping all reference current-state inputs arbitrary. It still proves every
output and surviving next-state bit; no reset/reachability assumption hides a
dependency. Exact FF bijections, actual external-port checks and live-use/pruning
negative tests guard the projection. Independent Verilog read-back reproduces
the complete mapped census and costs.

Typical standard-cell area falls 292,580.0514→288,888.2010 µm² (**1.261826%**).
The two SRAM footprints remain 100,978.2656 µm², so cells plus macros fall
393,558.3170→389,866.4666 µm² (**0.938069%**). Combinational cells fall
12,593→8,327; next-state depth falls 27→24. However, address depth changes
29/29→30/30 and maximum signal fanout 11→15. Slow mapping has one extra candidate
buffer and address depth 30/30 versus baseline 29/30. Both corners fail the
agreed structural screen. No timing, placement, routing or Docker run follows.

`build/validation/tiled-chip-02/boundary-diagnostics.json`, SHA-256
`c2c081e998856aedda76efd3eeb3a68194987ac92e3d5338158f35024d165584`,
binds its observations to the settled maps. Cursor bits zero/one drive eight
engine and seven map pins each. Upload-data bits three/four drive seven engine
pins, four map distribution roots and two macro pins. One deepest candidate
address path starts at cached-word bit 35 and has twenty engine gates plus ten
map gates. A local interface/load budget does not establish a complete-chip
budget. These are conservative graph measurements, not electrical delays.

`build/validation/tiled-chip-boundary-01/report.json`, SHA-256
`a4115d2928fbb2aac8c8001d3244a693100cc99d60991de90035dc571643f77d`,
passes in 16.161 s: all four retained hybrid/direct MLIR/RTL pairs remain
byte-identical, with audit, `Interfaces` and both mapped Verilog read-backs.
Its 241 frozen inputs and the new comparison's 248 frozen inputs match the
completed checkout. The comparison records 119 generated artifacts.

`integration-01` stopped at a reserved Verilog instance name. `integration-02`
passed RTL equivalence but stopped when mapped pruning was compared against
the generic state list. Both are retained. The third run verifies the matching
mapped pruning and arbitrary-reference-state relation described above.
`build/validation/tiled-chip-01` preserves initial work and its pre-edit snapshot;
`tiled-chip-02` preserves the continuation snapshot, proof work, focused tests,
projection check and diagnostics. All 44 prior experiment manifests remain
unchanged. The [tile study](../physical/map-tile-study.md) owns interpretation;
`physical/experiments/tiled-chip-results.json` pins the selected result.

Retain this candidate as verified evidence and defer timing/physical allocation.
The next hypothesis is to optimize controller and selection glue together while
retaining storage tiles, and to count producer loads across all consumers.
Require another bounded full-chip mapping/equivalence screen before allocating
physical work. The production baseline, previous physical receipts, macro
locations and half-height corridor are preserved; licensing remains pending.

## 2026-09-22 — Combined controller/selection mapping and complete load budget

Completed the [combined boundary comparison](../physical/map-tile-study.md#combined-controller-and-selection--september-22)
without changing Lean definitions, RTL, SRAMs or the execution schedule. An opt-in
synthesis mode retains 32 storage tiles and combines the surrounding logic.
The distribution helper counts controller, tile and fixed macro loads, preserves
tie-offs/clock wiring, and reproduces both prior separate mapped hierarchies and
buffer receipts exactly.

- **Result:** both corners map to 289,427.1156 µm² of standard cells, 1.077632%
  below the original hybrid; 354 distribution buffers are included. Maximum
  fanout falls from the previous candidate's 15 to ten. Address depths are 30/29,
  next-state depth is 25, and package output depth increases to 15. The maximum
  address-depth requirement fails at both corners. Keep timing and physical
  allocation deferred; neither tiled candidate is promoted.
- **Evidence:** `build/storage/tiled-chip/combined-01/report.json`, SHA-256
  `a3d49d4c94914288b0c1f1025813c553912b2ac9327a0c3c648e6072b9998d31`. Four positive arbitrary-state
  SAT checks, rejected address/buffer mutations, 1,536,596 simulated edges and
  27 focused Python tests pass. The unchanged standard-axiom audit covers 14,831
  declarations / 7,529 theorems. The gate takes 274.167 s with a 180 s per-command
  cap; its longest command takes 74.092 s. All 252 inputs and 123 generated
  artifacts match after completion. All 45 preceding experiment manifests remain
  unchanged; retained hybrid emissions and tiled RTL/state projections match.
- **Diagnosis:** the longest paths start at cached-word bit 35 and contain
  eighteen gates before a candidate PC, one distribution buffer, four tile gates
  and seven/six final selection gates. The diagnostic's first optional named-net
  probe encountered an optimized-away alias; that attempt is retained. The final
  diagnostic records absent named bits as `null` and independently reproduces
  every live address path and the complete mapped metrics.
- **Next discriminator:** connect this candidate-PC dependency to actual
  decode/dispatch expressions and check its relevance on admitted executions.
  Then evaluate a cycle-preserving refactor with explicit correspondence if
  computation moves earlier. A conservative path count does not establish
  sensitizable delay or authorize an added execution cycle.

The [selected receipt](../../physical/experiments/combined-chip-results.json)
binds the report, diagnostics, tests and current synthesis/helper hashes. No
physical tool, container, commit, push, licensing decision or heartbeat change.

## 2026-09-22 — Fetch deadlines, retained STA and electrical repair cost

Completed the [fetch contract study](../fetch-contract-study.md) with the
existing assembly/schedule abstractions. New Lean facts prove arbitrary-state
capture forwarding, the entered-word address calculation's 21-bit metadata
dependence, and its 18-bit reduction under an explicit valid-word premise.
Two valid programs entered from rest demonstrate that cached bit 35 can change
the same-edge branch and following candidate address. Production and tiled
emissions remain unchanged. No false paths or added pipeline cycles.

- **Timing:** six complete-chip Liberty STA checks of retained baseline,
  separate and combined mappings complete in 5.087 s. Slow setup slack is
  +10.26/+10.03/+10.11 ns; each limiting path begins at SRAM Q. Cached-word
  paths have more than 2 ns additional slack. Upload-data-to-SRAM hold fails,
  and fanout violations number 1,300/687/685 per corner. Wire parasitics and
  clock-tree effects are absent. Report: `build/storage/sram-timing/fetch-contract-03/report.json`,
  SHA-256 `afb5634061f07b84c47d15c843f7e5f2bff02a1ca96d0b2c171e2ab42554d1e7`.
- **One controlled repair:** the pinned library specifies fanout eight, not
  the earlier structural budget ten. The exact combined mapping receives
  1,369 noninverting buffers, costing 9,935.6544 µm². Both corners then report
  zero fanout/slew/capacitance/pulse-width/period violations, but hold remains
  negative. Slow setup changes only +10.11→+10.13 ns; address depth grows
  30/29→37/36. Whole-controller arbitrary-state SAT passes at both corners,
  an inverted buffer is rejected, and mapped Verilog read-back agrees.
  The 15.094 s probe's longest command is 4.041 s. Report:
  `build/storage/electrical-distribution/fanout-01/report.json`, SHA-256
  `cada2e7052a84f685a98a5d7be22e02964c08620e031bead3c145a579423746c`.
- **Validation:** the 13.141 s final gate passes 30 focused Python tests, the
  new valid-program witness, 128 consecutive-branch checks, default build and
  the standard-axiom audit (14,847 declarations / 7,543 theorems). Four freshly
  emitted core/chip MLIR files and the assembly manifest match the retained
  comparison byte for byte. Both old separate distribution results reproduce.
  All 46 preceding experiment manifests are unchanged. The selected timing
  and repair reports' 43 inputs and 67 artifacts verify; all eight corresponding
  containers were independently confirmed absent. The final gate binds 221
  code inputs and 16 artifacts. Report: `build/validation/fetch-contract-01/report.json`,
  SHA-256 `36a8dc1e982cf7dac31a5cfdff27a8fcafc6b1d1b0b111be6bdff6636592a181`.

The first timing attempt stopped at a private-cell-name lookup mismatch and
confirmed cleanup; the next succeeded in 3.983 s. The selected third run
verifies the shared runner refactor with identical numeric results. These
receipts remain preserved. The initial native SAT lemma failed the existing
axiom audit and was replaced by a kernel-checked mask/case proof; the final
audit passes without widening its trusted axiom list.

Adopt the cheap checks and retire strict depth reduction as a prerequisite for
STA. Future successful tiled-chip checks now report timing eligibility while
retaining the historical structural score as a diagnostic; the policy source
hash is recorded in the [selected receipt](../../physical/experiments/fetch-contract-results.json).
Keep the flat repair as a cost probe: it is 2.32% larger than the original
hybrid and is not promoted. Next integrate the real load budget into local
map decode/selection before a placement/global-routing comparison. No routing,
clock-tree synthesis, extracted timing, commit, push, licensing or heartbeat
change occurred.

## 2026-09-22 — Map with the library load budget

Completed one [bounded local-load comparison](../fetch-contract-study.md#local-mapping-with-the-library-budget--september-22),
selected by [this receipt](../../physical/experiments/local-load-results.json).
The pinned ABC buffer limit defaults to ten; the library budget is eight.
The new opt-in complete-chip mapping applies eight during ABC and aggregate
distribution, with the same 16-word tiles, readers, state and execution schedule.

- The isolated control/candidate tile checks pass at both corners in 1.218 s.
  Nine extra buffers per tile reduce write-data input load seven→two.
- Complete standard-cell area is 290,943.9540 µm² at both corners, 0.559196%
  below the original baseline and 8,418.8160 µm² below flat repair. Local
  tiles add 288 buffers, surrounding mapping adds 50, and shared distribution
  falls 354→225: net 209 extra buffers. All nonbuffer cell counts are unchanged.
- Four complete-controller SAT checks, two rejected mutations and 1,536,596
  independent simulated edges pass in 252.468 s; the longest command is
  67.035 s against its 180 s cap. Original and tiled emissions stay identical.
  Report: `build/storage/tiled-chip/local-load-01/report.json`, SHA-256
  `2d9e83fe72e888cd199d6e1a8e9392fc89fc1db9ef4b756309750703fa323c5b`.
- Six cell/SRAM timing checks take 5.125 s and reproduce the baseline/separate
  controls. Candidate typical/slow setup slack is +13.50/+10.52 ns and hold
  is −0.58/−0.86 ns. All measured electrical violation counts are zero;
  all six containers are independently confirmed absent. Report:
  `build/storage/sram-timing/local-load-01/report.json`, SHA-256
  `a4a8687a5b9549e86b7ab7787524ce37b5dd05f93ad578895332f4717dcb7a05`.
- The final verification checks every artifact in six retained reports,
  current experiment inputs, 32 focused Python tests and unchanged identities
  for 267 Lean sources and all 47 preceding experiment manifests. The main
  gate audits 14,847 declarations / 7,543 theorems with standard axioms only.
  Validation: `build/validation/local-load-01/report.json`, SHA-256
  `a862281d26dc3ab8157a87106e5adfa58f8256c82459e8991d16b158d3872c3f`.

Retain this mapping for a bounded physical comparison, beginning with exact
mapped-netlist intake. The old physical preparer consumes original hybrid RTL;
the experiment must preserve the new mapping instead of silently resynthesizing
it. Matched placement, clock distribution, hold repair and global congestion
will decide whether the small area margin survives. No placement/routing run
or production promotion occurred; the old routing and antenna issues remain.

## 2026-09-22 — Preserve the mapping through placement and hold repair

Completed the [bounded exact-mapping comparison](../chip-physical-study.md#exact-mapping-placement-and-hold-repair--september-22),
selected by [this receipt](../../physical/experiments/mapped-physical-results.json).
The preparer now accepts the retained mapping, starts after synthesis, and
requires a fresh floorplan ODB connection check before physical continuation.
Both imports preserve all named cells and terminals; only one high and one low
constant tie cell are added per case. Five new tests cover connection mutation,
unknown/conflicting ties, stale receipts and unsafe continuation starts.

- Both cases use the same 20 ns boundary, two macro positions, half corridor,
  pinned tool/PDK and repair controls. Imports have 120 s caps; the two sequential
  physical flows each have a 600 s cap, four CPUs and 6 GiB. There is no detailed
  routing or automatic cap extension.
- `mapped-base-place-01` times out during global routing after completing
  placement, clock synthesis and hold repair. `mapped-local-place-01` completes
  global routing with 1,312 overflow in 92.868 s summed step runtime. Both exact
  flow containers are independently confirmed absent. The timed-out baseline
  has no completed global-route congestion/timing result.
- Total instance area, including macros, is 485,738.1152 versus 473,519.9456 µm²:
  candidate reduction 2.515382%. Both final databases retain the same macros
  and a clear corridor. Fresh matched post-repair placement-RC STA passes hold
  in all three screens; slow setup is +0.580206 versus +6.09608 ns.
- Fresh candidate coarse-route RC reduces slow setup to +2.00859 ns and reopens
  two fast-screen hold violations at `A_DIN[0]`, worst −0.105158 ns. There are
  203 clock-tree fanout violations, 57 slow slew violations and six capacitance
  violations, five on SRAM outputs. Fast screening still mixes −40 °C cells
  and −55 °C SRAM. No extracted timing or qualified closure claim follows.
- Three-corner checks start with empty inherited metrics, confirm propagated
  clocks and record placement/global-routing RC mode. Their successful reports
  are `mapped-base-diagnostics-04`, `mapped-local-diagnostics-01` and
  `mapped-local-postrepair-01` under `build/physical/mapped-diagnostics/`.
  Three preceding read-only wrapper attempts failed on SDK API/serialization
  details; their reports remain, with containers absent. Physical runs were
  not repeated. The first closeout test invocation failed on Python package
  discovery; its receipt is also preserved separately from the successful gate.
- Fresh final-ODB exports each pass 508,252 original independent pin edges and
  reject a compiled public-output mutation. Reports are under
  `build/physical/chip-check/mapped-base-oracle-01/` and
  `build/physical/chip-check/mapped-local-oracle-01/`. The gate checks 402 retained
  hashes and passes 57 focused tests. All 267 Lean sources and all 48 preceding
  experiment manifests remain unchanged. Validation:
  `build/validation/mapped-physical-01/report-02.json`, SHA-256
  `db3978fca891740b51a5505ef3accdee93ec9df042a2b06f1912e479b6a605ab`.

Retain the candidate and target clock distribution, SRAM output loading and
upload minimum-delay repair before more detailed routing. The digital schedule
and program contract are unchanged; the next discriminator concerns the
implementation's actual clocks, loads and arrival windows. No commit, push,
license or heartbeat change occurred.

## 2026-09-22 — Clock load budget and ineffective generic repair

Completed one [bounded clock/SRAM comparison](../chip-physical-study.md#clock-budget-and-post-routing-repair--september-22),
selected by [this receipt](../../physical/experiments/clock-sram-results.json).
The prior 203 clock fanout failures are bound to actual leaf nets; each can
include one dummy load. The candidate therefore requests explicit clusters of
seven registers and enables post-routing design/timing repair, retaining the
same mapping, macros, corridor and 20 ns timing boundary. Antenna repair stays
outside this isolated experiment.

- `clock-sram-01` completes through `31-openroad-stamidpnr-3` in 392.249 s summed
  step runtime within the 600 s cap, using four CPUs and 6 GiB. The exact flow
  and diagnostic containers are independently confirmed absent. Detailed routing
  is not run.
- Clock fanout violations fall 203→4; the four remaining upper branches each
  drive 16 buffers. Before post-route repair, fresh coarse-route hold screening
  already passes, worst +0.071698 ns. Area rises 9,924.7680 µm² to 483,444.7136
  µm², leaving a 0.472148% advantage over the original physical baseline.
- Post-route design/timing repair spends 284.023 s but produces byte-identical
  exported Verilog and identical cell placements/connections. The saved NL
  views before and after both repair steps have SHA-256
  `07d4127c1b82d5f1d4a314069b3106d81736938dbe332f8c41f1fe05161c6a24`.
  Global rerouting changes overflow 1,319→1,320 and the wire estimates; it does
  not implement the intended cell-level repair. The repair counter alone would
  have overstated progress.
- Final fresh slow setup is +2.39656 ns; the smallest hold slack is +0.021291 ns
  in the mixed −40 °C-cell/−55 °C-SRAM screen. Four fanout, 52 slow slew and nine
  capacitance violations remain. Seven capacitance failures are SRAM outputs,
  including nets with only one or two sinks. No extracted timing is claimed.
- The shared `check-mapped-physical.py` replaces copied measurement wrappers for
  future work. It verifies a completed checkpoint and measures fresh corners
  with propagated clocks and explicit RC mode. Three new tests reject changed
  final states/databases, incomplete checkpoints and missing/ambiguous timing
  modes. The final annotation audit accounts for eight unused ports and 184
  unconnected dummy outputs, with no consumed unannotated nets or partials.
- The final ODB export passes 508,252 independent pin edges and rejects public
  output corruption. Sixty focused tests and 334 retained hash checks pass;
  all 267 Lean sources and all 49 preceding experiment manifests are unchanged.
  Validation: `build/validation/clock-sram-01/report.json`, SHA-256
  `971b80dbd28e3458ebe1f8aae064f771acc677066d2376095584deab9a1342a0`.

Retain the explicit clock-budget policy as a comparison, and reject repetition
of the unchanged generic post-route repair. The next inexpensive discriminator
is an effective local repair of the four upper branches and SRAM driver/load
interfaces, with actual changed implementation and functional preservation
checked before another full routing pass. No source execution contract, backend
default, license, heartbeat, commit or publication changes.


## 2026-09-22 — Local clock repair and optimizer RC initialization

The approved local investigation finds two distinct causes of the ineffective
repair. Ordinary OpenROAD repair excludes clock nets. The SRAM repair tree
sees zero per-layer wire RC while timing sees 0.100344 pF wire capacitance on
the worst output. Explicit initialization from the same PDK preserves the
reported load and produces a real inserted buffer on that same net.

The selected recipe repairs all seven SRAM outputs and copies four upper clock
buffers at their existing tree level. It adds eleven buffers, 208.656 µm²,
while preserving every original cell, parameter and placement. New cells are
legalized, the corridor remains clear, and new power pins connect to VPWR/VGND.
Fresh matched placement-RC fanout is 4→0, capacitance 0→0, and all three
setup/hold screens pass. Smallest hold is +0.087491 ns; slow setup +5.829120 ns.
Five slow SRAM address-input slew failures persist. Routed SRAM load remains
unmeasured for this candidate; the prior 1,320 overflow is not a new result.

The local recipe takes 40.023 s and independent fresh measurement 31.626 s.
Per-container bounds are 120 s, two CPUs and 2 GiB, with no network or source/PDK
writes. All exact containers are independently absent. The final pin oracle
passes 508,252 edges and rejects compiled public-output corruption in 114.663 s.
Twelve focused tests pass, including buffer contraction with wrong clocks,
addresses, parameters, cycles, shorts and missing drivers as negative cases.

Receipts:

- `physical/experiments/local-repair-results.json` selects the completed result;
  `physical/experiments/local-clock-sram-repair.tcl` retains the exact recipe.
- `build/physical/local-repair/inspect-03/report.json` records eligibility;
  `direct-global-01` and `rc-initialized-01` isolate the RC initialization effect.
- `build/physical/local-repair/targeted-03/report.json` records the legal local
  repair; `local-measure-03/report.json` binds fresh geometry, independent
  read-back, buffer contraction and matched corner measurements.
- `build/physical/chip-check/local-repair-oracle-01/report.json` binds the
  independent trace to a fresh export with the same final candidate netlist hash.
- `build/validation/local-repair-01/report.json` checks 505 artifacts, all 267
  unchanged Lean sources and 50 preceding experiment manifests. SHA-256:
  `0b2891234e4cafe1ef0af856caec918154a69fb34224fa960f609aae7b98e98d`.

The earlier failed probes remain preserved: command-adapter discovery,
generated buffer naming, legalization eligibility, and omitted CTS dummy
outputs were resolved before selecting the completed candidate. None is
reported as a physical improvement. No full global-routing run, detailed
routing, extraction, source execution-contract change or backend promotion
occurred. The next discriminator is one capped coarse-routing comparison of
the frozen repaired checkpoint with explicit layer RC and the existing CTS.

## 2026-09-22 — Frozen local repair survives coarse routing

Admitted the selected repaired ODB to exactly one GlobalRouting step, retaining
CTS and every cell placement. `local-route-01` completed in 45.112 s under a
600 s/four-CPU/6 GiB cap. Explicit nominal layer RC is verified independently
against the technology LEF for five layers in all three fresh timing screens.
No post-route repair or detailed route ran.

Fanout violations fall 4→0 and capacitance 9→1 in every screen. All seven
repaired SRAM outputs satisfy 0.064 pF; the prior worst is now 0.053038 pF.
Minimum hold improves +0.021291→+0.093542 ns, while slow setup falls
+2.396560→+2.021800 ns and slow slew rises 52→58. Those slew failures share 28
nets; 12 address, four enable and 18 upload-data SRAM pins are affected, along
with 24 standard-cell pins. One `buf_1` output, `_09593_/X`, remains at
0.308889 pF against 0.300000 pF. Overflow changes only 1,320→1,302.

The completed route exports the exact previously tested netlist
`503fea96988af21fa23681007affb6c3c5a74ad24846f875120eaf8505efa03b`.
All 18,665 instance geometries and connections remain; area is unchanged at
483,653.3696 µm² and the corridor is clear. The previous 508,252-edge pin trace
and corruption rejection are reused by byte identity and unchanged model/vector
inputs, without another simulation. Forty-three focused tests pass.

The final diagnostic receipt is
`build/physical/mapped-diagnostics/local-route-final-02/report.json` (14.408 s).
The initial 14.571 s receipt is preserved; a literal report-label quoting fix
was followed by identical fresh metrics. All exact containers are absent.
The final `build/validation/local-route-01/report.json` checks 182 artifacts,
267 unchanged Lean sources, 52 preceding experiment files and 17 earlier local
receipts. SHA-256:
`889c23b38c495ab763256a2431451d2b3b8c73ed611c9b09669c8185867471db`.
`physical/experiments/local-route-results.json` selects this result.

Retain the repaired candidate for a bounded local data-driver repair with
initialized RC and frozen clocks, preserving setup/hold and connectivity.
Congestion and slew remain obstacles to detailed routing. Antenna closure,
extraction, timing signoff and backend promotion remain open.


## 2026-09-22 — Data buffering survives a complete coarse-wire check

The bounded follow-up to `local-route-01` adds 43 buffers on 29 named driver
nets, preserving all original cells, placement, hold-delay cells, 670 clock
nets and untargeted signal connections. The successful local probe takes
36.866 s. Its area cost is 769.3056 µm² (0.16%); total instance area is
484,422.6752 µm². Independent buffer-contracted readback and the 508,252-edge
pin oracle pass, with one compiled output corruption rejected.

The first local timing report appeared clean, but had 524 partially unannotated
candidate drivers per corner. A fresh placement-only initialization also leaves
513 partial annotations on the unchanged control and 524 on the candidate.
Those timing results are unqualified, and both receipts are preserved. Their
independent structural checks remain useful. The evidence does not establish
why the placement estimator leaves these mostly SRAM-connected nets partial.

One schema-2 diagnostic admission then starts only GlobalRouting, requiring the
functional/geometry evidence and explicitly withholding timing qualification.
`local-slew-route-01` finishes in 42.652 s within a 600 s/four-CPU/6 GiB cap.
Fresh diagnostics take 14.466 s and verify complete coarse-wire annotations and
nominal per-layer RC. Every exact container is independently absent.

Slow setup improves +2.021800→+5.339320 ns, while slow slew falls 58→22: 57
previous failures clear and 21 newly reported pins fail. Eleven of twelve SRAM
address inputs and all four enable inputs now pass. The weak `_09593_/X` load
clears, and the seven earlier SRAM output repairs remain within their limits.
All setup/hold/fanout counts remain zero, but minimum hold decreases to
+0.060261 ns. Other SRAM outputs, `storage0/A_DOUT[36]` and `[50]`, now exceed
their load limits in at least one screen. Capacitance counts are 2/1/2 across
typical/slow/fast; overflow moves 1,302→1,310. This improves the electrical
candidate without establishing congestion or timing closure.

The routed export and full cell/connectivity/placement context match the tested
local candidate exactly, so its pin oracle is reused without a second
simulation. Fifty-five focused tests pass. Closeout checks 531 artifacts,
267 unchanged Lean sources, 53 prior experiment files and 22 prior receipts.

The next investigation has ten named electrical groups: eight remaining
slow-slew driver nets and two SRAM output loads. Hold-delay cells and clock
topology remain part of the preservation contract. Require complete annotations
before using timing, and audit all nets for new failures after rerouting.
Congestion remains a separate evidence gate before detailed routing.

Receipts:

- `physical/experiments/local-slew-results.json` selects the diagnostic result;
  `local-data-buffer-repair.tcl` preserves its exact recipe.
- `build/physical/repair-probes/slew-buffer-03/report.json` records the selected
  local repair; the two earlier failed attempts remain separate.
- `build/physical/repair-validation/slew-local-01/report.json` records independent
  geometry/connectivity and the initial, subsequently rejected timing estimate.
  `slew-local-02/report.json` fails the placement-only annotation gate.
- `build/physical/chip-check/local-slew-oracle-01/report.json` binds the functional
  export, models and vectors.
- `build/physical/local-slew-route-01-invocation.json`, its standard report and
  `build/physical/mapped-diagnostics/local-slew-route-final-01/report.json` bind
  the completed coarse route and fresh diagnostics.
- `build/validation/local-slew-01/analysis.json` maps every remaining pin to its
  driver. `report.json` has SHA-256
  `4347577cdbdb821a05ee59cd92b5587881107ddc86b9a4ce01b930520c40ab8b`.

No detailed routing, antenna stage, extraction or backend promotion is claimed.


## 2026-09-22 — Bound the electrical investigation and localize SRAM congestion

The step-back decision was to classify the ten remaining electrical groups,
allow at most one justified local repair, and stop with an architectural
decision rather than continue a repair loop. Fresh read-only diagnostics
(17.484 s) reproduce `local-slew-route-01`'s complete coarse-wire timing and
export exactly, adding all 128 SRAM output loads and selected driver inputs.

All ten drivers have two or four sinks; 82–97% of slow load is wire capacitance.
Three long logic connections, four upload hold-delay outputs, one SRAM address
branch and two SRAM outputs therefore admit a buffer-isolation hypothesis.
The one 120 s/two-CPU/2 GiB probe fails after 17.801 s with `GRT-0183`: heap
underflow during 3D maze routing on `net6399`. It saves no changed netlist or
repaired ODB. The last progress count of seven buffers/four nets is unvalidated;
source hashes and the pre-edit netlist are unchanged. No candidate is adopted,
and the prepared structural/oracle follow-ups and standalone route do not run.
This is a tool failure, not a timeout or physical infeasibility result.

A 0.641 s read-only OpenDB query gives a more useful next boundary. The prior
and current 179×98 GCell grids have identical coordinates and capacities.
Every recorded overflowing cell lies in the lower SRAM strip. About 90% of
recorded overflow is in cells centered inside the SRAM footprints, mostly
SRAM0; about 2% is in the reserved corridor. Saved-grid sums 1,298/1,309 differ
from flow totals 1,302/1,310 by four/one units, so both measures remain explicit.
Guide/body overlaps also include non-SRAM-connected traffic. Neither bounding-
box membership nor guide overlap is an exact detailed-track or DRC test.

Retain the validated 43-buffer chip and its storage/fetch contract. The next
investigation should bind real SRAM pin shapes, obstructions, power routing
and capacity, distinguishing upload, address, return and unrelated transit
traffic. Any proposed physical region must include all incident connections;
the rejected earlier address-only projection and unchanged-capacity screen
remain rejected. Require a measurable geometry/capacity change and preserved
pin access before another physical run. The tool error does not justify
switching storage organization or relaxing the execution contract.

`physical/experiments/electrical-cost-results.json` records the decision.
`build/validation/electrical-cost-01/` contains classification, saved grids,
congestion accounting, guide reports and the failed-probe disposition.
`report.json` has SHA-256
`9ff604cb4fa1e97c343a745fc0fd22d72c03351e2c38fe31f18a052c68612f40`.
Closeout verifies 120 artifacts, preserves 531 preceding artifacts, 267 Lean
sources, 55 prior experiment files and 13 prior receipts, and independently
confirms all seven exact containers absent. No standalone routing run or new
functional simulation is claimed.

## 2026-09-22 — SRAM interface geometry and a bounded upload-stage prototype

Completed the approved interface study and considered pipelining by adding an
opt-in stage to upload, whose physical write can wait while execution reads
retain priority. The 43-buffer `local-slew-route-01` remains the physical control.
No new placement, routing, clock/hold repair or backend promotion was performed.

The 2.586 s read-only extraction binds 58,781 terminal geometries, tracks,
macro obstructions and 30,592 power-via metal rectangles to the retained ODB.
Both macros expose south-facing Metal2 pins; Metal2/3 footprint obstruction
fractions are 99.74%/100%. Metal4 union with power geometry is 50.75%/50.66%.
After following known buffers/delays, upload accounts for 92/171 Metal4 nets
whose guides overlap a macro and 44/64 whose guides overlap its inset interior.
These are guide/geometry screens, not DRC attribution. All 684 nominal escape
rays clear south; the width-fit grid screen is not a legal-access proof.
Fixed-neighbor mirror projections worsen all-incident span by 42.23%, 81.82%
and 72.52%, so none earns a placement run.

The pinned OpenROAD exporter adds capacity reductions to both saved capacity
and saved usage. This corrects the earlier inference that equal saved capacity
alone establishes unchanged obstruction effects. Earlier receipts remain intact;
their unchanged guides and lack of improvement still do not justify long routing.
Saved overflow 1,309 and flow overflow 1,310 remain distinct measurements.

`Storage.UploadPipeline` adds valid/address/data registers totaling 71 bits.
The checked queue invariant, memory view and emitted write-priority expression
preserve pending writes across busy/start edges; full chip refinement remains
open. `upload-pipeline-01` passed 13,947 core edges and 508,252 pin edges, but
failed its negative gate because the test hid an unconditional-write error.
`upload-pipeline-02` shortened the pulse but still hid the error in old halt
contents; its incomplete receipt says `running`, although both commands exited
and the expected rejection failed. Preserve that receipt as a failed attempt.
The final `upload-pipeline-03` fixture preloads a distinguishable opposite bank:
14,200 core edges pass and the faulty wrapper is rejected at edge 12,494.

`build/validation/sram-interface-01/final-validation/` then rebuilds the complete
library, audits 14,932 declarations / 7,573 theorems, checks `Interfaces` and ten
geometry controls, and re-emits byte-identical core/chip RTL. It reruns the
14,200-edge core fixture and rejects the stronger mutant that bypasses the
shared grant, including its address/read users. The pin trace is reused only
with exact RTL/model/oracle/tool identity. This final gate takes 16.878 s.

The matched typical-library synthesis comparison takes 11.153 s and changes
393,558.3170→401,138.8046 µm², 2,895→2,966 FFs and 15,492→15,994 cells.
The 1.926141% overhead compares the shared reference hybrid and upload-stage
variant; it does not compare against the separately optimized physical chip.
Keep the stage opt-in. Next cost a concrete local upload-distribution placement
including source wires, both replicas, clock, hold, ties and return/address
traffic before admitting further physical work. The durable
[manifest](../../physical/experiments/sram-interface-results.json) binds all
reports and the preceding studies' preserved artifacts.

## 2026-09-22 — Reject upload-stage insertion using directed ownership and free space

Completed the approved placement-cost discriminator without a physical run.
`scripts/upload_locality.py` binds the prior interface receipt, frozen geometry,
guides and exact mapped stage. Directed traversal verifies 64 distinct FF source
bits and matching replicas. The 580-net word family has 172 shared, 30 SRAM-only
and 378 other-consumer nets. Among its 44 Metal4 interior crossings, 41 are shared
and three SRAM-only. Of 128 hold-delay cells, 106 are shared; only 22 plus eight
buffers are exclusive candidates for release (480.8160 µm²).

The exact mapping has 62 ordinary data FF/mux pairs and two data FFs using other
logic, plus seven address/valid FFs. Fixed-neighbor gaps below the two macros
fit 25/10 pairs, or 27/10 after optimistic exclusive-branch removal. An idealized
projection ignoring occupied cells suggests −9.60% span on 96 affected nets,
only −1.94% over the complete word family. That apparent gain does not establish
a feasible layout.

A separate relaxation allows muxes elsewhere and assigns only the 64 data FFs
to free-interval capacity. Individual bands admit at most 44/22 FFs. Across both,
66 slots suffice, but the optimal affected-net span becomes
17,316.2725→26,064.8275 µm (+50.52%; +10.22% over the complete word family).
Multiple centers can overlap within an interval and other costs are zero, so
this is a lower bound for the stated point/row model, not a legalized placement
or physical-wire theorem. The assignment has a matching dual certificate and
agrees with brute force on 48 small cases.

The 71 new clock pins add 0.19665296 pF typical / 0.18365925 pF slow before
wires and buffers. Bare FFs cost 3,478.2048 µm² and the 62 ordinary payload
muxes 1,124.9280 µm²; other logic and clock/hold repair remain additional.
The earlier 1.926141% matched whole-synthesis overhead remains a separate result.

The first helper attempt rejected power-net package ports after collecting
removed-cell supply connections into a data-only projection. Signal/power
separation was corrected and tested; the failed log and source copy remain.
The preliminary successful analysis used 64 logical pairs; the final version
binds the actual 62 mapped mux pairs. Final analysis takes 0.797 s, relaxed
allocation 0.196 s, and all 13 focused tests pass. No Lean, RTL, mapped netlist,
placement, routing or earlier receipt was changed.

Reject these insertion configurations and retain the 43-buffer physical chip.
The next candidate should own the existing received-word registers and their
immediate decoding/validation/distribution region, with every shared consumer
and displaced cell included. The
[locality manifest](../../physical/experiments/upload-locality-results.json)
binds the finished reports, assumptions and preservation checks.

## 2026-09-22 — Bind the received-frame region and reject unrelated locality gains

Completed the approved receiver/decoder/distribution cost study. A fresh native
Yosys readback took 0.730 s. The helper reconciles 18,708 physical instances and
18,669 nonempty, non-power nets and binds all 2,895 FFs through the retained
typed reference and tiled state projections. Eight empty ODB aliases are
explicitly excluded. The initial helper rejected an empty alias; a regression
test distinguishes that case from missing, split or merged live connections.

The receiver plus pure-input decode/distribution, complete receiver feedback and
private ties contains 871 cells / 11,826.2592 µm², including 149 hold-delay cells.
There are 421 outgoing and 25 incoming boundary nets. Mixed-state logic remains
outside; all downstream register/macro/package consumers are counted.

The full bit census corrects an initial impression from inspecting low bits:
53 received-word FFs are below SRAM0, three below SRAM1, two beside the right
macro edges and six above. Bits 0–4 supply the map payload and account for
61,868.4725 µm (72.3%) of word-family span, but none of its 44 Metal4
interior-overlap nets. Those 44 belong to 34 bits in the 6–63 field; all 41
shared ones also reach receiver feedback/control and 25 additionally reach
pure frame decode/control. This classifies existing guide traffic, not DRC.

Three bounded fixed-site exchange searches at 20/40/80 µm preserve identical
occupied footprints/orientations and all 670 clock-net pin-coordinate multisets.
They make 14/18/19 exchanges and move 4/6/7 cells outside the chosen region.
All connections of these displaced neighbors count. Affected-net span falls
71.1700/175.7425/221.2775 µm, only 0.0681/0.1667/0.2085% over the complete region
plus displaced nets. The ten diagnosed electrical nets have no moved terminals.
There are 13/15/16 shortened arcs on nets touching existing hold cells, up to
15.72/36.48/60.00 µm. These geometric changes imply no measured slack benefit.

Reject all three candidates. The final native analysis takes 1.587 s (1.734 s
command wall time); 14 focused tests pass, and an independent 1.194 s audit sums every
live net in the chip and checks footprints, clocks, diagnosed pins and all
previous receipt hashes. No physical tool, functional simulation, new RTL,
clocked stage or candidate ODB was produced. A final replay after adding an
explicit IHP-unit guard and clamping the reported largest shortening at zero
when every arc grows reproduces all earlier case results. Both versions and
their audits remain available.

The next explicit boundary is `net3533`, the bit-41 branch driven by
`hold3533/X` and used only by the two SRAM `A_DIN[41]` pins. Cost a concrete
drive/buffering change there while preserving the hold chain and other
source-side consumers. It targets a measured slew group and requires no new
clocked state. The prior broad electrical probe's incremental-router failure
did not settle this narrower hypothesis. The
[word-region manifest](../../physical/experiments/word-region-results.json)
binds this study; the 43-buffer chip remains the physical control.

## 2026-09-22 — Bounded compact execution decision

Completed the approved [PIO/PRU-inspired comparison](../storage/compact-execution-study.md)
against one concrete paired-successor machine. One 64×64 single-port SRAM holds
two atomic 32-row images; each row contains two 32-bit possible successors.
The selected old response supplies the next row address before the edge, so
consecutive one-cycle branches do not require an extra fetch edge.

`build/validation/compact-execution-01/report.json` records 18 tests, two explicit
Lean schedule lemmas (with a compiler/image premise), four behavioral mutants
and an injected-axiom rejection, completing in 8.881 seconds. UART covers all
256 payloads on one image; SPI covers 256 distinct TX/RX pairs with independent
edge/capture expectations; branching covers 4,096 six-sample histories plus
128 consecutive edges. Wait timeouts, reset, program replacement and retained
result ownership are also checked at delivered-command boundaries.

A stale-row mutant initially escaped the UART test because four-edge holds
allowed the memory request to recover. The final negative control exposes it
on the second consecutive branch. Raw serial framing, package composition and
Python/Lean correspondence remain outside this model gate.

Reject the candidate as an equivalent replacement: a currently admitted
32-action/8,192-edge sequence needs 33 paired rows including boot, exceeding
the 32-row bank. Qualifying waits, general checked guards and independent
entry/terminal/branch slots also lack encodings. Its 250 declared register bits
include retained wrapper budgets but are not a mapped area result. All 205
library sources and three prior receipt files remain unchanged during the gate.
No hardware, synthesis or physical experiment was produced.

Retain the current engine and 43-buffer physical control. Resume the bit-41
SRAM-only buffering cost gate, with paired-successor scheduling preserved as a
research result. Resident payload remains a separate proposal under its existing
encoding/proof/physical-budget gate. The
[compact-model manifest](../../physical/experiments/compact-execution-results.json)
binds the decision and exact counterexamples.


## 2026-09-22 — Reopened paired execution with full capacity and measured lookup cost

The user challenged abandoning the organization after one encoding failed.
Completed one [full-capacity revision](../storage/compact-execution-study.md#full-capacity-follow-up):
one 512×64 single-port SRAM, two 256-row atomic images, two 32×20-bit FF parameter
tables and two boot tokens. The parameter projection restores canonical E64
operations and the 256-position/32-record capacity without assuming recovered
loops or compressible traces. Total declared state is 1,592 bits including
retained wrapper budgets, compared with 2,901 for the current chip. The table
has two read ports because upload validation reads both successor parameters.

`build/validation/paired-execution-03/report.json` records 18 focused model tests,
six detected behavioral mutants, two conditional Lean schedule lemmas with an
axiom negative control, and all six compiled protocol fixtures. Independent
peers exercise 24 I²C cases / 10,349 execution edges and nine UART receive frames.
The former 8,192-edge counterexample and full 256-position images pass. Resident
UART/SPI reuse one image across 256 payload or TX/RX cases. No universal compiler,
loader, package-wrapper or full emitted-chip theorem is asserted.

A matched standalone two-bank/two-read/one-write FF-table comparison maps the
256×5 index organization to 252,384.1740 µm² and the 32×20 parameter organization
to 111,557.0988 µm² at either corner. The 140,827.0752 µm² table saving exceeds
the larger SRAM's 49,124.1376 µm² premium by 91,702.9376 µm². Those are component
costs, not a new whole-chip area. Slow-corner read arrivals are 6.77 versus 6.17 ns,
both including the same 4 ns input delay. Parameter-table standalone setup/hold
slacks are +9.63/+0.27 ns, but 569 fanout-limit violations remain. No macro arcs,
entry logic or wire parasitics are included in that timing result.

Four independent arbitrary-state SAT checks validate saved mapped outputs and
every next-state bit. The initial joined-reader injection changed only a JSON
port; named-wire intake reconstructed the original connection, so its gate
correctly refused to pass. Updating both the port and matching netname exposes
the fault. The focused correction and final rerun retain the earlier receipts.
Attempt 01 stopped at sandbox Docker access before CAD; attempt 02 stopped at
that ineffective mutation. Attempt 03 passes in 122.269 s, with no subprocess
exceeding 43.083 s. Four network-disabled, read-only timing containers were
independently confirmed absent. All 205 library sources remain unchanged;
239 source and 70 artifact hashes match, as do nine pinned macro views.

**Decision:** continue the paired organization. Next emit and independently
check the complete revised controller, include validation and the existing local
electrical load policy, and time the actual larger-macro row/entry paths. Only
that composed result can admit placement. Preserve the 43-buffer chip and the
bit-41 repair as control/fallback; do not resume the local repair solely because
the first compact encoding failed. No production chip source or detailed route
was changed. The [follow-up manifest](../../physical/experiments/paired-execution-results.json)
binds report SHA-256 `c6c2087046223e30786f9eafbcb2c325a5e33681a8ca0cb5b4e936a32f2e7d4e`.

## 2026-09-22 — Complete paired controller, exact mapped replay and macro timing

Completed the [full-controller gate](../storage/compact-execution-study.md#complete-controller-and-macro-timing)
in `build/validation/paired-controller-02/report.json`. The opt-in
`PairedController.lean` emits both banks, two parameter reads, atomic admission,
boot/current/cached state, counters, captures and resident payload through the
existing netlist machinery. Existing sampler, serial, pin-map and mailbox
composition is reused. A separate wrapper binds one actual 512×64 SRAM; all
205 preceding library sources and the default chip remain unchanged.

Emission initially exceeded its 120-second cap while traversing shared
expression trees. The process group stopped before RTL/CAD. Forty-five explicit
combinational wire bindings remove that repeated traversal without adding state
or cycles; emission then takes 2.637 seconds. The first complete gate stopped
at strict state intake because Yosys represented six unused reserved token bits
as literal `x`. Intake now permits only those exact unconnected coordinates
for census, rejects live unknowns and preserves every functional connection.
Both earlier receipts remain intact. Eight focused intake tests and four invalid
graph controls pass in `paired-intake-01`, taking 3.159 seconds.

The emitted core passes 173,359 edges, including 116,811 independent E64 state
comparisons, 4,096 consecutive-branch histories, full-capacity execution, all
256 resident UART payloads/SPI pairs, independent I²C/RX peers and interrupted
atomic uploads. The complete serial/sampler/mailbox package passes 331,401 pin
edges / 1,517 serial frames; all pin edges repeat on the typical mapped chip.
Both saved mapped corners pass arbitrary-state output/next-state SAT, with
macro responses exposed as independent inputs and every physical FF accounted
for. The stale SRAM-row mutant fails at edge 296; an inverted mapped buffer and
an injected axiom also fail. The namespace audit checks 463 declarations.
This is not a complete Lean refinement of the compiler or package.

The whole-chip typical/slow areas are **302,239.2384 / 302,246.4960 µm²**, including
**150,102.4032 µm²** of SRAM. This is **22.8829% / 22.8810%** below the exact
optimized `local-load-01` mapping under the same eight-load policy. There are
1,572 physical FFs from 1,592 declared bits; 20 unused coordinates are recorded.
All signal fanout, slew, capacitance, pulse-width and period checks pass at
both corners. The final distribution adds three buffers beyond ABC's repair.

Actual macro arcs are included under the retained 20 ns ideal-clock constraints.
Typical/slow setup is **+8.53 / +3.93 ns** and hold **−0.61 / −0.90 ns**. The
slow limiting setup path goes from SRAM `A_DOUT[53]` through parameter/admission
logic to rejection status `uo_out[4]` (11.87 ns arrival, 15.80 ns required).
Execution row/entry paths have **+8.04 / +8.81 ns** slow slack. The worst hold
path is serial shift FF → SRAM `A_DIN`: 0.33 ns arrival versus 1.23 ns required.
The reference's slow setup/hold is +10.52/−0.86 ns, so the area saving comes
with reduced setup headroom. Wires and clock distribution are excluded.

The main gate passes in **63.291 seconds**; 262 input and 78 artifact hashes
were independently rechecked. The previous paired receipt's 309 bound files
also match. The retained reference timing artifacts match their receipt and
the exact netlists used for the area comparison. Both bounded timing containers
were independently confirmed absent. The
[manifest](../../physical/experiments/paired-controller-results.json) binds report
SHA-256 `9e2d550a924006e332efb4be15c93c883d7f9f0e6b10965278dd5d9e53e4be0f`.

**Decision:** proceed to exact one-macro physical intake and a bounded
placement/clock/hold comparison, measuring the larger obstruction and total
repaired area at the same stage as the control. No placement, detailed route,
extracted timing or backend promotion occurred in this gate. Preserve the
43-buffer physical control, bit-41 fallback and experimental upload pipeline.

## 2026-09-22 — Shared physical targets and matched paired placement

The [physical-target handoff](../physical-targets.md) now binds validated mappings,
pinned macro views/power/placement, every typed state owner and four semantic
path roles. The old control and new paired controller have small source adapters
and share the existing preparation, runner, readback and reporting flow. Both
floorplan imports preserve every signal connection. Actual paired macro/PDN
intake confirms the 512×64 footprint, power-net binding and reserved clear band
before standard-cell placement. Power continuity and routed access remain open.

The saved-netlist power-port difference first stopped strict readback. A fresh
receipt projects only explicitly declared isolated rail ports after OpenDB
power checks; no signal identity is relaxed. A first approximately 26-second
placement used the platform's fanout limit ten. The matched repeat uses the
control's eight-load setting, with the same 600-second/four-CPU/6-GiB cap, and
again finishes in about 26 seconds. Both attempts remain preserved.

Fresh measurements compare `target-paired-place-02` at
`17-openroad-stamidpnr-2` with the reused control `mapped-local-place-01` at
`25-openroad-stamidpnr-2`. Both are post-CTS/hold-repair checkpoints; all common
resolved constraints agree. Area is **348,205.8528 versus 473,519.9456 µm²**,
a **125,314.0928 µm² / 26.464375%** saving including SRAM and physical repair.
Hold buffers fall from 2,986 to 1,678; clock buffers/dummy loads from 427 to 242.

Paired slow setup is **+0.304933 ns**, on SRAM `A_DOUT[51]` through shared
parameter/admission logic to rejection status. Slow next-address/entry slacks
are +3.790690/+6.185663 ns. Slow hold is +0.405227 ns; the fast screen has
+0.095552 ns hold. The control's corresponding overall slow setup is +6.096080
ns and fast hold +0.099694 ns. The control has no SRAM-to-status combinational
path. Its first collection rejected that absence; the final collector requires
STA to agree with reachability derived from the exact mapping, including absence.

All candidate signal electrical checks pass. Its **113 fanout violations are
clock nets**, versus 203 in this control stage. The control has five slow slew
violations; the candidate has none. Independent annotation reconciliation finds
182 control/94 candidate unused drivers, zero consumed unannotated nets and zero
partially unannotated drivers in every corner. These are qualified placement
wire estimates with propagated clocks, not global-route or extracted timing.
The fast screen still mixes −40 °C cells and −55 °C SRAM.

The actual paired export passes **331,401 pin edges** and rejects a compiled
public-output corruption. Final export identity reuses this result and the
control's previous **508,252-edge** trace without another simulation. Vectors,
bench and models match their original receipts. Sixty-nine focused tests pass;
five mutations against the actual paired OpenDB reject wrong state ownership,
missing paths, wrong power, changed macro location and an occupied corridor.
All 27 exact containers are independently confirmed absent. The preceding
paired controller's 262 source/78 artifact hashes and model's 239 source/70
artifact hashes still match; no Lean or RTL source changed.

`build/validation/physical-target-01/report.json` has SHA-256
`4d0c0a9189de5ee32ec1b78d8491daf781d977ac29498fb3e83201f96063c0bc`.
The [manifest](../../physical/experiments/physical-target-results.json) records
both matched measurements, functional reuse, prior attempts and resource caps.

**Decision:** retain the paired candidate, then diagnose its clock leaf loads
and narrow rejection-status setup margin using these saved checkpoints. Preserve
pin timing and remeasure any repair before admitting a bounded coarse route.
Detailed routing, antenna closure, extracted timing, final power qualification
and default upload-format promotion remain gated. The 43-buffer chip and
bit-41 fallback remain available.

## 2026-09-22 — Paired clock fanout and complete status-cone repair

The paired placement's 113 fanout failures were clock leaf drivers carrying
10–17 loads against the eight-load limit. `paired-clock-01` resumes the verified
macro/PDN checkpoint with seven-sink CTS clustering and stops after post-CTS
hold repair. Clustering is the only resolved flow change after path
normalization. All fanout failures disappear. Area rises from 348,205.8528 to
352,863.4176 µm², while slow setup barely changes from +0.304933 to +0.303624 ns.
Fast-screen hold improves from +0.095552 to +0.099842 ns. The run is capped at
600 seconds, four CPUs and 6 GiB; no routing step runs.

The first data repair strengthens `_05626_`, `_05822_` and `_05886_`, three small
buffers on the limiting SRAM-to-rejection path. Explicit nominal layer RC is
initialized from the pinned LEF for the local optimizer. Applying that same
initialization in fresh independent placement STA leaves 308 partially
unannotated drivers on both the unchanged clock control and three-cell repair.
Those `paired-status-control-01` and `paired-status-candidate-01` measurements
remain unqualified. The collector now records optimizer and measurement RC
separately; the repeated probe and `paired-status-candidate-02` measurement use
the original flow configuration for independent STA and recover complete
consumed-net estimates. The three-cell repair gains only **0.008933 ns**, with
the worst path moving to another branch. Earlier receipts remain untouched.

The selected bounded follow-up sizes the full SRAM-output-to-`uo_out[4]`
combinational distribution cone: 128 `buf_1` and 40 `buf_2` cells become
`buf_4`. Sequential and macro boundaries stop the selection. All other
instances remain fixed during legalization; every net terminal and macro pin
geometry stays identical. `paired-status-cone-01` takes about three seconds
under the 120-second, two-CPU, 2 GiB repair cap. Fresh independent collection
takes about eleven seconds using the retained flow configuration.

Final slow setup is **+1.089368 ns**, on SRAM `A_DOUT[20]` to rejection status;
slow next-address/entry slacks are **+4.680503/+7.196474 ns**. Slow hold is
**+0.418639 ns** and fast-screen hold **+0.099842 ns**, unchanged by the data
repair. Fanout, slew and capacitance checks pass in all three measured corners
with zero partially unannotated drivers and zero consumed unannotated nets.
Final instance area is **354,010.1184 µm²**: the cone repair costs 0.324970%
over clock repair; both changes cost 1.666906% over initial paired placement.
The candidate remains **25.238605% smaller** than the old control at the same
post-CTS stage. These are propagated-clock placement estimates, including the
existing mixed-temperature fast screen, not routed or extracted timing.

The clock-repaired chip passes **331,401 independent package pin edges** and
rejects a compiled output corruption. Fresh Yosys readbacks and explicit
noninverting-buffer contraction establish identical connectivity after exactly
168 permitted buffer resizes; real-netlist inverter and rewired-input controls
fail. This transfers the same zero-delay trace evidence without repeating the
final simulation. The shared physical checker resolves all 1,572 FF owners and
four timing roles, confirms macro/power geometry and the empty corridor.
**71 focused tests** pass. All **26 exact containers** are independently absent.
The preceding paired controller's 262 source/78 artifact hashes and model's
239 source/70 artifact hashes are unchanged.

`build/validation/paired-closure-01/report.json` has SHA-256
`6706c3a3f2a0a1629973be204ef6038478e99754a5a2ea3e606e5af03101407f`.
The [repair manifest](../../physical/experiments/paired-closure-results.json)
binds the selected `repair-probes/paired-status-cone-01/repaired.odb`, independent
measurement, parent state, functional evidence, rejected measurements and caps.

**Decision:** retain seven-sink clustering and the complete status-cone repair.
Next capture and admit this exact repaired checkpoint for one bounded coarse
route, then remeasure access, congestion and timing/electrical/annotation checks.
Detailed routing remains unadmitted. No Lean, RTL, state, execution schedule,
package timing or pipeline cycle changed; no antenna, extracted timing,
power-continuity qualification or default backend promotion occurred.

## 2026-09-22 — Exact paired repair intake and bounded coarse routing

The shared route intake now accepts a target-based, hash-bound buffer-resize
validation through schema 3. It recomputes noninverting-buffer connectivity,
checks fixed unrelated geometry, links the original pin oracle and requires
complete positive placement measurements with passing electrical limits.
The staged state contains only the exact selected ODB and empty metrics.
The existing GlobalRouting-only bound, 600-second maximum and disabled repair
controls remain enforced. Prior experiment receipts and their executed artifacts
are preserved; `physical_route_intake.py` is intentionally extended.

`paired-route-01` admits the 168-buffer repair and runs one GlobalRouting step
under a 600-second cap, four CPUs and 6 GiB. The physical stage completes in
**36.283 seconds**. No synthesis, placement, CTS, signal/hold repair, detailed
routing or antenna repair runs. The exact container is independently absent
before standard reporting and fresh collection.

Compared with the retained 43-buffer control's `local-slew-route-01`, overflow
falls from **1,310 to 41**, a **96.870229% reduction**. Forty units remain on
Metal3 and one on Metal4. Resource/demand are 425,596/191,854, versus the
control's 452,959/147,062; reported usage rises from 32.47% to 45.08%. Overflow
is a capacity-demand count, not a detailed DRC count. Normalized configurations
differ only in netlist/defines, macro organization/power and placement
obstructions. Clock, routing layers, eight-load policy, seven-sink clustering,
30% capacity adjustment and explicit nominal RC match. The architecture and
placement changed together, so this comparison does not isolate buffer sizing.

Area remains exactly **354,010.1184 µm²**, versus the routed control's
484,422.6752 µm²: **26.92% lower**. The earlier 25.24% saving used the control's
post-CTS placement stage. Fresh independent collection takes **12.109 seconds**,
verifies nominal per-layer RC in all corners and confirms complete consumed-net
annotation. It reports **−2.493735 ns slow setup**, **−0.659543 ns fast-screen
hold**, and **−0.491156 ns slow hold**. These coarse estimates differ in RC policy
from the retained-flow placement measurement and remain separate from extraction.

The slow critical path is SRAM `A_DOUT[53]` → rejection output `uo_out[4]`.
It arrives at 18.293736 ns against 15.800000 ns required. Two loaded logic gates
are `_05608_/Y` (`nand3_1`, two sinks, 0.226882 pF, 2.200929 ns cell delay) and
`_06399_/X` (`a21o_1`, three sinks, 0.283454 pF, 1.218126 ns). Slow SRAM-to-address
and SRAM-to-entry slacks remain +0.913580/+4.982161 ns.

The worst fast hold path is `uio_in[1]` → `_12267_/D`, owned by
`r_pin_first_incoming[1]`; data arrives at 0.737588 ns against 1.397131 ns
required. The clock trunk into `clkbuf_3_2_0_clk_regs/A` contributes 0.632916 ns
wire delay while passing fanout/electrical checks. Fast hold has 36 input and
55 register-to-register failures; slow has 11 input failures. Serial-shift paths
are among the internal failures. Fast SRAM upload hold remains +0.200687 ns.
All fanout checks pass. The 316 slow slew failures cover 58 nets, and 68 slow
capacitance failures cover 68 nets; their union is 96 signal nets. Fast/typical
capacitance counts are 70/69. No electrical violation is on a clock net.

A separate **2.348-second** minimum-one-access-point probe, capped at 180 seconds,
passes with zero standard-cell pins lacking access across 32,942 checked pins,
348 valid macro planar access points and zero macro pins lacking access. The
source database stays unchanged and the probe container is absent. This does
not establish simultaneous legal routing. The guide/body screen records 67
Metal4 rectangles on 32 nets overlapping the macro footprint; this is not DRC.

The routed export is byte-identical to the placed repair. All physical context
fields except database identity are unchanged, including placement, clock
connections, macro geometry, power shapes and the clear corridor. The prior
331,401-edge pin trace and corruption rejection transfer without simulation.
All 1,572 FFs and four semantic timing roles resolve. **79 focused tests** pass;
the first combined test command used the wrong Python import path and is
preserved separately. All **six exact containers** are independently absent.
The analysis rechecks 648 hashes and 321 prior source/result identities.

`build/validation/paired-route-01/report.json` has SHA-256
`a2a08cfe904cd790b74964d3a708d1f54b95e5972f34d4cb840f5e42636b4726`.
The [route manifest](../../physical/experiments/paired-route-results.json) binds
the source selection, admission, routed database, comparison and diagnostics.

**Decision:** retain the paired architecture and its saved coarse-route result.
Next cost bounded repair of the register-clock trunk, input/serial hold paths
and loaded status-cone logic, using complete wire estimates and explicit
affected-net accounting. Recheck functional identity, setup/hold and electrical
limits before another route; the 41 overflow units also remain open. Detailed
routing is unadmitted. No Lean/RTL, pipeline cycle, package timing, host format,
licensing decision, antenna closure, extracted timing or backend promotion changed.


## 2026-09-23 — Paired local repair with fresh coarse wire estimates

Retain `paired-local-status-01` from the bounded local study. Slow setup changes
from **−2.493735 to +0.071044 ns** and fast-screen hold from **−0.659543 to
+0.072689 ns**. All measured setup, hold, fanout, slew and capacitance violations
are zero in all three corners; consumed-net annotation is complete and nominal
layer RC is independently verified. Slow/typical hold are +0.360733/+0.176697 ns.
The fast screen still mixes −40 C standard cells with −55 C SRAM.

Four clock repeaters alone reduce fast hold failures from 91 to 12 without
changing status setup. Buffering the measured signal loads then clears
capacitance, while exposing short-path hold failures. The selected combination
adds four clock repeaters, 111 signal-driver buffers, 126 endpoint delay buffers
and one SRAM receiver buffer. The final two status drivers are selected from a
bounded 100-path near-critical audit. All 242 cells are noninverting buffers;
no original cell moves or changes type, and no state or pipeline cycle is added.
Area is **357,660.6912 µm²**, a **1.031206% increase** from the paired routed
baseline and **26.167640% below** the retained routed control.

Each candidate is legalized with the original placement frozen, incrementally
coarse-routed, independently exported and remeasured in three corners. The
successful repair recipes take about four seconds; independent collections take
about twelve seconds each. All nine probes, including inspection/failure/audit,
total **34.193 s**; six collections total **71.313 s**. Each probe and each
collection command has a 120 s cap, two CPUs and 2 GiB.

Independent readback and buffer contraction preserve logical connectivity;
a deliberately grounded buffer input is rejected. Macro-pin geometry, the
corridor, all 1,572 FFs, four semantic path roles and added-cell power bindings
pass. The earlier 331,401-edge trace transfers through this identity check;
no new pin simulation is claimed. **25 focused tests** pass, **514 prior
identities** are preserved, and **36 exact containers** are independently absent.
The final analysis verifies **1,693 hashes**.

Preserve the failed first clock probe: the pinned resizer's DPL post-insertion
path asserts before producing a selected candidate. Direct database insertion
followed by normal legalization succeeds. Also preserve the initial overstrict
guide-byte check: 28 nets legitimately retain their coarse guide blocks after
nearby driver replacement. The corrected validator requires guide presence,
complete fresh wire annotation and independent connection identity.

`build/validation/paired-local-repair-01/report.json` has SHA-256
`3b9c6a31b3f63dd6e8ff98918b1939a186ffd1d2ff72ca181cdc60b89ad06c73`.
The [local-repair manifest](../../physical/experiments/paired-local-repair-results.json)
binds the staged results, selected ODB, exported netlist and frozen recipe.

**Decision:** retain this local candidate for one bounded whole-chip coarse
reroute, then fresh timing/electrical, congestion and pin-access checks. Bind
the added-buffer proof and changed clock topology in a distinct continuation
contract; do not reuse the resize-only selection unchanged. The roughly 71 ps
setup and 73 ps fast hold margins are narrow. The baseline's 41 overflow units
and prior pin-access pass are not measurements of this modified candidate.
Detailed routing, antenna/DRC closure, extracted timing, physical power
qualification and backend promotion remain open. No Lean/RTL, pipeline cycle,
package protocol, host format or licensing decision changed.


## 2026-09-23 — Whole-chip coarse reroute of the paired local repair

`paired-reroute-01` completes one GlobalRouting step in **58.116 seconds** under
a 600-second, four-CPU, 6 GiB cap. It starts from the exact selected
`paired-local-status-01` ODB with empty inherited metrics and automatic repair
disabled. Independent three-corner collection takes **12.353 seconds** and
verifies complete consumed-net annotation and actual nominal layer RC.

Slow setup is **+0.430335 ns**, fast-screen hold **+0.081790 ns**, and slow hold
**+0.347819 ns**. Setup, hold and fanout have zero violations in all three
corners. Typical setup/hold are +6.205010/+0.169243 ns. The local incremental
estimate had +0.071044 ns slow setup and +0.072689 ns fast hold; those timing
gains survive the full reroute. These remain coarse estimates, with the existing
−40 C cell/−55 C SRAM fast-screen mismatch, not extracted timing.

Electrical failures reappear: fast slew/capacitance **4/19**, slow **80/16**,
typical **5/19**. The union is **27 signal nets** and zero clock nets. Actual
connectivity separates 21 nets with eight loads each from six SRAM write-input
nets feeding bits 10, 15, 17, 19, 21 and 52. Four of those SRAM nets already use
`buf_8` drivers; two retain delay cells. Worst fast capacitance is 0.386423 pF
against 0.300000 pF at `_08772_/X`; worst fast input slew is 0.734179 ns against
0.380000 ns at SRAM `A_DIN[15]`. Slow slew's 80 failing pins occupy 14 nets.

Overflow falls **41 → 22 (46.34%)** relative to the pre-repair full route.
All remaining overflow is Metal3; Metal4 falls from one to zero. Coarse demand
falls 191,854 → 186,936 with the same 425,596 resource count. The router's
`GRT-0273` warning states that the nondefault rule on `clk` was disabled to
reduce congestion; the baseline has no such warning. Clock connectivity is
unchanged, but this run does not isolate the contribution of the changed wire
rule. Overflow is not a detailed-route DRC count.

The **2.360-second** pin-access probe passes, with no standard-cell pin lacking
access across 33,426 checked pins, no macro pin lacking access and 348 valid
macro planar access points. This is individual access, not simultaneous legal
routing. The guide/body screen records 68 Metal4 rectangles on 33 nets overlapping
the macro footprint; it is not DRC evidence.

The new schema-4 intake independently recomputes logical identity through 242
added buffers and the preceding 168 buffer resizes to the original 331,401-edge
pin oracle. It checks original placement, macro/corridor geometry, power bindings,
source/configuration identities and complete passing local measurements before
the bounded route. Shared PDK views and recorded tool/library aliases are admitted
only with byte checks. All 49 focused tests pass, including malformed-clock,
power/geometry, stale-input, partial-RC and scope rejection controls.

The routed export is byte-identical to the local candidate; every collected
physical context field except database path/hash is identical. This preserves
functional connectivity, all 1,572 FFs, placement and **357,660.6912 µm²** area
(**26.17% below** the retained routed control), without another pin simulation.
All **six exact containers** are independently absent. The analysis verifies
**753 hashes** and preserves **528 prior source/evidence identities**; the prior
intake helper changes only to dispatch schema 4. Early shared-input preflight
rejections and the corrected analysis warning-text check remain recorded.

`build/validation/paired-reroute-01/report.json` has SHA-256
`86abf480ddf026fe10d4163a63017fb1f68afbe5a3e4c4f64a585ede635d9065`.
The [reroute manifest](../../physical/experiments/paired-reroute-results.json)
binds the admitted selection, route, fresh timing/electrical reports, pin access
and guide screening. Its setup/hold verdict is true; electrical and physical
closure verdicts are false.

**Decision:** retain the timing/area gains. Next apply bounded local repair to
the 21 distribution nets and six SRAM write inputs, preserving hold and checking
all affected connections. Locate the 22 Metal3 overflow units in the saved grid
before choosing a congestion change. Requalify the resulting whole chip before
detailed routing. No new detailed route, antenna closure, extraction, physical
power qualification, RTL/pipeline/protocol change or licensing decision occurred.

## 2026-09-23 — Connection ownership, reconciled loads and an unexecuted repair plan

Completed the approved preparation before another physical repair. Three
read-only geometry/STA commands take **20.684 seconds** in total, each capped at
120 seconds, two CPUs and 2 GiB. They consume the settled local and full-route
databases and reproduce both three-corner global measurement reports exactly.
Consumed-net annotation is complete, clocks are propagated and actual nominal
layer RC is verified. No repair, placement, routing or new pin simulation ran.

The 27 failing nets now carry complete physical consumers, terminal geometry,
typed source/sink owners, library limits, load ranges, retained delays and
min/max path summaries. Conservative traversal retains shared owners. The
distribution group splits into **one mode-control, nine serial-data and eleven
parameter-word control branches**; six further nets feed SRAM write inputs.
Pin capacitance, consumers, cells and placement are unchanged, while estimated
wire capacitance increases **1.03–3.52×**. On SRAM bit 15 it rises from 0.075497
to 0.228279 pF, and slew worsens from 0.067867 to 0.734179 ns against a 0.38 ns
limit. All six SRAM drivers still pass capacitance limits. The shared serial
consumer on `net1897` remains an explicit repair obligation.

Both saved ODBs retain the same nine nondefault-rule bindings, including
`clk → CTS_NDR_0`, despite the full-route log's runtime disable warning.
Saved binding identity does not establish identical effective routing policy;
this measurement does not isolate that override's contribution to the result.

The saved grid reconciles all **22 Metal3 overflow units** with 22 individual
cells. **Seventeen are above SRAM**, and the other five form the x=259.2 µm
column. One overlaps the macro body and one the reserved corridor. Only seven
overlap the failing nets' coarse guides. The other 15 require separate traffic
diagnosis; guide overlap is not causal attribution or detailed DRC.

Three shared helpers collect connections, join semantic ownership and compile
checked repair descriptions. The durable
[candidate](../../physical/experiments/paired-signal-repair-plan.json) specifies
**21 driver buffers and six SRAM receiver buffers**, retaining all original
cells, hold chains, clock connections and cycle boundaries. The unoccupied row
rectangles are hints, not legalized placement. Added cell-footprint cost is
**636.8544 µm² (0.178061%)**; no physical gain is claimed. The generated recipe
reproduces byte-for-byte and passes Tcl completeness checking but is unexecuted.

**35 focused tests** pass. Independent closeout confirms all **six diagnostic
containers absent**. The first read-only geometry attempt encountered OpenDB
SWIG proxy equality, and the second an unsupported layer-rule accessor; both
failed receipts and worker versions remain intact. Final analysis verifies
**799 hashes**. All 600 initial identities match before documentation updates;
**595 prior source/evidence identities** remain unchanged while five docs are
intentionally updated, including the stale next-discriminator list.

`build/validation/paired-repair-plan-01/report.json` has SHA-256
`b7ac5d6ff3f30b4cbf421945aa5d2761d665057ee0f90550a62efd332f5b8ce5`.
The [preparation manifest](../../physical/experiments/paired-repair-plan-results.json)
binds the read-only collection, reconciled diagnosis and unexecuted plan.

**Decision:** run one bounded local probe of the checked candidate, requiring
independent identity, legal placement, power bindings and complete all-corner
setup/hold/electrical checks across all affected connections. Diagnose the
remaining congestion separately before full-route requalification. Detailed
routing, extraction, antenna closure, physical power qualification and the
fast-screen temperature mismatch remain open; licensing remains pending.

## 2026-09-23 — Bounded execution and local qualification of the checked signal plan

Executed the approved 27-buffer plan once as `paired-signal-repair-01`, starting
from the settled `paired-reroute-01` ODB. The **6.005-second** probe stays within
its 120-second/two-CPU/2 GiB bound, with source design and PDK read-only. It inserts
21 driver buffers and six SRAM receiver buffers, legalizes only the added cells
and updates incremental coarse wires. The source checkpoint remains unchanged.

Independent export, geometry and three-corner STA take **12.448 seconds**.
Read-only reports for all 54 changed/new nets, saved grid/pin geometry and a
separate OpenROAD placement check take **12.752 seconds**. All measured corners
pass setup, hold, fanout, slew and capacitance, with complete consumed-net
annotation, propagated clocks and verified nominal RC. Slow setup improves
**+0.430335 → +0.527857 ns**. Fast-screen hold remains **+0.081790 ns**; slow
hold remains +0.347819 ns. Typical setup/hold are +6.258440/+0.169243 ns.
The 54 affected nets provide 324 positive min/max path summaries across the
three corners, and global STA also covers adjacent paths.

All 27 original problem nets are electrically repaired in these local estimates.
Fast slew/capacitance counts fall **4/19 → 0/0**, slow **80/16 → 0/0**, typical
**5/19 → 0/0**. The largest load on an original distribution driver falls from
0.386423 to 0.012289 pF in the fast screen. SRAM bit-15 input slew falls
**0.734179 → 0.019937 ns** against a 0.38 ns limit. The six new receiver branches
retain at least +0.273833 ns fast hold slack. Existing hold-delay cells and the
shared serial consumer on the bit-21 branch are retained.

Fresh native Yosys readback takes 0.865 seconds. It checks the exact planned
connections and buffer-contracted identity; grounding a new buffer input is
rejected. The complete chain through 168 prior buffer resizes and now 269 added
buffers is recomputed to the original 331,401-edge pin oracle. This reuses the
functional trace without another simulation. Every original cell/type/location,
all 342 clock-net connections, macro geometry and corridor remain unchanged.
Independent placement, row/overlap and new power-terminal binding checks pass.
Area is **358,297.5456 µm²**, exactly **636.8544 µm² (0.178061%)** above source.

Only 46 guide rectangle sets change, all within the 54 declared connections.
Another 2,297 raw guide blocks differ solely by repeated rectangles, not new
geometric coverage. Stored nondefault-rule bindings remain unchanged. The saved
incremental grid reports zero overflow; it does not supersede the prior full
route's 22 Metal3 units or qualify the 15 source hotspots outside the failing
nets' guides. No whole-chip or detailed route ran in this study.

All **eight exact containers** are independently absent. The three physical
stages total **31.205 seconds**. Analysis verifies **916 hashes** and preserves
all 621 initial identities before documentation changes; **616 prior source and
evidence identities** remain unchanged while five docs are intentionally updated.
The [signal-repair manifest](../../physical/experiments/paired-signal-repair-results.json)
binds the exact candidate, measurements, functional ancestry and local verdicts.
`build/validation/paired-signal-repair-01/report.json` has SHA-256
`52184dbc7bf5d2d19cacb7a1e113860cbb00928733e9fa6df09d7891425adcaf`.

**Decision:** retain the locally qualified candidate. Bind its full buffer
ancestry through routing intake, account for the saved Metal3 hotspots, then
require one bounded whole-chip coarse route with fresh timing/electrical,
congestion and pin-access checks. Coarse estimates, narrow fast hold and the
cell/SRAM temperature mismatch remain explicit. Extracted timing, detailed DRC,
antenna closure and physical power qualification are still open. No RTL,
pipeline, protocol, backend-default or licensing change occurred.

## 2026-09-23 — Whole-chip qualification of the 27-buffer signal repair

Executed the approved **single** `OpenROAD.GlobalRouting` step as
`paired-signal-route-01`, with a 600-second/four-CPU/6 GiB cap and all automatic
design, timing and antenna repair disabled. It finishes in **100.452 seconds**.
Independent mapped checks take **12.305 s**, minimum pin access **2.366 s**,
saved-grid/rule collection **0.414 s**, and two read-only residual-net comparisons
**20.470 s**. No additional route or physical repair runs.

The intake extension distinguishes 27 immediate additions from 242 prior ones
and 168 earlier resizes. Fresh Yosys readbacks of the original oracle, parent
and candidate take 1.284 s and recompute both identities. The parent export is
bound to its independent measurement; immediate geometry/power checks preserve
earlier repairs. **41 focused tests** pass, including six new chained-intake
cases. The original helper bytes and all prior experiment receipts are retained.

All **27 original targets and all 54 edited connections pass electrical limits**
after full routing. All corners have zero setup/hold/fanout violations, with
complete annotation and verified nominal RC. Slow setup is **+0.408159 ns**,
fast-screen hold **+0.088087 ns**, slow hold **+0.350921 ns**. Netlist bytes and
all context fields except database identity match the local candidate, retaining
342 clock nets, 1,572 FFs, every placement, macro/corridor geometry and
**358,297.5456 µm²** area. Minimum standard-cell/macro pin access passes.

Electrical qualification still fails on **15 different nets**: fourteen
eight-load branches (twelve `buf_1`, two `nand2_1`) and hold-buffer output
`net1889` into SRAM `A_DIN[51]`. Slow slew failures fall **80 → 16**; fast, slow
and typical capacitance counts are **13, 12 and 12**. Read-only local/full
measurements reproduce the independent global metrics and find unchanged pin
capacitance, **1.025–2.682×** wire capacitance, and **83.5–94.9%** wire share of
the residual nets' load. The ratio is measured variation, not a future bound.

Flow and saved-grid totals agree on **21 Metal3 overflow units**, versus 22.
Only two locations persist; twenty clear and nineteen appear. Capacity arrays
match. One remaining hotspot overlaps the macro edge at (259.2, 144.0) µm;
its sole guide association changes `_02961_` → `_01660_`. None overlaps the
corridor, eleven include clock guides, and five include a failing-net guide.
Association does not establish track-demand causality. Source accounting
preserves all 258 guide-associated nets and their conservative shared owners.

Runtime warnings name **`clknet_0_clk_regs`, `delaynet_4_clk`, and `clk`**, versus
only `clk` in the source route; all nine stored rule bindings stay unchanged.
The first analysis draft's generic wording incorrectly described repeated `clk`
warnings. It is preserved under `analysis-draft/`; the final analysis asserts
the exact distinct warning lists and reports the changed effective policy.
No isolated comparison attributes timing or congestion to that policy change.

All **nine exact containers** are independently absent. The
[signal-route manifest](../../physical/experiments/paired-signal-route-results.json)
binds `build/validation/paired-signal-route-01/report.json`, SHA-256
`0b82d074d9879f41e48d0b73602fc0ecbe3d0e2eeb8c4b5e0f4a35b7a6ee3329`.
Collection passes; electrical and congestion qualification fail. Before docs,
615 of 616 initial identities remain unchanged; the one changed helper has a
verified preserved copy. Five documentation pages are updated separately.

**Decision:** retain the repairs, then establish distribution-family wire-load
margins across passing neighbors as well as failing nets before selecting another
bounded local candidate. Diagnose the persistent macro edge separately from
migrating signal/clock congestion. Detailed routing remains unadmitted; coarse
wire estimates and the fast cell/SRAM temperature mismatch remain explicit.
No RTL, pipeline, protocol, default-backend or licensing change occurred.


## 2026-09-23 — Measured distribution contract and checked family repair plan

Completed the approved saved-evidence inventory and plan preparation without
executing another repair or route. The shared `physical_distribution.py` helper
uses explicit typed-owner predicates and all 64 SRAM write inputs, then closes
coverage over buffer and hold chains. It retains shared memberships and exact
consumers. The inventory contains **1,067 connections in 211 trees**, including
**124 hold cells**. This is complete within its stated family scope, not an
inventory of every chip signal.

Read-only geometry and both three-corner STA collections finish in **57.258 s**,
with 120-second/two-CPU/2 GiB caps per command. They yield **6,402 connection/corner
records** and **12,804 min/max path summaries**. Global timing/electrical metrics
match the prior independent measurements; terminal geometry and pin loads are
unchanged. Complete consumed-net annotation and explicit nominal RC pass. All
three exact containers are independently confirmed absent.

The assessor records per-branch capacitance/slew headroom and available wire
budget. Reserve sensitivity at 5/10/15/20/25% selects **20/27/29/33/34 connections**,
respectively. The **20% experimental target** includes all 15 failing nets and
**18 currently passing neighbors**. It is a trial gate, not a library requirement
or universal guard against future routing. No 2.682× multiplier is embedded.
SRAM bit 50 passes but has only **6.42% slow slew headroom** (0.556960 ns against
0.595200 ns), so it joins failing bit 51 in the proposed receiver repair.

The single checked plan contains **31 driver buffers and two SRAM receivers**,
all `buf_8`, with joint unoccupied-row hints and a collision-checked namespace.
Two targeted driver branches have six consumers; selection is not restricted to
eight-load failures. Predicted area addition is **778.3776 µm² (0.217243%)**,
within **1,074.8926 µm² (0.3%)**. Original cells, clocks and hold chains must remain.
Actual legality, new power bindings and electrical benefit remain unmeasured.

The [contract](../../physical/experiments/paired-distribution-contract.json)
requires at least 20% capacitance/slew reserve for the rebuilt inventory and all
new branches (**1,100 connections expected**, including 66 changed/new), zero
chip-wide electrical failures and at least 90% of current setup/hold slack in
every corner. Slow setup must remain at least **+0.367343 ns**, fast-screen hold
at least **+0.079278 ns**. These are acceptance floors for a future candidate.
Fresh whole-chip routing must later requalify congestion and effective clock
rules. The model, state count and execution-edge contract do not change.

Saved guide associations place inventory nets at 20 of 21 congestion hotspots,
but proposed targets at only five. The persistent macro-edge guide `_01660_`
belongs to shared cached/mode/capture logic outside the chosen scope. These
associations do not establish the cause of excess track demand or predict that
the buffer plan reduces congestion.

**54 focused tests** pass, covering completeness, passing neighbors, changed
source/consumer/corner evidence, reserve and budget gates, namespace collisions,
and existing repair/intake checks. The recipe passes syntax checking without
CAD execution. The prior generator and its test source are preserved byte for
byte. Before documentation updates, **986 of 988 initial identities** remain
unchanged; only those two source files change. Five documentation pages are
updated separately.

The [distribution manifest](../../physical/experiments/paired-distribution-results.json)
binds `build/validation/paired-distribution-plan-01/report.json`, SHA-256
`41ef9eab35ec182f42fe724fa438f66f11c4d738367314b1e03b4a017fc576c9`, and the
[unexecuted plan](../../physical/experiments/paired-distribution-repair-plan.json).
The next gate is one capped local execution of that exact plan followed by its
independent identity, placement/power and full-inventory measurements. Congestion
needs a separate discriminator before a full-route allocation. Detailed routing,
extracted timing and the fast cell/SRAM temperature mismatch remain open. No RTL,
pipeline, protocol, default-backend or licensing change occurred.

## 2026-09-23 — Local execution of the distribution contract

Executed the exact saved **33-buffer plan once** against `paired-signal-route-01`.
The source checkpoint, contract, generated recipe and preceding report hashes
pass preflight. The local probe takes **5.658 s**; independent export/geometry/STA
takes **12.439 s**, and full-inventory geometry/STA/placement checks **28.784 s**:
**46.881 s** of physical commands, each capped at 120 seconds, two CPUs and 2 GiB.
All eight exact containers are independently confirmed absent.

Independent readback verifies 31 driver buffers and two SRAM-input buffers,
without moving/resizing original cells or changing state/cycle boundaries.
All 342 clock-net connections, 1,682 chip-wide hold cells (124 covered by this
inventory), macro/corridor geometry and original power bindings remain. New
placement and power bindings pass; thirteen new cells move from their planning
hints during legalization. Area rises **778.3776 µm² (0.217243%)** to
**359,075.9232 µm²**, below the 0.3% cap.

Rebuilt coverage is exactly **1,067 original + 33 new connections**, in 211
logical trees, with all 64 SRAM write inputs retained. Every connection passes
the saved 20% capacitance/slew reserve in all three corners. Minimum reserves
are **26.12% capacitance / 21.87% slew**. Whole-chip electrical and setup/hold
violation counts are zero. Worst setup/hold slack is unchanged in every corner:
slow setup **+0.408159 ns**, fast-screen hold **+0.088087 ns**, so all fixed
90%-retention floors pass. The independent measurements cover 3,300 connection/
corner records and 6,600 min/max paths with complete consumed-net annotation,
propagated clocks and verified nominal RC.

All 31 selected original drivers see lower fast-corner load. Slow slew at SRAM
bits 50/51 falls from **0.556960/0.605968 ns** to **0.062730/0.062341 ns**. The
closest remaining budget is unedited bit 14's **21.87% fast slew reserve**;
its 1.87-point excess over the trial threshold is not a routing guarantee.
The new quantitative checker distinguishes incomplete evidence and failed
budgets, with **61 focused tests** passing. Fresh buffer contraction rejects
a grounded new-buffer input and independently recomputes the full ancestry:
302 buffer additions, 168 prior resizes, preserving the 331,401-edge pin oracle.

Only 57 declared connections change guide rectangle sets; no outside connection
does. The incremental grid's zero overflow does not replace the source's
**21 Metal3 units**. Nine stored clock-rule bindings remain. No new local NDR
warning is observed, which does not establish that the three source full-route
clock-rule relaxations were reversed. Congestion and effective policy retain
separate evidence boundaries.

The [distribution-repair manifest](../../physical/experiments/paired-distribution-repair-results.json)
binds `build/validation/paired-distribution-repair-01/report.json`, SHA-256
`9fa498482f38e0c8fc7c79a2426a08b494402a33d72815af2c61d626cb934b0b`.
All **1,183 initial identities** remain unchanged before the five documentation
updates. The planning receipt remains immutable; two new checker/test files
record the post-edit acceptance logic.

**Decision:** retain the locally qualified candidate. Diagnose the persistent
macro edge and migrating full-route congestion using saved artifacts, then bind
the exact candidate, ancestry and distribution budgets through intake before
one bounded whole-chip coarse route. No new whole-chip route, detailed routing,
extraction, RTL/pipeline/protocol/default or licensing change occurred here.

## 2026-09-23 — Native congestion diagnosis and distribution-route qualification

Completed the approved saved-congestion diagnosis and one bounded whole-chip
requalification of the exact 33-buffer candidate. **`paired-distribution-route-01`**
takes **62.633 s**, under 600 s/four CPUs/6 GiB with all automatic repair disabled.
Independent global checks take **12.711 s**, full inventory/placement checks
**28.869 s**, and minimum pin access **2.393 s**. All fourteen exact containers
are independently absent. No further physical repair or route follows.

Before launch, the extended schema-4 intake recomputes distribution coverage,
the immutable selection and quantitative gates, then checks exact driver and
receiver edits and legal added footprints. Three fresh native netlist readbacks
retain the original **331,401-edge** oracle through 302 cumulative buffers and
168 prior resizes. The route's independently exported netlist is byte-identical
to the candidate; all cells, placements, **1,572 FFs**, **342 clock nets** and
**359,075.9232 µm²** area remain unchanged. Minimum pin access passes.

The reusable congestion checker binds native GRT markers to the matching saved
grid and flow totals. The pinned OpenROAD source confirms that reductions are
included in both saved capacity and usage. The former macro-edge **17/18** grid
cell actually had available capacity/demand **0/1**, with `_02961_` crossing in
the earlier route and `_01660_` in the source. Guide overlaps are wider than
native crossings: source counts are **235 associations / 213 crossing nets**.
The local candidate inherits all 21 source marker records byte for byte despite
its incremental zero-overflow grid; a negative control rejects those as stale.
Two read-only API-inspection failures are retained (system Python lacked `odb`;
the SWIG source set was opaque), resolved with installed bindings and native JSON
export. Neither is a route failure or timeout.

Fresh Metal3 overflow changes **21 → 20**, with three persistent locations.
Native capacity/demand is **10/11** on twelve edges, **11/12** on seven and
**3/4** on one new upper macro-edge hotspot. The former zero-capacity overflow
clears. Native markers name **209 crossing nets**, against 239 guide associations;
six hotspots have actual clock crossings. Nine stored clock-rule bindings stay
unchanged, but runtime relaxations shrink from three named nets to only `clk`.
This does not isolate a causal timing effect or demonstrate congestion closure.

All **33 repaired nets plus 33 new branches** retain the fixed 20% reserve.
Across the full inventory, **1,091/1,100** meet reserve, six pass electrical limits
but miss reserve, and `_03012_`, `_03116_`, `_03160_` violate capacitance in every
corner. Their pin loads and consumers stay fixed, while wire capacitance grows
about **2.11× / 1.99× / 2.73×** relative to local estimates. Global checks also
find slow SRAM `A_REN` slew **0.596672 ns > 0.595200 ns** outside this inventory.

Fresh slow setup is **−0.074067 ns**, versus **+0.408159 ns** locally and a fixed
**+0.367343 ns** floor. Hold stays positive, but all retention floors fail:
fast **+0.041429**, slow **+0.290273**, typical **+0.121309 ns**. All consumed nets
have complete coarse wire estimates, propagated clocks and verified nominal RC.

The worst setup path changes from SRAM bit 51 to bit 53, ending at `uo_out[4]`.
An exact matching bit-53 prefix saved on another endpoint shows the one-receiver
status link `_06301_/Y → _06302_/B1` gaining load **0.068197 → 0.113368 pF** and
gate delay **1.117685 → 1.732932 ns**. This link is outside the branching-family
inventory. The worst input-hold path retains identical pins and edges with
**0.737588 ns** fast data arrival; capture-clock arrival grows
**0.472345 → 0.519004 ns**. These separate path mechanisms are more specific than
attributing every regression to congestion or an effective clock-rule change.

**73 focused tests** pass. Of **1,316 initial identities**, 1,315 remain unchanged
before documentation; the modified intake helper's original bytes are archived.
Final collection verifies **1,640 hashes**. The
[distribution-route manifest](../../physical/experiments/paired-distribution-route-results.json)
binds `build/validation/paired-distribution-route-01/report.json`, SHA-256
`e77b07eaf6e08e89d9abe6def32deb354c5ca2926c2132e19ed53284d1a29619`.

**Decision:** retain local repair benefits and reject whole-chip qualification.
Extend the checked scope to the single-receiver status link, capture-clock
arrival, SRAM control inputs and all nine inventory connections below reserve.
Select a bounded local repair with explicit setup/hold, neighborhood and area
gates; keep native congestion capacity/demand as a separate investigation.
Do not repeat a full route before local qualification. Detailed routing,
antenna closure, extraction and physical power qualification remain open.
No RTL, pipeline, protocol, default-backend or licensing change occurred.

## 2026-09-23 — Explicit path/control coverage and one bounded local repair

Extended the checked scope before selecting the next repair. Nineteen timed
connections add the one-receiver status link, seven input-hold endpoints and
all eleven dynamic SRAM control/address inputs to the complete distribution
families. Another 208 static macro inputs and one clock input are classified
separately. Read-only collection takes **12.134 s**. In addition to read-enable's
known slew failure, write-enable has only **3.66%** slow slew reserve.

The shared compiler gains an explicit-stage schema with checked sizes, original
consumers, unoccupied footprints, unique names and FF-data hold endpoints.
Legacy rendering remains byte-identical. The frozen plan declares nine `buf_4`
distribution drivers, one `buf_8` status driver, two `buf_4` SRAM-enable receivers
and fourteen `buf_1` buffers, two at each input endpoint. The **26-buffer** cost
is **284.8608 µm²**; stronger cells at every site would exceed the original cap.
The 20% reserve, timing floors and original area reference are not relaxed.

**`paired-path-repair-01`** executes once in **5.739 s**. Independent global
geometry/STA takes **12.434 s**, complete connection and saved-placement checks
**30.897 s**. Including source diagnosis, physical commands total **61.204 s**;
each is bounded to 120 s/two CPUs/2 GiB. All ten exact containers are absent.

All **1,145 covered connections** pass reserve in all three corners, with
minima **20.88% capacitance / 22.12% slew**. Whole-chip electrical violations
are zero. Slow setup improves **−0.074067 → +0.436742 ns**; fast hold
**+0.041429 → +0.093797 ns**, slow hold **+0.290273 → +0.439880 ns**, typical
hold **+0.121309 → +0.208469 ns**. Every original timing floor passes. Area is
**359,360.7840 µm²**, or **+0.296747%** cumulatively from the distribution-budget
reference; only **11.6542 µm²** remains below its 0.3% cap.

Matched status-path prefixes show driver load **0.113368 → 0.009168 pF** and
driver-hop delay **1.733107 → 0.317004 ns**; the hop includes the unchanged
predecessor's wire. That same output path reaches **+1.452227 ns** setup, while
another path now sets the global minimum. Slow read/write-enable transitions
become **0.073174 / 0.080670 ns**. The seven guarded inputs gain **82.4–88.6 ps**
fast data delay with identical capture-clock arrival at each endpoint in every
corner. The former worst endpoint's hold becomes **+0.123537 ns**.

Independent readback confirms all original cells/placements, **342 clock
connections**, **1,682 hold cells**, macro/corridor geometry and power bindings.
Only 36 guide-rectangle sets change, within the 45 declared changed/new nets;
clock guides stay fixed. Contraction transfers the **331,401-edge** oracle
through **328 cumulative buffers** and 168 prior resizes. Grounding a second
hold buffer fails the negative control. **74 focused tests** pass.

The initial collector's source-sink classifier mislabels seven original input
connections and their fourteen new branches after insertion. A separate checked
metadata artifact restores the declared source roles, verifying that every
electrical selector and connection stays identical. The initial collection is
preserved. Final reconciliation checks **2,002 hashes**: **1,569 of 1,573**
initial identities remain unchanged before documentation, three modified helper
originals are archived, and an unrelated README edit is observed and left intact.

The [path-repair manifest](../../physical/experiments/paired-path-repair-results.json)
binds `build/validation/paired-path-repair-01/report.json`, SHA-256
`bd8c280c0d19368043b43741baef7e5c1de3de826616eb0efb5a7fb682433178`.

**Decision:** retain the locally qualified repair. Extend shared intake to bind
the explicit path/control scope, every serial stage, complete functional ancestry
and original cumulative budgets before one bounded whole-chip coarse reroute.
The source's **20 Metal3 overflow units** remain the congestion reference;
incremental zero counts and inherited markers do not requalify it. No new
whole-chip route, detailed routing, extraction, RTL/pipeline/protocol change,
default promotion or licensing change occurs in this study.

## 2026-09-23 — Shared path intake and retained timing through a full route

Implemented shared path/control admission before spending the next route.
`physical_path_contract.py` rebuilds the nineteen declared connections, complete
distribution families and every new stage from source connectivity. It checks
the full non-data macro-input census, carries input-hold roles through inserted
buffers, reparses raw measurements and retains the original reserve, timing
floors and cumulative area reference. **90 focused tests** pass. The initial
new test caught lost role propagation where a branch already had a family;
the fix precedes admission. A mistaken parent-manifest choice was separately
rejected by functional identity during preparation, before CAD ran. Both
rejected receipts remain preserved.

**`paired-path-route-01`** completes one GlobalRouting step in **92.059 s** under
600 s/four CPUs/6 GiB. Automatic repair is disabled. Fresh whole-chip diagnostic
collection takes **13.371 s**; all-connection and placement checks **31.520 s**;
minimum pin access **2.515 s**. Two short read-only marker/API queries inspect
the settled database. All eleven exact containers are independently absent.

Slow setup is **+0.420384 ns** and fast-screen hold **+0.101286 ns**, versus
**−0.074067/+0.041429 ns** in the prior full route. Slow/typical hold is
**+0.457194/+0.221184 ns**. Every original timing floor passes. All **19 repaired
source nets plus 26 new branches** retain the 20% reserve. Complete coverage
finds **1,139 passing, four below-reserve and two failing connections**, from
**3,435 corner records / 6,870 min/max paths**. Every chip-wide electrical
failure is covered: `_03253_` and `_04701_` exceed capacitance in all three
corners; all nine slow slew failures share `_03253_`.

The remaining below-reserve connections are `_02981_`, `_03380_`, `_04527_`
and SRAM DIN14 branch `net31`. Serial branches `_02981_`, `_03253_` and
`_03380_` all carry bit 53; the five capacitance-sensitive drivers are existing eight-load `buf_1`
cells. Every measured pin-load set is unchanged. On the two failing nets,
fast-corner wire capacitance grows **2.57× / 2.13×** relative to the local
candidate. The whole-family contract detects this migration of weak margins;
the local 20% target does not prove a bound on global wire redistribution.

Fresh export is byte-identical to the local candidate. Every cell and placement,
**342 clock connections**, **1,572 FFs**, macro/corridor geometry and power
binding remains. Functional ancestry transfers the **331,401-edge** oracle
through the same **328 buffers and 168 prior resizes**, without another pin
simulation. Area stays **359,360.7840 µm²**, cumulatively **+0.296747%**, leaving
only **11.6542 µm²** beneath the fixed 0.3% allowance. Two more `buf_1` cells
alone would cost 14.5152 µm², so additive repair cannot be presumed affordable.

The final route table reports **22 overflow units**: 21 Metal3 and one Metal4,
versus twenty Metal3 units previously. Native JSON also contains 22 markers;
the saved grid exposes only 21 Metal3 units. Strict complete reconciliation
rejects the mismatch. A separately labelled 21-marker subset matches exactly;
the horizontal **11/12 capacity/demand marker at (511.2, 352.8) µm** remains
unreconciled and is not assigned a layer by inference. Only two matched hotspot
locations persist from the source. This is no congestion improvement or complete
location diagnosis. Nine stored clock rules remain, but runtime relaxation now
includes **`clknet_0_clk_regs` and `clk`**, versus only `clk` in the parent.
Timing passes under this policy without isolating its causal contribution.

The [path-route manifest](../../physical/experiments/paired-path-route-results.json)
binds `build/validation/paired-path-route-01/report.json`, SHA-256
`a6e2493a0b50a63066f7a174da3c6fef371f8b9986ad164669a646d11670a5d3`.
Final report construction checks **2,099 hashes**, including all **1,797 prior
identities**; 1,796 are unchanged before documentation and the original intake
helper is archived. No previous receipt is rewritten.

**Decision:** retain whole-chip timing gains and reject full electrical/reserve
and congestion qualification. Use saved geometry, loads and library costs to
compare redistribution or selective sizing over the residual families under
unchanged budgets. Resolve the extra congestion marker independently before
choosing a location-specific capacity change. No second route, further repair,
detailed route, extraction, RTL/pipeline/protocol change, backend promotion or
licensing decision occurs in this study.

## 2026-09-23 — Physical organization policy and saved-chip candidate screening

Added a bounded physical organization layer between the measured distribution
inventory and exact repair plans. `physical_organization.py` reconstructs actual
transport trees, retains shared trunks once and compares three explicit choices:
fixed-origin buffer growth, equal-count same-source leaf exchanges and a separate
SRAM data receiver. The policy binds the settled `paired-path-route-01` database
and original path contract; 2,202 clock/hold/endpoint instances are protected.
Ordinary leaves may move between branches while fixed state, macro and transport
loads stay attached. No physical implementation is edited.

The reconstruction finds **211 trees / 1,109 family branches / 4,613 leaves**.
Its **898 transport cells** comprise **774 buffers and 124 delays**, with
**10,303.9776 µm²** counted once. Earlier passing screen columns called this
combined transport count buffers; the selected receipt distinguishes the two.
The broader **1,145-connection path contract** remains the qualification scope.
The six residual connections occupy four trees and 64 branches; **192 independent
pin/corner checks** reproduce saved STA loads from pinned Liberty files.

The first attempt rejects mixed-load capacitance aggregation: maxima from
opposite rise/fall edges cannot be summed independently. The corrected reader
sums all receivers at a common edge before taking extrema. That failed log and
three intermediate passing screens remain, with their earlier helper bytes
archived. A later refinement lets ordinary leaves on mixed branches regroup
while fixed transport consumers stay attached. Virtual exchanges are checked
against the saved independent Yosys readback; a wrong functional source is
rejected by complete circuit comparison after buffer contraction.

**`paired-organization-screen-05`** completes in **7.330 s**, without Docker or
CAD. **107 focused tests** pass, including 17 new organization checks. Eighteen
choices are costed and **no complete portfolio passes the current geometry
policy**. Uniform stronger-driver choices cost at least **18.1440 µm²**, beyond
the **11.6542 µm²** remaining in the original cumulative area allowance.
`_04701_`'s driver `_09463_` collides with `_11880__1348` even at `buf_2`; allowed
leaf exchanges do not reduce its span. Other rejected growth footprints are
recorded by exact neighboring instance.

An eight-swap, zero-added-area bit-53 candidate reduces the three residual
branches' pin-envelope HPWL **602.275 → 598.0025**, **947.010 → 928.255** and
**860.970 → 284.315 µm**. It changes thirteen scalar-input assignments in a
virtual copy and preserves full buffer-contracted identity. Its greatest
geometric gain is on `_03380_`; failing `_03253_` improves only about 2%, and
no new wire capacitance, slew or setup/hold is measured. The second nonempty
exchange improves a neighbor while leaving its residual target unchanged.
Neither is evidence of physical qualification.

The mixed hypothesis combines that bit-53 regrouping, two `buf_1` → `buf_2`
upgrades and a DIN14 `buf_1` receiver, costing **10.8864 µm²** and leaving
**0.7678 µm²** beneath the unchanged area cap. This is area arithmetic only:
the `_09463_` footprint already fails, and timing/electrical benefit is unknown.
The fixed-placement policy therefore exposes the next missing capability
without widening budgets or selecting an executable repair.

The [organization manifest](../../physical/experiments/paired-organization-results.json)
binds `build/validation/paired-organization-01/report.json`, SHA-256
`40621e90cb011a1e96520acac28010dc9973867035ce06e374ed0a65b2ea5d32`.
Report creation checks **2,229 hashes**: all **1,946 prior nondocument identities**
remain unchanged, and all six updated documents have matching pre-edit snapshots
within the **1,952-identity** initial inventory. Existing source helpers and
every prior receipt remain intact.

**Decision:** retain the abstraction and screen a narrow move-and-resize rule
for the blocked buffer, costing all incident connections and protected boundaries.
Compare bit-53 grouping choices against weak-branch wire budgets. New edit types
need independent exact-edit/readback checks and bounded local physical validation
before whole-chip route admission. Keep the original reserve, timing floors and
area reference. The **22-marker / 21-grid** congestion mismatch is a separate
unresolved question. No CAD, new physical measurement, repair, route, RTL/pipeline
change, backend promotion, commit, push or licensing decision occurs here.

## 2026-09-23 — Bounded organization refinement and local electrical qualification

Extended the organization policy with one named buffer's bounded same-row
move-and-resize rule and a grouping objective that ranks weak branches against
their wire budgets. The pinned LEF reproduces both source signal-pin locations
before projecting a new footprint; the screen costs both incident connections,
protected geometry and the original cumulative area allowance. Equal-count
exchanges preserve source identity and pin-capacitance bounds. Proportional
span/wire scenarios are conditional screening assumptions, not electrical bounds.

**`paired-locality-screen-01`** takes **8.842 s** to compare **35 choices / 104
complete combinations**. Twenty-six pass area/footprint checks and thirteen
also pass the conditional wire-budget screen. The selected plan moves `_09463_`
one **0.48 µm** site left while growing it from `buf_1` to `buf_2`, upgrades
`_08797_` in place and adds one DIN14 receiver. Sixteen bit-53 leaf swaps produce
**23 distinct scalar-input reassignments across ten branches**. The three target
pin-envelope spans change **602.275 → 575.020**, **947.010 → 332.4225** and
**860.970 → 534.445 µm**. Both incident spans of the moved buffer remain fixed.

The new exact-plan compiler validates source endpoints, consumer bijections,
protected cells, legal footprints, same-row/grid movement and area before
producing the recipe. Six preflight mutations are rejected. **110 focused
tests** pass, including twenty organization checks. The initial sandbox launch
cannot access Docker and stops before a probe directory or container exists;
that log is preserved. The authorized launch is the sole executed physical edit.

**`paired-locality-01`** completes its local probe in **18.720 s** under
**120 s / two CPUs / 2 GiB**, with source design and PDK mounted read-only.
Fresh diagnostic collection takes **24.822 s**, complete connection/geometry/
placement checks **81.585 s**, and minimum pin access **5.314 s**. Every bounded
check completes; all nine exact containers are independently absent.

All **1,146 connections / 3,438 corner records / 6,876 min/max paths** meet the
original 20% reserve. Minimum reserves are **24.5592% capacitance / 21.5316%
slew**. Capacitance, slew, fanout, setup and hold violation counts are zero in
all three corners. Slow setup remains **+0.420384 ns** and fast-screen hold
**+0.101286 ns**; all original timing floors pass. The derived contract advances
source identity and edit selectors, adds the new receiver to complete coverage,
and retains every original numerical budget.

The bit-53 pin loads remain unchanged. Their fast-corner wire capacitances fall
**0.157347 → 0.073543 pF**, **0.322079 → 0.042548 pF** and
**0.173625 → 0.067571 pF**. The formerly failing `_03253_` now has **54.34%
capacitance reserve** with its original `buf_1` driver. This is measured local
coarse-routing benefit; the span screen did not predict the resulting parasitics.
Added area is **10.8864 µm²**; total **359,371.6704 µm²** is cumulatively
**+0.299786%**, leaving **0.7678 µm²** under the unchanged 0.3% experiment allowance.

Independent fresh Yosys readbacks preserve complete buffer-contracted circuit
identity and transfer the retained **331,401-edge** oracle. Exact physical
readback confirms the declared reassignments, two resizes, one translation and
one new receiver; all **2,202 protected instances**, **342 clock connections**,
original power bindings and nine stored clock-rule bindings remain. Fifteen
guide sets change within sixteen declared incident nets; clock guides remain
unchanged. A grounded receiver and a corrupted moved footprint are rejected.
All **33,600 standard-cell pins** and the macro pass minimum pin access, with
no off-grid warnings. This access check does not prove simultaneous routability.

The [locality manifest](../../physical/experiments/paired-locality-results.json)
binds `build/validation/paired-locality-01/report.json`, SHA-256
`28d4f25a4d50d303afadf833a6ccfc95fd9c9fa119a19e22f025d02179293d5d`.
Report construction checks **2,582 hashes**, including preservation of all
**2,008 initial identities**: 1,999 remain unchanged, and the three edited
source/test files plus six documents have matching original snapshots. Prior
receipts and source physical artifacts remain intact; this journal is append-only.

**Decision:** retain the locally qualified candidate and extend shared route
intake to independently recompute regroup/resize/move operations, full functional
ancestry, all 1,146 connections and the original budgets before admitting one
bounded whole-chip coarse comparison. The local incremental grid's zero overflow
does not replace the source's unresolved **22-marker / 21-grid** congestion
evidence. The unmatched **11/12 capacity/demand marker at (511.2, 352.8) µm**
remains a separate diagnosis. No whole-chip route, detailed route, extraction,
power-grid continuity qualification, RTL/pipeline change, backend promotion,
commit, push or licensing decision occurs in this study.

## 2026-09-23 — Shared physical edits and a rejected whole-chip qualification

Extracted four declared operations into `physical_organization_edits.py`:
buffer resize, bounded same-row move-and-resize, same-source consumer regrouping
and receiver insertion. Candidate search and the historical recipe builder are
separate from policy validation and independent readback. The common checker
supports different operation counts, measures both incident sides and protects
state, clocks, macro, hold cells, rows, blockages, supply connectivity and occupied
footprints. The retained local recipe and exact proof reproduce unchanged.

Schema-5 shared route intake independently reconstructs exact edits, functional
ancestry, original roles, all **1,146 connections**, raw electrical/timing records,
pin access and the original area reference. Fresh Yosys readbacks transfer the
existing **331,401-edge** oracle. **121 focused tests** pass in **3.275 s**;
six real-artifact mutations with updated hashes are rejected. The first negative
control harness expected a later area-budget diagnostic; admission correctly
rejected the mutation earlier at ancestry. The corrected harness and both logs
are retained. Preparation's nonfatal unclosed-file warnings are also preserved;
the resulting bytes and fresh readbacks are hash-bound.

**`paired-locality-route-01`** is the sole whole-chip route, under **600 s / four
CPUs / 6 GiB**, with automatic design, timing and antenna repair disabled. The
flow reports **36 seconds**, exits zero and warns of congestion. All subsequent
checks finish within their caps: fresh diagnostics **12.696 s**, complete
connections/geometry/placement **71.632 s**, minimum pin access **4.888 s**.
Ten exact containers are independently absent. No timeout occurs.

The six original weak connections retain 20% reserve. `_03253_`'s fast wire
capacitance is **0.044594 pF**, close to the local **0.042548 pF** and below the
prior full-route **0.322079 pF**; its minimum capacitance reserve is **53.66%**.
However, whole-chip qualification fails. Of **1,146** scoped connections,
**1,142** meet reserve, three fail and one misses reserve. Serial-shift bit-50,
bit-49 and bit-51 branches `_02988_`, `_03097_`, `_03552_` now fail capacitance;
their unchanged drivers/pin loads accompany **2.76× / 3.26× / 2.84×** fast wire
growth against local estimates. `_04718_` has **19.9146%** slow slew reserve.

Independent global checks find a fourth capacitance failure on `_01924_`, outside
the declared inventory. All corners have four capacitance failures; the slow
corner has twelve slew failures across `_02988_` and `_03552_`. Slow setup falls
**+0.420384 → −0.055813 ns**, and fast hold **+0.101286 → +0.064551 ns**. Both
retained floors fail; all other timing floors and the original area cap pass.
Area stays **359,371.6704 µm²**, cumulatively **+0.299786%**, leaving **0.7678 µm²**.

Exact readback confirms a byte-identical netlist and unchanged physical context,
including all 342 clock connections and power bindings. All **33,600 standard-cell
pins** and the macro pass minimum access with no off-grid warnings. Every consumed
net is annotated. These checks do not establish simultaneous routability.

Reported overflow rises **22 → 33**. All **33 native markers / saved-grid units /
flow units** reconcile on Metal3: ten 11/12 and twenty-three 10/11 capacity/demand
edges, with no zero-capacity hotspot. Two locations persist from the prior result.
The old 22-marker / 21-grid discrepancy remains unresolved for that older artifact;
the new reconciliation does not retroactively explain its missing edge.

Read-only analysis of the saved reports identifies one timing mechanism without
another CAD command. For the matched `ui_in[6] → _12281_/D` hold path, every
reported data arc and **0.785377 ns** data arrival are unchanged. Capture-clock
arrival increases **0.509116 → 0.548950 ns**, explaining the **39.835 ps** slack
loss at report precision. The worst setup source changes from SRAM to
`r_mode[0]`, through overloaded `_01924_` to status `uo_out[4]`; the matching
prior path is not present in the saved top-1,000 report. Its clock/data split
therefore remains unmeasured. All nine stored nondefault-rule bindings remain,
but the new route logs no relaxations versus prior `clk` and `clknet_0_clk_regs`.
This is a runtime-policy observation, not proof of final spacing or sole cause.

The [manifest](../../physical/experiments/paired-locality-route-results.json)
binds `build/validation/paired-locality-route-01/report.json`, independent
admission, tests, failed quantitative gates and saved-result diagnosis. All
**2,151 initial identities** are accounted for: **2,141** unchanged, with matching
original snapshots for four modified source files and six documents. Prior
receipts remain intact and the journal update is append-only.

**Decision:** retain the reusable abstraction and local evidence; reject the
routed candidate's qualification. Next query matched mode-to-status and input
clock paths on both saved chips, inventory the uncovered control tree and passing
siblings, and compare complete bit-49/50/51 distribution families against the
33 reconciled shared-capacity edges. Verify effective clock-rule application
before choosing any further physical intervention. Keep the original budgets.
No additional physical edit, new pin simulation, detailed route, extraction,
RTL/pipeline change, backend promotion, commit, push or licensing decision occurs.

## 2026-09-23 — Matched clock/control paths and complete affected families

**`paired-coupling-01`** compares the settled `paired-path-route-01` and
`paired-locality-route-01` chips using only read-only collectors. Normalized
configurations match. Four paths fix source/destination transitions and every
intermediate pin; independent parsing requires identical pin, transition and
cell sequences. Complete transport closure covers **118 connections** in five
trees: shared control **6**, serial bits 50/49/51 **13 / 8 / 88**, parameter
control **3**. Thirteen clock nets cover root, SRAM delay chain and register
branches. Exact pin loads and geometry are unchanged across both chips.

Two three-corner family/path collections take **14.263 / 14.202 s** of command
time. The initial reports lump input-wire and cell delays, so two additional
path-only collections request input-pin detail: **10.777 / 10.756 s**. Geometry
takes **0.491 s**. These five successful commands total **50.489 s**, each under
**120 s / two CPUs / 2 GiB**. No route or repair runs. A prior **0.197 s** attempt
stopped on a Python syntax error before OpenROAD; its worker, log and failed
receipt are preserved. All six collector containers and both source-route
containers are independently absent. No timeout occurs.

The slow mode-to-status path changes **+2.262653 → −0.055813 ns**. Its arrival
increase is **2.318466 ns**, comprising **2.299226 ns data** and **0.019240 ns
launch clock**. The required time stays fixed. `_01924_`'s fast wire capacitance
grows **0.115121 → 0.309965 pF**. Its driver, wire into `_06218_/B1` and following
gate add **1.534994 ns**, or **66.76%** of the matched data increase. Other arcs
contribute; this is measured attribution, not a predicted repair outcome.

The slow SRAM-bit-53 status path changes **+0.420384 → +0.113294 ns**. Arrival
grows **0.307090 ns**: **0.205627 ns launch clock / 0.101463 ns data**. Clock
wire into `delaybuf_4_clk/A` and that cell add **0.173777 ns**; `delaynet_3_clk`
wire capacitance changes **0.085832 → 0.162166 pF**. This is a distinct mechanism
from the dominant mode/control data-path regression.

Fast input hold changes **+0.104386 → +0.064551 ns** on the same path. Every data
arc and **0.785376847 ns** arrival remain identical. Capture clock arrives
**39.833486 ps** later, and the changed requirement accounts for **39.835244 ps**
slack loss. The prior worst parameter self-hold path remains **+0.101285927 ns**
as launch and capture move together with reconvergence correction. A clock shift
therefore needs a path-specific contract, not one undifferentiated clock margin.

All **118** family connections pass 20% reserve in the earlier full route;
**113 pass / four fail / one misses reserve** afterwards. All six shared-control
branches were outside the previous scope. The new measured watchlist proposes
the inherited inventory plus these branches (**1,152** total), four exact paths
and thirteen clock nets, while preserving all numerical budgets. Production
admission is not changed. Fresh global timing/electrical values reproduce the
saved measurements; consumed-net annotation remains complete.

Fresh geometry independently reproduces all **33 native Metal3 overflow edges**.
Thirty-four selected-family nets cross **21** edges, ordinary clocks cross
**nine**, and all edges contain other signal traffic. No current edge directly
contains a net with a stored NDR binding. The pinned OpenROAD source and binary
version agree on commit `dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`:
`applySoftNDR` records a runtime cost change without clearing the database rule.
Both artifacts retain nine identical bindings and dimensions, while only the
older run logs softening `clk` and `clknet_0_clk_regs`. This does not establish
a useful clock-rule relaxation counterfactual. The older 22-marker / 21-grid
discrepancy remains unresolved for that artifact.

Four negative controls reject wrong path transition, missing arc, ambiguous
path and wrong grid identity. The preceding 121 production tests are retained;
no production source changes or repeated suite run is needed. The
[manifest](../../physical/experiments/paired-coupling-results.json) binds
`build/validation/paired-coupling-01/report.json`, raw measurements, source-code
evidence, complete diagnosis and the measured watchlist. All **2,497 initial
identities** are accounted for: **2,491** unchanged, plus matching original
snapshots for the six updated documents. Earlier receipts remain intact and
this journal remains append-only.

**Decision:** screen area-neutral data regrouping and the actual support for a
clock-delivery constraint as separate choices. The former must cover complete
control/serial trees and passing siblings; the latter must protect the measured
SRAM launch and input capture behavior. Retain global capacity checks and the
original timing, reserve and cumulative area contract. Only **0.7678 µm²** remains
in its allowance. No new physical repair or route is selected, no numerical
budget is relaxed, and no RTL/pipeline change, backend promotion, commit, push,
new pin simulation or licensing decision occurs.

## 2026-09-23 — Integrate the branch in reviewable local milestones

The user approved consolidation and requested commits as work progresses.
An initial inventory recorded **283 pending paths** (37 modified tracked files,
246 untracked files) above `47f90b3`. The implementation was separated by
logical dependencies: shared composition/admission/results, SRAM/fetch
organizations, paired execution, physical tooling, experiment records, and
current documentation. The first five commits are:

- `fe6abab` — shared contracts
- `7d3dc27` — sram and fetch
- `c9e7391` — paired execution
- `551b071` — physical tooling
- `e927b77` — experiment records

The default Lean import omitted `Storage.PairedController`, causing the
portable gate's complete-module check to reject the accumulated tree. Adding
that import brings all **206** modules into the default build/audit without
changing a backend selection or claiming the missing paired refinement.
The code and experiment recipes otherwise retain their initial contents.

Isolated source snapshots passed **86**, **148**, **192**, then **408** Python
tests as the relevant milestones accumulated; each run skipped the same two
Linux-specific process-inspection cases on macOS. The final run has 406 passes.
The clean first build and later incremental builds, complete-library audit,
paired graph controls and conditional schedule checks passed. The final audit
covers **15,395 declarations / 7,706 theorems**, including generated declarations,
with standard axioms only and a rejected injected custom axiom.

The full foundation wrapper hit its **1,200-second aggregate cap** during
Memory after **29 of 32** suites passed. Its cleanup initially reported
termination unconfirmed; independent `ps` and process-group probes confirmed
the exact group **8135** absent before results were collected. The failed
aggregate receipt is retained. Only Memory, SerialUpload and HostResult were
resumed, under separate **600-second** bounds; all passed. All **32 constituent
suites** are therefore complete, but the interrupted aggregate command is not
reported as a pass. The separate `foundation-completion.json` binds the final
sources and the split execution. No successful suite was needlessly restarted
after that timeout.

All **88** experiment-record files retain their inventory hashes, **76** JSON
records parse, and **39** local report bindings match. Generated evidence and
local one-off study scripts remain under ignored `build/`; committing their
selected summaries does not distribute the raw artifacts. Previous receipts
and this journal's initial prefix are preserved.

The [integration guide](../history/branch-integration.md) now distinguishes retained
interfaces, references, experimental implementations and open proof/physical
obligations. The technical index routes readers to current owners instead of
repeating an obsolete sequence of next steps. The submission plan explicitly
labels its earlier hybrid sequence and points to the current paired decision.
No physical experiment, RTL behavior change, default promotion, push, PR or
licensing decision is part of this consolidation. Source snapshots, checks and
commit receipts live in `build/validation/branch-consolidation-01/`.


## 2026-09-23 — Timing obligations and complete organization comparison

Implemented the approved organization study with saved chips and no CAD run.
The source audit identifies live rejection on page zero as part of the current
edge observation; the existing registered page-three result is a distinct view.
The host input-hold witness is `ui_in[6]` to first-stage clear control, and the
parameter self-hold witness uses one physical clock endpoint. The measured SDC
matches the current 20 ns / 4.0 ns maximum / 0.2 ns minimum I/O assumptions.
The organizer page still specifies 6x4; the 0.3% increment remains our separate
experimental comparison budget.

`physical_organization_study.py` adds conditional clock-shift obligations and
combinational-copy costs. `report-physical-organization.py` joins these to the
existing planner and independent virtual identity check. The first helper
milestone is committed as `47aaa9c`. No Lean/RTL source or physical edit changes.

Selected comparison **paired-organization-comparison-04** completes in
**4.112 s** under a **120-second** command cap. It checks all **1,152** inherited
and proposed-watchlist connections against the selected database, reconstructs
five trees and reconciles **354** independent net/corner pin loads. Twelve
consumer swaps across fourteen branches change twenty scalar inputs with whole
buffer-contracted virtual identity preserved. No complete family clears the
conditional wire screen. The bit-51 ratio improves **1.725 -> 1.186**, which is
still above budget and remains a geometric scenario rather than a routed result.

Clock-environment replay keeps newer data delay and substitutes earlier launch
and required time. It restores the measured input-hold reserve but still leaves
**0.403916 ns mode/status** and **0.048422 ns SRAM/status** below retained setup
floors. These are conditional, one-sided obligations; no feasible clock tree is
claimed, and opposite checks remain to collect.

Two regional decoder-copy proposals add **14.5152 / 7.2576 um^2**, or
**21.7728 um^2** together, against **0.767837 um^2** left in the existing allowance.
The NOR's parent nets already have full-inventory measurements; reusing them
shows that the extra pin load fits the capacitance reserve with saved wire.
The XOR's two parent measurements remain missing. New wire, slew, placement and
timing remain unqualified. The small cost supports retaining local decoding as
a structural alternative instead of interpreting the incremental-cap rejection
as physical infeasibility.

**42 focused tests** pass, including eleven new helper cases. Four final
integration mutations reject changed diagnosis identity, missing path coverage,
an added cycle and state replication. The initial preparation attempt expected
hash strings to be reference objects and stopped before writing its initial
receipt; the error receipt is preserved. Four completed comparison versions and
all earlier outputs remain, with the fourth including reusable full-inventory
parent measurements and measured-SDC identity. No timeout occurred.

**Decision:** compare regional tree replacement/reuse and decoding with explicit
area, clock and shared-capacity budgets. Obtain the two missing parent-net
measurements and opposite timing checks before selecting a physical candidate.
Keep the prior admission contract and all numerical budgets intact; any separate
budget must be declared before execution. No coarse/detailed route is admitted.
The [study](../physical/physical-organization-study.md) owns interpretation and the
[manifest](../../physical/experiments/paired-organization-study-results.json)
binds the selected report and checks. Supporting receipts are under
`build/validation/paired-organization-study-01/`.

## 2026-09-25 — explicit hierarchy policies and matched flat control

Implemented the bounded [hierarchy comparison](../physical/map-tile-study.md#explicit-hierarchy-comparison--september-25)
around the existing tiled chip. The checker names its synthesis boundaries,
requires their exact instances after mapping and distribution, and binds every
flat leaf to its original module through JSON flattening and Verilog read-back.
`--compare-flat` maps the identical candidate RTL with the same recipe and load
budget while removing the storage-tile boundaries. Existing synthesis defaults
remain available; no Lean circuit or RTL generator changes.

Selected `hierarchy-policy-02` passes in **559.885 s**, longest command **84.247 s**
against the existing 180 s cap. Six SAT proofs, two rejected mutations,
**2,553,100** independently simulated edges, the Lean build and standard-axiom
audit pass. Portable validation records **448 passed / 2 skipped**. The
[tracked receipt](../../physical/experiments/hierarchy-policy-results.json)
pins the full report, 259 inputs, 178 artifacts, validation and source hashes.

Both corners reproduce the 2.021629% standard-cell saving from retaining the
32 tiles, with mixed address-depth effects; the study owns the measurements.
The first complete comparison, `hierarchy-policy-01`, also passed and remains
intact. An intermediate export probe exposed private-name encoding in Yosys;
the final run checks that exact conversion and rejects collisions or arbitrary
renaming. Two full runs total **1,057.987 s** elapsed, excluding the small probes
and unit tests. Historical cumulative CAD use remains unknown.

**Allocation:** retain the explicit policies and checked flat views for future
architecture comparisons. No timing, placement, routing or Docker run was
launched. This mapping result does not promote a physical candidate or close
the separate Lean interpretation obligation.

## 2026-09-25 — temporary size overages permitted for exploration

The user clarified that architectural exploration may temporarily exceed size
constraints when the overage is recorded; new ideas can be optimized afterward.
The [research workflow](README.md#exploration-with-temporary-size-overages) and
[active status](status.md) now carry this direction. Record the original target,
candidate size and overage, observed benefit, other regressions and the next
optimization question. A complete plan to recover the area is not a prerequisite
for trying an idea. The old 0.3% repair allowance remains a historical comparison,
and final qualification retains its applicable requirements. This is a policy
update; no hardware, acceptance checker, historical receipt or measured result
changed, and no new CAD run was launched.

## 2026-09-25 — regional decode copies, input distribution and coarse reroute

Completed the authorized [regional-decoding experiment](../physical/regional-decoding-experiment.md)
from the saved `paired-locality-route-01` checkpoint. The two missing parent nets
and opposite setup/hold checks were collected first. Two spatial gate copies
improve the local mode/status path by **0.656426 ns**, but add two fanout
violations. A second variant adds two shared input buffers, removes both new
violations and retains the timing gain with unchanged matched clock paths.

The buffered candidate adds **39.9168 µm²**, **0.011141%** of the original
reference area. Its total **359,411.5872 µm²** exceeds the historical repair cap
by **39.148963 µm²**. This overage is explicitly exploratory. Actual Verilog and
ODB readbacks pass identical-gate folding, buffer contraction, exact terminals,
all original cell placements, clock connections and power bindings. There is
no added state, pipeline cycle, RTL change or new Lean theorem.

One **88.946-second** coarse-route container retains the selected mode/status
gain (**+1.798552 ns** slack) and reduces global capacitance violations **4 → 1**
and complete-grid overflow **33 → 19**. Whole-chip qualification still fails:
worst slow setup is **−0.113646 ns** from SRAM output bit 51 to status; worst fast
hold is **+0.049847 ns** from `r_serial_shift[43]` into SRAM. SRAM input bit 35
has a fast slew violation. These replace the earlier critical paths without
meeting the retained setup/hold floors. The incremental probes' partial grid
snapshots cannot support a zero-overflow claim.

The final report reconciles **1,494 net/corner pin loads** and **192 timing
witnesses**, with complete consumed-net wire estimates. The original global
metrics reproduce. The new collection covers up to **126 connections**, including
all five selected families and both sides of added cells; the full 1,152-net
qualification watchlist remains a later obligation. The portable suite records
**463 passed / 2 skipped**, including fourteen decoder-copy tests and the blank
fanout-slack parser regression exposed by this experiment.

Nine CAD container attempts total **169.993 seconds** against the declared
1,200-second budget, with two local variants and one coarse reroute. All
containers are absent; no timeout or detailed route occurred. Preserved failed
attempts document the initial supply-port expectation for signal-only Verilog,
a geometry reader launched without OpenDB's runtime, and the fanout parsing
reconciliation. They required no repeated physical edit or coarse route.
The [manifest](../../physical/experiments/regional-decoding-results.json) binds
`build/validation/regional-organization-01/report.json`, 335 retained source
versions and 508 artifacts.

**Decision:** retain regional decoding as a measured implementation technique;
do not promote the physical candidate. Next compare the complete bit-51
distribution with the SRAM write-input timing environment. Keep the Lean
semantic reference and its open paired compiler/admission/package obligations.
This bounded prototype used existing generated circuitry and required no
Hardcaml migration.

## 2026-09-26 — SRAM distribution and write timing

Completed the authorized [SRAM follow-up](../physical/sram-distribution-experiment.md)
to the September 25 regional experiment, preserving its original evidence. Two
local variants add 20 then 34 noninverting buffers, with exact ODB and independent
Verilog readbacks. All original cells, placements and state remain; no cycles or
RTL changes are introduced. The final local variant clears both retained timing
floors and all 1,252 measured connections' 20% electrical reserve.

- **Complete-route comparison:** an unchanged reroute reproduces all baseline
  measurements and the stored grid. The candidate improves worst slow setup
  **−0.113646 → +0.321638 ns** and fast hold **+0.049847 → +0.089025 ns**. Global
  slew and fanout violations are zero. Every SRAM write-data hold check has at
  least **+0.161179 ns** margin; global hold now limits a different state path.
- **Failed qualification:** setup misses the retained +0.367343 ns floor by
  **45.705 ps**. `_04754_` now exceeds its 0.3 pF capacitance limit, while
  `_02966_` and `_05207_` miss reserve. Router overflow is **16**, versus 19 for
  the control; the saved grid exposes **15**. The extra Metal4 unit remains
  unresolved after two read-only API probes. No detailed routing or promotion.
- **Size:** 34 buffers add **364.6944 µm²**. Total placed area is
  **359,776.2816 µm²**, or **0.412712%** above the original reference and
  **403.843363 µm²** above the historical allowance. The die is unchanged; the
  overage is recorded under the approved exploration policy.
- **Evidence:** the complete inherited 1,152-connection watchlist plus additional
  read-path and new branches; **18,534** pin/corner reconciliations, **360**
  selected-path witnesses, and **1,920** write-interface witnesses. All **72**
  local matched clock comparisons are unchanged. Minimum pin access passes,
  with zero standard-cell/macro no-access counts.
- **Validation:** **471 passed / 2 skipped** portable tests. Regression coverage
  includes per-bit SRAM address capacitance overrides, explicitly absent macro
  fanout limits, malformed report-section rejection, and six signal-branch
  identity/geometry tests. Initial analysis rejections, a premature verification
  startup and the router/grid consistency rejection remain recorded.
  Final review reproduces and fixes a bus-pin cache-key regression; all five
  comparisons reproduce with the corrected reader, without another CAD run.
- **Resources:** twelve settled CAD containers, **429.640 seconds**, under the
  1,500-second cumulative bound; two incremental variants and two complete
  reroutes, two CPUs and 2 GiB. The preceding **169.993 seconds** remain recorded,
  for **599.633 seconds** combined. No timeout; all containers are absent.

The [manifest](../../physical/experiments/sram-distribution-results.json) binds
`build/validation/sram-distribution-01/report-02.json`, **1,943** retained source
versions and **2,240** artifacts. Report SHA-256:
`e8e27a51df68bf84e1f7ad4a6a06bb96b0ffdf7c764bc32cd623495f66aa4b30`.
The original `report.json` and its first manifest remain retained; the amended
report adds final-reader regression and reproduction evidence.

**Decision:** retain the improved candidate and the joint read/write timing
method; address the newly weak control families and fresh bit-53 setup path
before another qualification attempt. Global-route estimates, minimum pin
access, Lean interpretation and final layout remain separate evidence layers.
The fast-corner cell/SRAM temperature mismatch is unchanged.

## 2026-09-26 — Control distribution and competing read paths

Completed the authorized [control-distribution follow-up](../physical/control-distribution-experiment.md).
The initial scope expands the preceding 1,252 connections to 1,298, including
complete affected families and fresh read-path wires. An unchanged complete
reroute reproduces every baseline measurement, selected/write-interface path,
and stored routing-grid value.

- **Four added buffers:** local setup improves **+0.321638 → +0.556623 ns**,
  all **1,302** connections meet the 20% reserve, and global electrical counts
  are zero. Complete routing falls to **+0.063407 ns setup**, creates two
  capacitance failures and raises router overflow **16 → 20**. Hold improves
  to **+0.101286 ns**. The original targeted wires retain their margins.
- **Seven added buffers:** a fourteen-connection/two-path supplementary
  collection precedes three further edits. All **1,319** local connections pass
  reserve, but setup reaches only **+0.116998 ns**, below +0.367343 ns. The
  exact newly targeted bit-53 path improves **+0.063407 → +1.433723 ns**;
  another mux output driving two consumers about 800 µm away becomes limiting.
  This variant has no complete-route result.
- **Size and identity:** additions cost **85.2768 / 146.9664 µm²**, with
  historical allowance overages **489.120163 / 550.809763 µm²**. Original logic,
  state, cell placements, clock/hold cells and macro/power bindings survive
  actual database and independent Verilog readback checks.
- **Evidence:** **23,505** load reconciliations, **624** selected-path witnesses,
  **2,304** write-interface witnesses and **108** unchanged matched local clock
  comparisons. All 64 SRAM write-data inputs retain the hold floor. Minimum pin
  access passes for the completed four-buffer route. **471 tests pass / 2 skip**.
- **Congestion:** the new complete candidate's **20/20** router/grid totals and
  twenty native markers reconcile exactly. The baseline's **16/15** difference
  remains: pinned source shows that saved grids combine directional usage while
  router overflow is directional and native markers are 2-D. An unmatched 2-D
  marker cannot establish the precise extra Metal4 3-D edge.
- **Execution error and repair:** a failed local timing gate was followed by
  an erroneous repeat control launch using the original baseline. It was stopped
  after **20.567 seconds** with no final database and unchanged source. Its
  failed receipt is preserved. A run-local guard now rejects missing candidate
  stages before output creation or Docker; both edit/route rejection checks pass.
- **Resources:** twelve attempts, eleven successful and one interrupted repeat
  control, consume **419.640 seconds** of the 1,800-second bound. Two local
  variants and two complete coarse routes finish. All containers are absent;
  no timeout, detailed route or backend promotion. Cumulative regional/SRAM/control
  CAD time is **1,019.273 seconds**.

The [manifest](../../physical/experiments/control-distribution-results.json) binds
`build/validation/control-distribution-01/report.json`, **2,003** retained source
versions and **2,311** artifacts. Report SHA-256:
`e09f10703140902cb23b825584d2918ba1a7327e7881a7470a995c8ccf9b4188`.

**Decision:** retain the preceding 34-buffer SRAM design as the physical
starting point. Reject qualification of these two variants. Compare coordinated
placement and distribution of the status/decode region, measuring competing
paths and clock delivery together. The placement hypothesis is untested; formal
interpretation, coarse-route estimates and final layout remain distinct.

## 2026-09-26 — Coordinated status and decode placement

Completed the authorized [regional placement experiment](../physical/status-region-placement-experiment.md).
It permits **1,226 combinational cells** to move together while fixing the other
10,076 instances. The inventory expands to **4,199 connections / 2,190 complete
transport families**. An unchanged full reroute reproduces baseline measurements,
paths and routing grid. Both completed candidates preserve independently checked
cell/connectivity identity, row definitions and placement statuses.

- **Local versus complete routing:** coordinated placement improves local slow
  setup **+0.321638 → +1.195870 ns**, with unchanged +0.089025 ns hold and no
  added area. Complete routing regresses to **+0.181782 / −0.082617 ns**,
  creates **four hold and four capacitance violations**, and raises router/grid
  overflow **16/15 → 20/19**. Three capacitance failures are in scope; the fourth
  is SRAM output bit 11. The limited first placement pass also fails its
  complete-route setup comparison at +0.299410 ns.
- **Mechanism:** the new worst hold path's cells never move. An exact comparison
  attributes **180.005 ps** of its **232.458 ps** margin loss to changed launch
  and capture clocks. The original read path's local-to-full-route loss instead
  comes mainly from data delay. Minimum pin access passes on both full candidates;
  all SRAM write-data inputs retain their hold floor.
- **Evidence:** **75,582** load reconciliations, **576** selected-path checks,
  **2,304** SRAM write-interface checks, **90** targeted branch witnesses,
  **six** new exact hold witnesses and **96** unchanged matched local clock-pair
  comparisons. The **2,304** unrestricted regional witness records include
  repeated paths. The complete portable suite passes **478 tests / 2 skips**.
- **Execution and resources:** eighteen CAD attempts, fifteen successful and
  three rejected/failed, consume **927.689 seconds** of the unchanged
  1,800-second bound. Four edit attempts produce two candidates; three full
  routes complete. The input-hash rejection, two native placer failures and
  empty-row checker correction retain their original evidence and recoveries.
  All eighteen containers are absent; no timeout occurs. Cumulative regional,
  SRAM, control and placement CAD time is **1,946.962 seconds**.

The [manifest](../../physical/experiments/status-region-placement-results.json)
binds **3,473 artifacts / 2,904 retained source versions** and
`build/validation/status-region-placement-01/report.json`, SHA-256
`b841063f537ad665c35165d8f1b9f46be54e871f00953212e5469ba28ae881dd`.

**Decision:** reject both placement candidates; retain the preceding 34-buffer
SRAM design. Area stays **359,776.2816 µm²**, including the recorded
**403.843363 µm²** historical-allowance overage. Next test placement, routing
and timing/electrical repair together, with explicit clock and hold treatment.
That comparison remains untested. No RTL change, new Lean theorem, detailed
route, extracted timing closure or backend promotion follows.

## 2026-09-26 — Coupled placement, routing and native repair

Completed the authorized [coupled-flow comparison](../physical/routed-repair-experiment.md)
on the retained 34-buffer reference and coordinated placement. Both use
legalization, a complete route, native all-corner electrical/setup/hold repair,
legalization and another complete route. The saved flow had both post-GRT
repair flags disabled; the experiment uses a separate recorded recipe.

- **Result:** coordinated repair reaches **+0.571241 ns setup / −0.018681 ns
  hold**, with zero reported capacitance/slew/fanout violations and **13/12**
  router/grid overflow. Two hold violations and six timed-net reserve
  shortfalls remain. The same flow on the reference yields **+0.178522 /
  −0.022618 ns**, three capacitance failures and **27/27** overflow.
- **Attribution:** initial legalization flips 3,410 / 3,000 original cell
  orientations without moving their coordinates. Prepared setup is +0.148800 /
  +0.460087 ns, so the final improvement cannot be attributed only to added
  buffers. The coordinated repair fixes the old hold witness to +0.462381 ns;
  two other paths become limiting after full routing.
- **Actual changes:** reference repair adds five buffers and resizes three
  gates, +127.0080 µm². Coordinated repair adds six buffers and two delays,
  +174.1824 µm², with no gate resizing. Its total **359,950.4640 µm²** is
  **578.025763 µm²** above the historical allowance. Independent signal,
  all-corner function, geometry, row/status and power checks pass. Clock
  topology remains fixed; runtime clock-rule relaxation and changed routed
  delays remain explicit. Both minimum pin-access checks pass.
- **Tool boundary:** a +0.20 ns hold-target continuation fails with an empty
  insertion-load set on `ui_in[6]`. One recorded recovery skips nets with only
  protected loads, but the failure recurs on `_12274_/Q`, whose source net has
  protected and editable consumers. The pinned implementation filters
  protected loads after selecting a timing subset. Neither attempt produces a
  final candidate; partial optimizer output supplies no success claim.
- **Evidence:** four three-corner collections, **130,671** load reconciliations,
  **432** selected-path checks, **1,536** SRAM write-interface checks and **72**
  targeted branch witnesses. Constant ties are separately counted without
  claiming absent limits pass. The portable suite passes **485 tests / 2 skips**,
  plus four run-local inventory tests and seven launch guards.
- **Resources:** twelve CAD attempts, ten passed and two failed, consume
  **1,427.573 seconds** of the unchanged 2,400-second cap. Four edit attempts
  produce two first-pass candidates and no completed continuation. Six full
  routes finish; eight reservations conservatively count both failures.
  All twelve containers are absent; no timeout occurs. Combined retained
  regional/SRAM/control/placement/repair CAD time is **3,374.535 seconds**.

The [manifest](../../physical/experiments/routed-repair-results.json) binds
**2,229 artifacts / 2,122 retained source versions** and
`build/validation/routed-repair-01/report.json`, SHA-256
`56b5475fa26511822828d745e5b6486ad2db18e3df0fd2c1fb1453be427cc5b5`.
Earlier manifests and reports remain unchanged.

**Decision:** retain the coordinated repaired checkpoint as the leading
experiment and the 34-buffer source as reference; reject physical
qualification. Fix and test the pinned empty-load hold-insertion behavior
before a bounded hold/clock-aware continuation and final complete-route
remeasurement. Nonzero congestion and the 13/12 discrepancy also remain open.
No RTL change, new Lean theorem, extra pipeline cycle, complete compiler/package
refinement, detailed route, extraction or backend promotion follows.

## 2026-09-26 — Tested native hold fix and coordinated continuation

Completed the authorized [hold-fix continuation](../physical/hold-repair-experiment.md)
from the preceding coordinated repaired checkpoint. A one-condition patch
excludes protected pins when selecting failing hold loads, before slack/load
calculation and insertion. An isolated extension uses the exact pinned
OpenROAD revision and resident objects; the default image is unchanged.

- **Native evidence:** 12 checked executions cover all-protected loads, mixed
  passing/failing branches and an unprotected control. The original executable
  and unchanged extension reproduce six empty-load failures; the patch
  preserves protected connections, repairs the editable branch and produces
  an identical control netlist, geometry and timing. Failed fixture setup and
  compiler configuration attempts remain in the evidence lineage.
- **Result:** final setup/hold is **+0.382789 / +0.143801 ns**, clearing both
  retained floors, with zero reported capacitance, slew or fanout violations
  at all three corners. Both preceding negative hold paths clear and all 64
  SRAM write inputs retain their hold floor, minimum **+0.145047083 ns**.
- **Remaining gates:** five timed nets miss 20% reserve; **25/25** router/grid
  overflow remains. All 25 native markers reconcile strictly, improving the
  accounting boundary without removing congestion. The preceding checkpoint
  has lower congestion, at 13/12, but negative hold. Setup cushion above its
  retained floor is only **15.446 ps**.
- **Actual changes:** 90 delays and six buffers, no original resizing,
  **+1,632.9600 µm²** relative to the input. Total area is **361,583.4240 µm²**,
  including a **2,210.9857632 µm²** historical-allowance overage. Independent
  checks preserve all 11,310 originals, 3,732 protected cells, clock/power
  topology and final placement statuses; 125 original cells move legally.
  The optimizer's rollback-reset counter reports 37 hold buffers, so actual
  readback supplies the count and insertion-budget check.
- **Attribution:** the initial unchanged-circuit reroute already reaches
  **+0.518838 / +0.100468 ns**, but introduces two capacitance failures at every
  corner, two slow-corner slew failures and 25 overflow. Repair and final
  routing clear those electrical failures, add 43.333 ps hold cushion and
  spend 136.049 ps setup. Neither the patch nor new buffers alone explain
  the complete before/after timing gain.
- **Checks/resources:** two fresh three-corner collections, **65,652** load
  reconciliations, **264** selected-path checks and **768** SRAM write checks.
  **486 portable tests / 2 skips**, eight focused repair tests included, and
  four launch guards pass. Four CAD stages take **604.601 seconds**, producing
  one candidate and two full routes; no timeout and all containers absent.
  Combined retained CAD time is **3,979.136 seconds**. Compiler invocations
  total 20.542 seconds and native fixtures 8.234 seconds, separately recorded.

The [manifest](../../physical/experiments/hold-repair-results.json) binds
**17,343 artifacts / 1,002 retained source versions**, including the exact
dependency headers, binaries, failed checker and `buf_16` support revision.
Report `build/validation/hold-repair-01/report.json` has SHA-256
`7616001e95b92b3139519132d56f4527ac97cd181ab39985f49c42c3a365a691`.
Earlier reports and manifests retain their hashes.

**Decision:** keep the new result as the timing reference and retain the
preceding coordinated layout as the lower-congestion comparison. Next
diagnose and reduce the 25 reconciled Metal3 markers and five reserve
shortfalls while preserving both timing floors, protected cells and SRAM
write timing. Physical qualification remains open; no RTL/Lean change,
pipeline cycle, detailed routing, extraction or backend promotion follows.

## 2026-09-26 — Reject routing-policy changes and retain the saved hold repair

Completed the authorized [routing-policy follow-up](../physical/routing-policy-experiment.md)
from saved ODB `596a2c51189bc3e0abaed68103839973c3043842013787ecde5c3bbd8c6f2114`.
All 11,406 cells, placement/status, connectivity and area remain unchanged.

- An unchanged-policy complete reroute yields **+0.451521 ns setup /
  +0.151566 ns hold**, **29** reconciled congestion units, one capacitance
  violation per corner and seven slow-corner slew violations. Four of the
  original five weak nets recover reserve, but a different net fails and
  `_05213_` falls to 1.240% reserve. `_04558_` wire load grows from
  0.155683 to 0.335212 pF with unchanged pin loading.
- The proposed half-tile grid offset only translates **124,888 guide
  rectangles**; saved grid coordinates, capacity and usage stay identical.
  The pinned source applies this option when saving guides. Reject this
  discriminator without claiming true grid realignment cannot help; omit
  fresh shifted-checkpoint STA.
- A pre-recorded one-variant continuation gives worst-slack 30% routing
  priority. It yields **+0.376218 / +0.160825 ns**, **40** reconciled congestion
  units and the same electrical violation counts. Six nets miss reserve and
  one fails. It preserves both timing floors and all 64 SRAM write hold floors,
  but leaves only **8.875 ps** setup cushion. The router additionally disables
  the clock input's special routing rule during execution.
- Two three-corner collections reconcile **65,940** loads, **264** selected
  paths and **768** SRAM write-interface paths. Constant ties without reported
  limits remain separate from timed passes. Minimum pin access, **53 focused
  tests**, four launch guards and independent readbacks pass. Two helper setup
  failures and their corrections remain recorded.
- Eight CAD stages take **677.018 seconds**, including all three complete
  routes, with no timeout and all containers absent. The recorded continuation
  increases the route allowance from two to three while keeping the total
  CAD cap at 1,700 seconds. Cumulative recorded CAD time is **4,656.154 seconds**.
  Area stays **361,583.4240 µm²**, **2,210.9857632 µm²** above the historical
  allowance.

Reject the routing policies and retain the preceding hold-repair checkpoint
with zero electrical violations and 25 congestion units. Next establish an
unchanged import/incremental-routing control, then a bounded local signal
repair preserving successful clock routing. A partial incremental grid cannot
stand in for whole-chip congestion accounting. No detailed routing, tool-default
change or backend promotion.

The [manifest](../../physical/experiments/routing-policy-results.json) binds
`build/validation/routing-grid-01/report.json`, SHA-256
`0d0090d5cba39aa820cf790d135c9514ad727fd32fe0b9987b3e32406d3a2360`,
with **1,606 artifacts / 1,521 retained source bindings**. Manifest SHA-256:
`e23109cbb5dd9b4645f8f7d06fa34286aaece1971dffe0c64ce884b627c408b9`.
Earlier reports and manifests retain their hashes and verdicts.

Independent post-seal audit `build/validation/routing-grid-audit-02.json` passes
**5,867 hash references / 1,616 unique files**, including seven historical
reports. Its initial helper assumed only the newer object-shaped report
reference; the revision also reads older explicit path/hash fields. Neither
attempt changes any sealed artifact. Updated local links and `git diff --check`
pass.


## 2026-09-26 — Saved-route import controls

Completed `incremental-repair-01` from the retained hold-repair checkpoint,
ODB SHA-256 `596a2c51189bc3e0abaed68103839973c3043842013787ecde5c3bbd8c6f2114`.
The [study](../physical/incremental-routing-import-experiment.md) and
[manifest](../../physical/experiments/incremental-routing-import-results.json)
record a failed prerequisite; no signal candidate was attempted.

- Importing before incremental initialization preserves routes but erases
  demand: router/grid overflow falsely becomes 0/0 while 25 stale native markers
  remain. Reversing the order restores 25/25/25 overflow with strict marker
  reconciliation, but changes 79 Metal2 capacity entries and loses 83 units of
  clock-rule demand. Both controls preserve all 11,342 routed nets, 342 clock
  routes and every original instance/placement.
- Fresh measurements on the second control reproduce every parsed connection
  and selected/write path record: **+0.382789 / +0.143801 ns**, zero electrical
  violations, five reserve shortfalls and all 64 SRAM write hold floors passing.
  Coverage is **32,970** load checks, **132** selected paths and **384** write
  checks. The 1,790 constant ties remain separately counted.
- Added complete-grid and native-segment identity checks with 12 regressions;
  **65 focused tests** and **six launch guards** pass. The first analysis failed
  on stale markers; its retained successor records the rejection explicitly.
  No native patch, default tool change, Lean/RTL edit or added area follows.
- Five CAD stages use **168.145 seconds** under the 1,800-second allocation:
  two incremental controls, zero full routes/candidates/timeouts. All five
  containers are absent. Cumulative CAD time is **4,824.299 seconds**.
- Sealed report: `build/validation/incremental-repair-01/report.json`, SHA-256
  `2fc57afea2642eb214a06dc75265bea2c4e33ee4bc7648e27555205fcf3215f6`;
  **1,057 artifacts / 1,071 source bindings**. Prior reports remain unchanged.

Retain the prior checkpoint. Repair effective clock-rule costs and repeated
macro-access initialization, and qualify old-route removal through an edit/revert
control before the local signal repair. This is a tool-state finding, not a new
physical improvement or chip qualification.


## 2026-09-26 — Qualified route import and a preserved-clock signal repair

Completed `route-import-fix-01` from the retained hold-repair database,
SHA-256 `596a2c51189bc3e0abaed68103839973c3043842013787ecde5c3bbd8c6f2114`.
The [study](../physical/route-import-fix-experiment.md) and
[manifest](../../physical/experiments/route-import-fix-results.json) retain the
one-buffer candidate as the next experimental checkpoint.

- The pinned native adapter restores effective clock-rule costs and per-net
  removal records without repeating macro-access capacity. Exact no-edit and
  actual buffer edit/revert controls preserve all 11,342 source routes,
  126,729 segments, 342 clock nets and 174,035 checked 2-D/3-D resource edges.
  Ordinary, active-NDR and relaxed-NDR removal controls pass. The second native
  build corrects a stale derived overflow scalar; its two repeated controls
  reproduce the measured candidate's intermediate circuit and resource state.
- One `buf_4` beside `_08031_` changes only `_04215_` and its new branch.
  All 11,406 old cells, positions, row/status records, clock routes and capacities
  remain fixed. Slow target slew improves **2.081871 → 0.355251 ns**; weak
  connections fall **5 → 4**. Global setup/hold remains
  **+0.382789/+0.143801 ns**, with zero reported electrical violations and all
  64 SRAM write hold floors passing. Local hold falls **0.395976 → 0.210800 ns**,
  still positive; local slow setup gains **1.246193 ns**.
- The complete 10,991-net inventory yields **32,973 load, 132 selected path and
  384 write checks**. Constant ties remain separately counted. All **25**
  congestion units reconcile across native accounting, saved grids and markers;
  minimum pin access passes. Added area is **14.5152 µm²**, total area
  **361,597.9392 µm²**, historical allowance overage **2,225.5009632 µm²**.
- **79 focused tests / ten launcher checks** pass. Eleven CAD stages consume
  **336.314 seconds**; two native builds consume **6.100 seconds**. Cumulative
  CAD time is **5,160.613 seconds**. No full reroute or CAD timeout occurs;
  all thirteen containers are absent. The first comparison's overly strict
  identical-slew assumption is rejected and retained; its successor checks six
  propagated downstream slew changes. A sealer list/dictionary handling error
  is retained with its recovery before any final report was produced.
- Sealed report: `build/validation/route-import-fix-01/report.json`, SHA-256
  `50ba42ec4cc7830fa3cd898b1843c188082befdf64936153fcf2476337c76cdb`; **2,542 artifacts / 2,409 retained source bindings**.
  Manifest SHA-256: `2df8e2f3a66d81a1469afec1a718d5d1413326a06301f52d3f2960fbdf79b75b`.
  Candidate ODB SHA-256: `ea546b4e6a159d56e26e02329afcc8f18d54b69152e20097b2d39977b405cbd6`.
  The sealed parent source/header bundle is checked across **16,227 files**.

Retain this candidate and the prior hold-repair reference. The next bounded
question is a consumer partition for the weakest remaining signal `_01876_`.
Four reserve shortfalls, coarse congestion, detailed routing and final layout
checks remain open; no Lean theorem, RTL change or backend promotion follows.

Independent post-seal audit `build/validation/route-import-fix-audit-01.json`
passes **26,223 hash references / 18,785 unique files**, including all
16,227 external dependency files and nine historical reports. The report and
manifest retain their sealed hashes; prior receipts and verdicts are unchanged.
Updated documentation file links and `git diff --check` pass.

## 2026-09-26 — Complete iteration: routed A, checked images, bounded timing failure

The [plan](complete-design-iteration.md) moved through its initial audit and
bounded physical allocation. The [layout study](../physical/design-iteration-experiment.md)
and [image certificate](../storage/paired-image-certificate.md) own details.
**Reference A is not accepted; B and clean-source physical replay remain open.**

- The audit checks 3,551 unique inputs and regenerates the retained RTL. One
  2,122.352-second full-flow continuation completes detailed routing, extraction,
  antenna/connectivity and LVS. Extracted slow setup is −3.190857 ns; maximum
  cap/slew/fanout violations are 34/94/66.
- Magic initially reports 230,225 markers, all inside the SRAM rectangle. A
  54.520-second control imports the exact same GDS flat and passes all original
  full DRC rules with zero errors. No geometry edit, macro blackbox or waiver.
- Fresh wire-capacitance analysis explains the failed transfer from coarse
  estimates. The first calibrated repair fails on a protected-load insertion;
  its control and the final editable-signal-input configuration complete. Both
  pass independent function/geometry checks but fail physical admission. The
  last has −2.571731 ns slow setup, four slew violations and 202 coarse overflow.
  It adds 305 cells/resizes six, for 368,178.7680 µm² total functional area.
- Final routed-netlist readback preserves original signal logic after explicitly
  accounting for 151 antenna and 46,659 signal-free fill/decap cells. The actual
  netlist passes 331,401 package-pin edges. The initial antenna-only census
  rejection is retained separately.
- New Lean image/dispatch theorems check exact canonical source bytes and
  290-word uploads, preserving every finite successor-choice history. Six
  positives and ten kernel-proved corruptions pass. The paired host adds eight
  certified uploads on byte-identical A RTL, including pin-only protocol peers
  and malformed-upload recovery; each upload costs 85,285 modeled chip edges.
- Foundation: 207 modules, 15,471 declarations / 7,733 theorems, standard axioms
  only, 32 executable suites, 1,414.395 seconds. Python: 510 tests pass with two
  skips. The image gate takes 248.470 seconds; the host demo takes 105.097 seconds.
- Charged CAD/check time is **2,640.603 seconds**, including failed work and
  conservatively the entire host demo. Three configurations and one A full-flow
  attempt are used. All owned containers are absent; the second A route is
  preserved. No commit, publication, paid compute or fabrication occurs.

Campaign manifest: `physical/experiments/design-iteration-results.json`, SHA-256
`bb03efe9b71d1ea9e82f17dcf1b69b39c1f39428029cd703bfcaac5545d213ab`. It binds 21 reports, final artifact identities and the resource
ledger. Proof of timed controller/loading/package/RTL correspondence and a
qualified fast corner remain missing. The next hypothesis is to specialize
upload-validation parameter lookup away from execution lookup, prove its exact
equivalence, then check removal of SRAM Q from the rejection cone. That change
and a timing exception have not been implemented.

Closeout audit `build/validation/design-iteration-01/closeout-audit.json`,
SHA-256 `7989c18cfaf169e4649d3ee49bd3728b81d152a665ca163117ca4e175583c9cc`, passes 28 top-level bindings,
652 physical artifact references, 216/224/284 current image/host/foundation
source bindings and 616 local document links. A final Docker inventory finds
no campaign containers; `git diff --check` passes.

## 2026-09-26 — Validation isolation: equivalent circuit, rejected coarse layout

The separately approved [architecture experiment](../physical/validation-isolation-experiment.md)
adds an opt-in upload-only inactive-bank lookup. The old controller remains the
comparison and default. The 290-word image, 32-record capacity, state, package,
20 ns clock and execution edges are unchanged. No timing exception is added.

- `PairedValidation.isolatedPush_correct` proves the changed local expression
  under the original upstream equations. The foundation build/audit passes
  **15,556 declarations / 7,794 theorems**, standard axioms only. Four state-intake
  corruption tests pass. Whole-graph/emitter/closed-paired refinement remains open.
- `paired-validation-check-06` passes baseline byte reproduction, complete
  core/package arbitrary-state SAT, both mapped corners, 173,359 core edges and
  331,401 package edges / 1,517 frames on both RTL and mapped cells. SRAM-to-rejection
  reachability is absent. Typical mapped area rises **18,502.7976 µm² / 6.1219%**
  to 320,742.0360 µm²; slow cell-only setup improves **+3.93 → +7.99 ns**.
  The five failed checker attempts and their causes remain recorded.
- Exact physical import, macro placement and power checks pass. Placement, CTS
  and initial hold repair finish. Strict routing is stopped; the congestion-retaining
  retry times out at 600 seconds. Pinned source inspection corrects the runtime
  explanation: soft NDR relaxation restarts the routing iteration counter, and
  allowing congestion does not suppress those restarts.
- A fresh control removes exactly ten clock-width rules while preserving the
  exported circuit and all placement/package/power context. Its first coarse
  route completes with **8,911 overflow**. Subsequent repair is stopped; the
  completed first route is the sole selected checkpoint, not an optimized result.
- Independent fresh corners report slow setup **−9.286980 ns**, fast-screen hold
  **−0.409959 ns**, and maximum corner cap/slew/fanout violations **224/1,103/0**.
  All consumed nets have wire estimates; 198 unused unannotated drivers per
  corner are reconciled. The fast temperature mismatch remains unqualified.
- The actual saved circuit passes SAT over all original **1,572 FFs / one SRAM**,
  all 5,000 sequential input bits including clocks/resets, and package outputs.
  Hidden-state and inverted-clock controls fail as intended. It also passes
  **331,401 external-pin edges / 1,517 frames**. Fresh OpenDB target and geometry
  checks pass. SRAM-to-rejection is absent in both the graph and timing reports.
- The new worst slow path runs from `r_active[0]` to `r_cached[10]` through nine
  small buffers already in the mapped source. This motivates a matched physical
  control-distribution comparison. It does not prove lookup duplication alone
  caused every regression, or that the architecture cannot be implemented.
- Placed cell/SRAM area is **376,176.6432 µm²** in the unchanged 6×4 outline,
  **16,804.2049632 µm²** above the historical experimental cell-area allowance.
  Charged CAD/check time reaches **4,080.913 seconds**, including all failed
  work and the earlier phase. This extension uses **1,440.310 seconds**.
  All owned containers are absent; no new full-flow attempt is used.

Manifest: `physical/experiments/validation-isolation-results.json`, SHA-256
`294eee4f27152f7a7074ee6f556e68794fe5b2bb5f3524e1ca844d8c3e1887fb`.
Retain the architectural proof and circuit. Do not admit this unrepaired coarse
layout to the remaining A full route. A/B acceptance, complete refinement and
clean-source physical replay remain unfinished.

Closeout audit `build/validation/paired-validation-isolation-01/closeout-audit.json`,
SHA-256 `4cb13d43eb7c6cb58099a6ec3156da2d2309a43a88113f93fbb41f5aa4645709`,
passes 1,624 hash references / 1,250 unique files and 618 local document links.
The resource ledger reconciles; a final Docker inventory finds no owned
containers, and `git diff --check` passes.


## 2026-09-26 — Balanced distribution clears coarse congestion

Completed the approved [control-distribution experiment](../physical/buffer-balance-experiment.md)
on the same verified isolated-validation RTL and nonbuffer mapped logic.
Maximum positive-buffer tree depth falls **8 → 2**, with 105 additional buffers
and **762.0480 µm² / 0.2376%** mapped area. The actual placement coordinates from
the preceding failed layout guide spatial leaf grouping; fresh placement and
CTS determine the new implementation.

- Both mapped-corner SAT comparisons, an inverted-buffer negative and 331,401
  package-pin edges pass. Five new balancing tests and twelve existing
  distribution tests pass; no Lean source or default-backend change.
- Matched initial-route comparison: overflow **8,911 → 0**; slow setup
  **−9.286980 → −0.982379 ns**; slow cap/slew/fanout **217/1,103/0 → 23/90/0**.
  The prior post-route repair was stopped and remains a separate result.
- The new repair **completes**, adding 92 buffers and eleven hold delays,
  resizing one gate, and moving 145 original cells within checked legal sites.
  Whole-chip slow setup/hold becomes **+0.820730/+0.326675 ns**; fast-screen hold
  is **+0.040186 ns**. Coarse overflow remains zero. Four cap and 23 slow slew
  violations remain on seven nets.
- Independent checks reconcile both saved routing grids, require complete wire
  estimates for consumed nets and preserve package/macro/power geometry and
  clock topology. Both actual circuit exports pass FF/SRAM-input/package-output
  SAT and 331,401 pin edges each. Hidden-state and inverted-control mutations
  fail. SRAM-to-rejection reachability stays absent.
- Final area is **374,556.3840 µm²**, **15,183.9457632 µm² / 4.2251%** above the
  historical cell-area allowance, on the original 6×4 outline. That comparison
  allowance is not a competition die limit. Fast cell/SRAM temperatures remain
  mismatched; no new detailed routing, extraction or layout signoff is claimed.

The first intake rejects the non-allowlisted clock-rule override before CAD.
Its failed receipt remains. The corrected standard intake reaches CTS, followed
by the independently checked ten-rule clock-width-only copy used for the matched
comparison. The mapping/guidance policy, physical recipes, both saved stages,
actual checks and failed intake are hash-bound in
`physical/experiments/buffer-balance-results.json`, SHA-256
`47529b6eaa0a1cc200ff80c6e1d018559028dd7b899d345201dbdcef9ea1cc7e`.

Initial database:
`f7ce06f4360cc999d166cec8fe20178c163178f232a19afb2ae3dc44b6545c39`.
Completed repaired database:
`0bfe41e1e3ceabc1376160410ea45aa59ccf08a3a0e4c96d85e748aedd3a4ecc`.
The phase conservatively charges **276.538 CAD seconds**, for **4,357.451
seconds** cumulative. One A full-flow attempt remains unused. Retain the balanced
candidate, then address the seven measured electrical nets while preserving
clock topology and SRAM write hold. The native resizer already loads the
requested corners; a default-corner label change is not an established fix.
A, B and complete paired correspondence remain open.


## 2026-09-26 — Electrical screen closes; second A layout has positive extracted timing

Completed the authorized continuation through [seven-net electrical
repair](../physical/balanced-electrical-experiment.md) and the
[second allocated A detailed layout](../physical/balanced-detailed-experiment.md).

- Six buf_4 cells and one buf_2 add **96.1632 µm²**, clear all four cap and 23
  slow slew failures, and preserve original placement plus all 340 coarse clock
  routes. Slow setup is **+0.845816 ns**, fast-screen hold **+0.040186 ns** and
  conservative coarse overflow zero. Independent actual-netlist SAT, corruption
  controls, 331,401 pin edges and every SRAM write hold pass.
- The source-specific import loses one unit of saved usage at Metal3 `[21,72]`,
  with no capacity, circuit, route-segment or timing change. The strict rejection
  is retained. The admitted scoped screen counts that extra unit and prevents
  edited routes from using it; both native and conservative overflow remain zero.
  Removal/replay and actual edit/revert controls cover 174,035 resource entries.
  Terminal ordering alone required a corrected identity comparison.
- Detailed routing adds **118 antenna cells** and **45,931 power-only cells**.
  Full-rule Magic DRC, routing DRC, LVS, antenna and both power-grid connectivity
  checks pass. Original cells, placement and protected geometry are unchanged.
  Actual final signal identity, hidden-state/changed-clock rejections and
  **331,401 pin edges** pass.
- Fresh final-netlist/SPEF STA reproduces **+1.451337 ns slow setup** and
  **+0.020742 ns fast-screen hold**, with no slew violations. All 64 SRAM write
  holds pass; the fast-screen write minimum is **+0.118523 ns**. The SRAM-to-
  rejection path remains absent. The first A layout had −3.190857 ns extracted
  setup; this improvement reflects the combined architecture/distribution work.
- **A remains unaccepted.** All 14 fanout failures reconcile exactly to antenna
  inputs added to previously legal nets. The separate `paired_balanced_5_4_out`
  has no added diodes and reaches **0.307562 pF** against 0.300000 pF. All seven
  repaired nets remain clear. Fast views are still −40°C cells / −55°C SRAM;
  current upstream inventory and the macro datasheet do not close that bound.
- The flow exits successfully because its cap/slew enforcement defaults select
  no corners. The new `physical_timing_acceptance.py` requires every requested
  corner and rejects this final result. Five tests pass, including 21 distinct
  failed-corner/metric cases. Actual coarse receipts pass the same gate.

Retain the initial Python-module-shadowing failure, strict import rejection,
list-order comparison correction and failed fresh-STA `nom` SPEF mapping. The
latter is corrected to the flow's original `nom_*` key using the same extracted
file; its successful geometry readback and 3.421-second charge remain. Preflight
invocation accounting is corrected separately without omitting its elapsed time.
No native CAD code, PDK or Lean source changes in this continuation.

The electrical manifest is `physical/experiments/balanced-electrical-results.json`,
SHA-256 `0811c2a7fca7a570319ca038eea60c1a05cd62ba0bdeccc6e45a165dca994f1f`.
The detailed manifest is `physical/experiments/balanced-detailed-results.json`,
SHA-256 `2a93b522e236cfa67385b654eb083a0a2ce9da64c89bcb644da7bffc625dd7be`.
Final database: `9c4ef974bd865b875efa8dd356a96fa9bf4b3819667519fa204be1a37ac2aca3`.
Final GDS: `3ebb74dda57202b0caf2c73e310fa6a985705dd04a04727852fdd8fefd970fe3`.
Signal-cell/SRAM/antenna area is **375,294.8448 µm²**, with the historical
4.4306% overage recorded separately from the unchanged die and physical fill.

The full flow takes **413.996 seconds**. This continuation charges **568.830 CAD
seconds**, including controls, failures, final checks and fresh measurements,
for **4,926.281 seconds cumulative**. Both A full-flow attempts are now used.
Further physical work needs an explicit allocation; the next hypothesis should
account for antenna load before accepting a distribution repair. Fast-library
qualification and full paired refinement remain open; B is not admitted.

## 2026-09-27 — Antenna headroom loses to connecting wire capacitance

Approved one coordinated antenna-load plan and one additional A full-flow slot,
retaining the original two used A attempts, two reserved B attempts and eight-hour
aggregate limit. The [frozen protocol](../physical/antenna-load-experiment.md) and
[result](../physical/antenna-load-results.md) keep scope and outcome separate.
The [manifest](../../physical/experiments/antenna-load-results.json) binds all receipts.

The 41-buffer / 595.1232 µm² edit leaves at most three functional loads per parent
and leaf. Fifteen release/replay controls, exact edit/revert and readback pass;
all original placements and 340 coarse clock routes remain fixed. Arbitrary-state
SAT, hidden-state/control negative tests and 331,401 package-pin edges pass.
Zero conservative overflow, positive all-corner setup/hold and zero slew/fanout
failures survive the screen, but two new capacitance failures reject the candidate.

Fresh load measurements reproduce the calibrated-source and candidate metrics.
`paired_balanced_148_17_out` and `_03354_` have lower pin capacitance but wire
capacitance alone exceeds 0.300 pF; their routes grow by 475.2 and 511.2 µm.
The detailed-flow preparer refuses the rejected receipt before starting CAD.
No detailed layout or final antenna-effect measurement follows.

The nominal-RC diagnostic rejection and a subsequent worker syntax error are
retained and charged before the corrected calibrated comparison. Follow-up cost
is 126.399 CAD seconds; cumulative cost is 5,052.680 seconds / 84.21 minutes.
The additional A full-flow slot remains unused. Candidate allocation closes with
wire-aware transport placement as the next hypothesis, and unchanged fast-view,
formal-composition, A/B acceptance and clean-source replay obligations.

## 2026-09-27 — Transport repair survives extraction; remaining loads need a wider scope

Completed the approved [transport refinement](../physical/transport-split-results.md)
and existing third A full-flow slot. The [protocol](../physical/transport-split-experiment.md)
is frozen separately from the result. Two `buf_4` cells, selected from measured
routing trees, split `_03354_` and `paired_balanced_148_17_out` for
**29.0304 µm²**. All original cells and placements, the preceding 41 buffers and
340 coarse clock routes remain fixed; only four signal routes change.

Import/removal/replay and actual edit/revert controls pass. All 174,035 resource
entries reconcile with the inherited one-unit conservative reservation and zero
overflow. Arbitrary-state equivalence, hidden-state/control corruption checks,
331,401 pin edges / 1,517 frames, all-corner timing/electrical, all 64 SRAM write
holds and minimum pin access pass. Parent/child capacitance is below 0.240 pF
at every coarse corner, admitting the candidate without a second placement.

The final layout preserves all 12,232 source cells and adds 97 antenna and
45,905 power-only fill/decap cells. Independent final signal identity, negative
controls and the same package-pin replay pass. Fresh extracted STA reproduces
flow metrics exactly. Slow setup is **+1.229028 ns**, fast-screen hold
**+0.026968 ns**; all 64 write holds pass, with minimum fast-screen
**+0.112675 ns**. Routing/full-rule Magic DRC, all seven LVS counts, final antenna,
critical connectivity and power checks pass. KLayout DRC/XOR and flow EQY are
disabled and not counted as passes.

Both transport repairs remain below 0.240 pF after extraction. All preceding
14 fanout failures clear, but four different branches acquire protection inputs:
`paired_balanced_100_21_out` has 8+4=12; `paired_balanced_133_4_out`,
`paired_balanced_140_0_out` and `paired_balanced_19_5_out` each have 8+1=9,
against eight. The separate `paired_balanced_5_4_out` has no antenna inputs and
still reaches **0.303477 pF**, including **0.290461 pF** of wire capacitance.
Every corner reports **1 cap / 0 slew / 4 fanout** failures. Explicit native
all-corner cap/slew enforcement now makes the flow return failed after saving
the final views; the shared gate independently rejects cap and fanout.

The read-only inventory counts 905 signal nets with eight physical inputs
before protection; precisely the four new failures acquire antenna inputs in
this run. This supports comparing complete-network load reservation with bounded
repair after antenna insertion. It does not predict that all 905 require edits
or bound future antenna demand. Include connecting-wire load in the next scope.

Signal-cell/SRAM/antenna area is **375,804.6912 µm²**, with **491,412.0960 µm²**
fill/decap recorded separately. The useful-area comparison overage is
**16,432.2529632 µm² / 4.5725%**; the outline is unchanged. Against the preceding
detailed layout, useful area increases 509.8464 µm² and slow setup loses
0.222309 ns, while fast-screen hold improves 0.006227 ns.

The full route charges 444.182 seconds. Controls, circuit replay and final
inspection bring this continuation to **600.042 CAD seconds** and the campaign
to **5,652.722 seconds / 94.21 minutes**. All scoped containers are absent.
All three A full-flow slots are consumed; two B slots remain reserved behind
accepted A. No new routing slot or physical qualification follows. Fast-view
qualification, complete paired refinement and clean-source A/B replay remain open.

Manifest: `physical/experiments/transport-split-results.json`, SHA-256
`b2caf796124739d5c450d73437053afaae32b689756ae509424afceac64f086c`.
Final database: `a74f4a35aa1c2baf1a37c86df55081c94873106afac64ea2679329d04c6c1ad1`.
Final GDS: `e1decb4f9ea5a73692effd6da2d517e28708e4630bdfa9192d2b2f8a8a578455`.
The manifest binds both candidate stages, independent final checks, all receipts
and the full load inventory. No Lean, PDK or native CAD code changes in this turn.

## 2026-09-27 — Closure policy costs and the native restart boundary

Completed the authorized [protection/electrical assessment](../physical/protection-closure-results.md)
under a [separate frozen protocol](../physical/protection-closure-experiment.md).
The current third-A layout and all preceding artifacts remain unchanged.

An explicit additive policy keeping at most four functional receivers per driver
would affect 1,044 signal nets and require at least 1,949 buffers / 14,145.0624 µm²
using the smallest admitted buffer. A three-receiver policy affects 2,266 nets
and requires at least 4,143 buffers / 30,068.2368 µm². These are count/area lower
bounds with original cells retained, not layouts, optimal remappings or guarantees
of future antenna demand. Defer blanket insertion while qualifying repair after
actual protection is present.

The native probe uses the third layout before fill, with unchanged extracted
SPEF and libraries. Readback matches all 12,329 source cells, original placements,
signal connectivity and fixed geometry to the final layout, excluding its 45,905
power-only fill/decap cells. The first invocation rejects an unsupported
`report_worst_slack -corner` flag before repair and charges 6.006 seconds.

The corrected invocation reproduces the same four fanout failures and one cap
failure in all three corners with zero slew failures. It then crashes with
signal 11 in `GlobalRouter::getPinGridPositions`, reached through
`Resizer::makeBufferedNetGroute` and `RepairDesign::repairNet`. Matching pinned
source shows that the selected detailed-routing estimator uses the global-router
net/pin map, which this database/SPEF restart did not initialize. Its 4.642-second
receipt and pre-edit readback are retained. No candidate database/netlist is
emitted, so no candidate circuit, routing or timing checks are counted as passes.

The next proposed integration test keeps native routing state live and starts
with a small routed fixture, an unchanged control and an actual buffer edit.
Protect antenna ownership and clocks, verify circuit/resource changes, then
reroute and re-extract before all final gates. An additional whole-chip attempt
remains conditional on that control and a new explicit allocation.

This assessment charges **10.648 CAD seconds**, bringing the campaign to
**5,663.370 seconds / 94.39 minutes**. Both scoped containers are absent and
input/artifact hashes verify. All three A slots remain consumed; two B slots
remain reserved. No full route, tool/PDK patch, Lean theorem or accepted A follows.

Manifest: `physical/experiments/protection-closure-results.json`, SHA-256
`fdad80939061f74afc524fa6fce082825c7108fcde15b091160201a003b02879`.
The full reserve inventory and failed native recipes are retained under
`build/validation/protection-closure-01/`.


## 2026-09-27: live protection/electrical fixture qualifies

Completed the authorized [live repair experiment](../physical/live-closure-results.md)
under its [frozen protocol](../physical/live-closure-experiment.md). The final
18-cell IHP fixture gains one explicitly grouped `buf_4` and four native wire
repeaters, adding 43.5456 µm². Its initial 12-against-8 fanout and fast extracted
0.366837472 pF against 0.300000012 pF both clear after rerouting and fresh RCX.
All three corners have zero cap/slew/fanout failures; worst fixture setup is
+14.107367 ns and worst hold +0.044568 ns. All 12 timed endpoints are covered
for minimum and maximum paths in every corner.

Independent readbacks pass known-buffer circuit contraction, original cell
geometry, four declared diode/receiver pairs, exact clock routes against the
no-edit DRT and extracted controls, every new power binding, complete signal
route/SPEF coverage, native routing DRC, antennas and zero grid overflow. Native
no-edit initialization is repeatable after its first detailed-wire accounting
conversion. A diode-locked native repair aborts; releasing locks produces a
logically equivalent candidate that breaks two declared pairs. That candidate's
antenna check passes, so this is a grouping-contract rejection, not an observed
antenna violation. Cap-only repair also leaves the measured failure; the
1,000 µm wire-length target creates actual repeaters. These search parameters
remain fixture-specific.

Retained failed controls include both decoder-interface fixes, a checker that
compared pre/post-RCX encoding, and a checker that caught missing new-buffer
power bindings. The final recipe reapplies global connections. The final
checker rejects actual ownership/capacitance failures, changed FF clocks,
missing parasitics and stale SPEF. No full-rule Magic DRC/LVS, SRAM or chip
physical qualification follows from this sparse fixture.

The prepared chip intake binds the exact third pre-fill layout/SPEF, five failing
nets, 97 antenna cells and 340 clock nets. Historical receiver ownership is not
inferred from numbered diode names or geometric proximity. Next qualify complete
runtime repair-tree coverage and an explicit grouping contract on the chip,
then a concrete candidate before another full route. No chip edit, fourth A
attempt or new Lean theorem occurred. Three A attempts remain used; two B slots
remain reserved; fast-view/refinement/A/B/clean-replay gates remain open.

All attempted CAD work and independent Yosys reads charge **26.259 seconds**,
bringing the campaign to **5,689.629 seconds / 94.83 minutes**. All scoped
containers are absent. Evidence: `build/validation/live-closure-01/`; qualified
recipe `fixture-06/`, independent receipt `checks-03/receipt.json`.

Manifest: `physical/experiments/live-closure-results.json`, SHA-256
`fb44d38a3d2284e623fe64dadf899fa27c9cb79e1863aabe49bf198a910ece2b`.

## 2026-09-27 — Checked electrical repair on the actual chip

The [chip integration](../physical/chip-closure-results.md) transfers the fixture
controls to the saved third A layout. Five buffers and one declared diode clear
capacitance/slew/fanout in all corners after fresh extraction; native DRC/antenna
are zero. Slow setup is +1.242753 ns and fast-screen hold +0.026979 ns.
All original placements and 97 antenna bindings remain, with 340 exact clock
wires through detailed routing, complete consumed-net parasitics, and 331,401
passing package-pin edges. Added area is 78.0192 µm².

The independent route check rejects an actual control with three missing clock
wires despite zero native violation counts. The final recipe invalidates only
the five declared signal parents, keeps the incremental pin-access callback
inactive during editing, and rebuilds resources from retained detailed wires.
Every failed recipe and wrapper error is retained in the
[manifest](../../physical/experiments/chip-closure-results.json).

This continuation costs 634.894 CAD seconds; cumulative charge is 6,324.523
seconds / 105.41 minutes of eight hours. Three A full-flow attempts remain used,
two B attempts reserved, no fourth A allocation. Final fill/streamout/full-rule
DRC/LVS, power/final extraction, fast-view qualification and complete paired
refinement remain. This is local chip integration, not accepted A or a new Lean theorem.

## 2026-09-27 — Final layout checks expose the SRAM extraction boundary

The [finalization](../physical/chip-finalization-results.md) adds 45,901 signal-free
filler/decap cells while preserving all 12,335 original instances, every original
wire encoding, 340 clocks and all 98 antenna bindings. Fresh extracted timing
remains +1.242753 ns slow setup and +0.026979 ns fast-screen hold, with zero
electrical violations. Full-rule Magic GDS DRC, antenna, power connectivity,
independent circuit readback and 331,401 package-pin edges pass.

**Final GDS signoff is rejected.** Switching extraction from DEF/LEF to the
actual GDS exposes 24 illegal overlap markers and failed LVS. The pre-repair
chip reproduces the same failures, and standalone extraction of the unchanged
SRAM reproduces every overlap after translation by its placement offset. The
standalone interface has 351 declared pins after spelling normalization;
in-chip extraction exposes an extra internal ground terminal. No error or pin
is waived. Native malformed JSON stops LibreLane, independently of its failing
text LVS result. The current DEF-based LVS control still passes.

Retain the filled repair and qualify the SRAM extraction/interface before
repeating GDS LVS. Fast characterization and complete timed Lean refinement
remain open. This continuation charges **387.202 CAD seconds**, including the
failed finishing/inspection attempts and all controls; cumulative charge is
**6,711.725 seconds / 111.86 minutes**. All scoped containers are absent. Three A
full-routing attempts remain used and two B slots reserved; no new A slot.

Manifest: `physical/experiments/chip-finalization-results.json`, SHA-256
`e7402496649dce51c91ec663c01e8333687fbfc93b973186f5b70049d02e25f1`.

## 2026-09-27 — SRAM interface passes; internal qualification remains open

The [bounded SRAM continuation](../physical/sram-extraction-results.md) leaves
the chip and PDK unchanged. Control-hierarchy import removes the extra SRAM
ground terminal; raw merge evidence already places it on VGND and declared VSS.
A bijective adapter changes 338 bus spellings across the complete 351-pin
interface. Native chip LVS reports a unique match and zero differences. Both
address-to-ground and ground-to-power mutations fail native pin matching; four
invalid interface inventories are also rejected. The schematic SRAM remains a
blackbox.

All 32 layers and 754,685 labels of the supplied macro are retained exactly in
the chip GDS. All 1,024 full-flat device warnings locate on the two grounded
edge-device gates in each of 512 cells. Full flattening clears isolated overlap
and conversion errors but chip extraction times out at 600 seconds. The practical
control import leaves two overlaps and 438 conversion diagnostics; original
reports had 24 and 522. No remaining error is waived.

Strict independent KLayout SRAM LVS fails. Native readback records 23 matches,
two nonmatches, five schematic-only mismatches and a skipped top comparison.
The diagnostics include a metal-resistor/LVSRES model disagreement and absent
NMOS extraction in a word-line driver. Flat-mode extraction times out at 400
seconds without a comparison result. Preserve these controls and use small
context fixtures before further chip routing.

All ten CAD invocations, including audit/API failures and timeouts, cost
**1,316.754 seconds / 21.95 minutes**. Campaign total: **8,028.479 seconds /
133.81 minutes**. All containers are absent, source identities retained; three A
slots used, two B reserved, no fourth A. Full signoff, SRAM internals, fast views,
complete refinement, accepted A/B and replay remain unqualified.

Manifest: `physical/experiments/sram-extraction-results.json`, SHA-256
`9fe2ebdc978c2c5d46070c7c0d33f1e8c22bcb37bcbe3bb897c5033cb6720392`.


## 2026-09-27 — SRAM failures isolated with neighboring geometry

The [context-fixture study](../physical/sram-context-results.md) retains the two
failing cells and their complete parent blocks as four tracked GDS fixtures.
Every exported polygon, label and internal transform is preserved. The source
inventory locates 256 word-line drivers and 12 delay dummies.

The 16-driver parent contains all 64 expected MOS devices and matches flat.
Deep extraction places its 32 NMOS devices in the parent while retaining the
PMOS devices in child circuits, reproducing the previous child-level failure.
The complete delay parent matches deep after translating only the dummy R0
model to metal1, retaining its original nodes and 0.600 × 0.260 µm dimensions.
Width, length and equal-ratio dimension mutations all fail, as do physical metal
opens, bridges and NMOS-gate removal. The unchanged mutation carrier passes.
Seven malformed or unsupported adapter inputs are refused.

Two limitations remain explicit. Flat delay comparison combines six schematic
resistors into one while retaining six layout resistors. Native simplification
also discards a disconnected declared output and incorrectly matches that
driver control. The new fixture pin-use guard rejects the exact counterexample;
a separate internal-open control fails native LVS, along with output-short and
missing-NMOS controls. No existing failure or check is waived.

Six bounded invocations contain 24 native comparisons. Three failed receipts
retain an absent-layer export-check bug, the flat delay mismatch, and the native
false positive. Total cost including failures and cleanup: **39.179 CAD seconds**;
campaign **8,067.658 seconds / 134.46 minutes**. Input hashes remain unchanged,
all receipted containers are absent, and no chip, installed PDK or routing
allocation changed. Three A attempts remain used and two B attempts reserved.
Full SRAM/GDS qualification, compatible fast views, timed Lean refinement,
accepted A/B and clean-source replay remain open.

Next qualify consistent hierarchy ownership, dimensional resistor combination
and connected-port handling on the small fixtures before a larger SRAM block.

Manifest: `physical/experiments/sram-context-results.json`, SHA-256
`dbeb1f8e0c79e62a52de75001cbd3b083b901f78e9305f6185f149f75440a52e`.

## 2026-09-27 — SRAM comparison policy qualifies the local fixtures

The [comparison-policy study](../physical/sram-comparison-results.md) qualifies
the four unchanged context fixtures in both extraction modes. The packaged
[recipe](../../physical/fixtures/sram-comparison/README.md) binds ports from
top-owned source labels and extracted metal, flattens only the small netlists,
aligns dimensional resistor classes and preserves each resistor and declared
port through preparation. Only one file in a private 183-file deck copy changes;
source GDS, installed PDK and chip remain unchanged.

**Correction to the preceding entry:** six of its nine database matches fail
the final native port check. The isolated drivers, flat driver parent, adapted
isolated dummies and original discarded-output control were not full native
passes. The complete adapted delay parent (two runs) and its unchanged carrier
were the three actual native passes. All 24 original logs and raw receipts are
preserved, and the new manifest records the corrected interpretation.

Final packaged replay: **52 invocations**. Eight original fixture comparisons
and two unchanged physical carriers pass. All **42 deliberate defects** reject:
20 native mismatches and 22 explicit interface/model/dimension refusals. All
devices and declared pins match on positive inputs. Each complete delay result
retains six ambiguous internal dummy-net pairs; it does not prove a unique
instance-name mapping for those nets. Eight incomplete-evidence controls and
the seven existing source-translation refusal controls pass.

Ablations reproduce the unreconciled driver hierarchy failure and, with valid
physical ports but interface safeguards removed, establish a real final-native
pass for the disconnected-output defect. Removing global legacy-label support
preserves all eight positive fixtures, so the final recipe leaves general label
rules unchanged. Removing the non-combination settings produces a native pass:
both dimensional classes combine six resistors to one 0.260 × 3.600 µm device.
The rejected expectation remains recorded; retaining six separate resistors is
the stronger selected contract, not a claim that those flags alone fix LVS.

Ten bounded invocations consume **198.128 CAD seconds**, including all failures
and cleanup. Four receipts complete and six retain failed expectations/recipes:
missing or combined port labels, Ruby proxy identity, earlier physical-open
guard rejection than expected, an ablation syntax error and the disproved
combination expectation. Campaign total: **8,265.786 seconds / 137.76 minutes**.
The final audit checks **7,670 source/artifact files**, verifies exact packaged
recipe identity, and confirms all frozen sources unchanged and receipted
containers absent. No extra A routing attempt; three A used and two B reserved.

Next scope a bounded hierarchical macro integration with changes limited to the
two affected direct-child block types, complete port accounting and faults
crossing those boundaries. Preserve array hierarchy. Full SRAM/GDS signoff,
the earlier Magic diagnostics, compatible fast views, timed Lean refinement,
accepted A/B and clean-source replay remain open. Changes remain local.

Manifest: `physical/experiments/sram-comparison-results.json`, SHA-256
`e27dd920505df8fa6eec9c8dc35ebe78fe6c298c6ad9a8e647e971ee8e46e7ee`.

## 2026-09-27 — Hierarchical SRAM integration locates the remaining failures

The [bounded integration](../physical/sram-integration-results.md) inventories
the supplied macro before comparison preparation. Extraction retains 140 layout
definitions and a device-free macro top; 62 of 145 schematic definitions are
reachable. The prior near-flat macro arose during unmatched-name alignment.
The new [diagnostic recipe](../../physical/fixtures/sram-integration/README.md)
sets 22 explicit circuit-name pairs and expands only the admitted driver/delay
families. The private deck changes one comparison file; source GDS, installed
PDK and chip remain unchanged.

All **548 physical label positions** bind consistently to **351 distinct macro
ports**, retained through alignment, preparation and comparison. Repeated supply
labels probe one connected net per supply. Both sides retain two matrices,
128 columns, 1,024 tiles and 32,768 cells. Scoped expansion preserves every
device/parameter; native finger combination yields **140,639 NMOS and 75,167
PMOS** on each side. Twelve qualified dummy metal1 resistors remain separate;
the other **98,704** resistors retain their unresolved metal2/metal3 versus
`LVSRES` representations.

Native comparison still fails: **23 matching types, eight nonmatches and
19 skipped parents**, including the macro. The failures are the bit cell, array
edge, bit-line driver and five buffer/inverter/fill-cap types. Recorded parent
inventories agree in total devices but place them at different hierarchy levels.
This is not proof of their wiring or of the expanded driver/delay connections.
The packaged replay reproduces the complete circuit readback and policy audit.
Cross-block fault comparisons are deferred because their positive macro control
does not pass.

The next candidate context is the complete 32-bit tile: **192 MOS devices and
96 resistors**. It needs preserved geometry, explicit model/layer/dimension
interpretation and ownership/boundary qualification. The manifest also locates
the array-edge, bit-line-driver, column-driver and row-register contexts for the
remaining failures. These are candidate contexts, not newly passing fixtures.

Four bounded offline invocations cost **38.143 CAD seconds**, including failures
and cleanup. Three complete; the first macro adapter refused after misreading
layer 50/25 as topmetal1. The pinned deck identifies it as metal4; the corrected
recipe retains every port guard. The failed receipt remains intact. A final
audit checks **4,440 unique source/artifact files**, exact packaged replay and
container absence. Campaign total: **8,303.929 seconds / 138.40 minutes**.
No new A route; three A used and two B reserved. Full SRAM/GDS signoff, prior
Magic diagnostics, fast compatibility, timed refinement, accepted A/B and
clean-source replay remain open. All changes remain local.

Manifest: `physical/experiments/sram-integration-results.json`, SHA-256
`5370a251b97dc192e152d8c62696aa8a0b6f93a3819dc84e89e0d5ab669ba707`.

## 2026-09-27 — Complete SRAM tile isolates a source width disagreement

The [tile experiment](../physical/sram-tile-results.md) exports the complete
32-bit tile with its four tap instances and original hierarchy. All 27 source
layers preserve polygon XOR and text identity. Its 192 MOS devices occupy
different hierarchy levels in native extraction and source CDL; bounded tile
netlist flattening reconciles that ownership without changing geometry.

All **96 physical resistor markers measure 0.200 × 0.600 µm**, while the source
declares **0.260 × 0.600 µm**. Native metal2/metal3 extraction agrees with the
marker measurements and expected endpoints. The strict dimensional adapter
refuses the source with `SOURCE_GEOMETRY_DIMENSION_MISMATCH: R1`.

A separate diagnostic changes three repeated width tokens, affecting all 96
resistors, and applies only the checked R0/R1 metal2 and R2 metal3 translation.
Both deep and flat extraction match **288 device pairs, 182 net pairs and
42 pin pairs**, with no ambiguity. Restoring the original widths on the same
prepared comparison fails in both modes. The packaged comparison reproduces
the original diagnostic's complete native circuit readback and policy audit.
The supplied tile, complete SRAM and chip remain unqualified.

The [tracked bundle](../../physical/fixtures/sram-tile/README.md) has four
counterfactual positive comparisons, **42 fault rejections** (30 native,
12 explicit policy), seven incomplete-evidence refusals and 13 adapter
refusals. Faults include single-bit wiring/device/model/dimension changes,
word-line swaps, physical metal/gate edits and physical port corruption.
The shared physical bit-cell mutations affect 32 instances; their unchanged
carrier preserves all geometry/text and passes both modes.

An auxiliary local fault-area field incorrectly reports zero after its live
KLayout geometry view is mutated. The whole-tile XOR checks remain correct.
Separate saved-GDS readback records local/whole-tile areas of 0.008/0.256 µm²
for the open, 0.012/0.384 µm² for the bridge and 0.039/1.248 µm² for the missing
gate. Original receipts and this explicit correction are both retained.

Four bounded offline invocations cost **86.455 CAD seconds**, including
cleanup, with 52 native LVS comparisons. Final audit verifies **4,577 unique
source/artifact files**, identical packaged recipes, the causal replay and
container absence. Campaign total: **8,390.384 seconds / 139.84 minutes**.
Three A routes remain used and two B routes reserved; chip, macro inputs and
installed PDK remain unchanged. All work remains local.

Next resolve whether the exact supplied views intentionally use different
width conventions or contain an inconsistent reference. An accepted correction
or interpretation needs source provenance and retained fault sensitivity.
Remaining array/control contexts, macro wiring, Magic diagnostics, fast views,
timed refinement, accepted A/B and clean-source replay remain open.

Manifest: `physical/experiments/sram-tile-results.json`, SHA-256
`35861d73053e38124b63369065d86768030d663b8838e553dacab012fc58cc32`.

## 2026-09-27 — SRAM provenance and explicit component trust

The [provenance study](../physical/sram-trust-results.md) verifies all seven
actual SRAM views and the shared behavioral dependency against the complete
pinned PDK tree. CMOS5L explicitly aliases the SG13G2 SRAM library. Direct
measurement of the original 2023 GDS/CDL reproduces the 0.200/0.260 µm width
split; it is not caused by mixing our view versions. Twenty-six public source
captures retain the reference configuration/history and upstream discussions.
The exact interpretation remains undocumented in the inspected material.

The first native abstraction probe refuses before extraction because DEF is a
required Step input. The second supplies the retained DEF to the unchanged
GDS-selected native script: 47 cell names match the reference regex, and the
macro becomes an empty 351-terminal definition. Twenty-three overlaps and 518
conversion diagnostics remain. The one-instance native boundary comparison
matches, rejects signal-to-ground and ground-to-power faults, and still matches
when an internal width edit is projected away. This measures interface coverage
and its internal blind spot; it does not repair extraction or qualify the macro.

The source-audit parser initially selected both historical one-port/two-port
bit cells and refused; the correction selects the exact one-port definition.
A guessed upstream README fetch returned 404; the actual pinned doc is captured
separately. Both failures remain recorded. The independent audit verifies
3,867 frozen input/artifact paths and revalidates prior actual-chip boundary
and geometry receipts. No chip/PDK modification or additional full route occurs.

Three bounded offline invocations cost **21.779 CAD seconds**, bringing the
campaign to **8,412.163 seconds / 140.20 minutes**. The
[manifest](../../physical/experiments/sram-trust-results.json) SHA-256 is
`5f1d0fab527f89ac88ee8f0873a78f6769d128421724909d18488452cc1d303e`.
It binds 232 local raw files, the source audit, exact controls and proposed
component contract. Receipted containers are absent and source hashes unchanged.

The [maintainer report](../physical/sram-maintainer-report.md) is prepared and
unsent. Current work separates conditional paired formal correspondence from
exact-version physical component qualification. The contract is a proposal,
with no new Lean axiom or production admission change. Internal signoff, fast
compatibility, timed refinement, accepted A/B and clean-source replay remain
open; [status](status.md) owns the next work.

## 2026-09-27 — Conditional paired graph and package correspondence

The [formal continuation](../storage/paired-formal-correspondence.md) proves
the actual shared graph constructor preserves next-state and observation
semantics. Both 45-node binding lists establish their equations; the seven
upstream premises of the isolated-validation proof are now discharged from the
graph. The retained variant agrees with the original paired controller for
arbitrary input and register valuations.

The existing sampler, serial receiver, pin map and result observer compose with
that interpretation. The single-port memory contract explicitly distinguishes
idle, enabled reads and writes. It starts with arbitrary contents/Q and tracks
known words through a partial model. Legal package read/write modes and
preservation of every previously active SRAM word are proved. Given the memory
law as an explicit parameter, every finite package input history has equal
before/after-edge observations in the retained typed package and graph model.

This is not yet E64 execution correspondence: accepted-upload coverage,
committed-image agreement and the controller's timed dispatch/capture/wait
invariants remain open. No global memory axiom, physical waiver or admission
change is introduced. The proposed SRAM contract and prior physical receipts
are unchanged; this continuation has its own source freeze.

The default library build and reachability check pass for 212 modules. The
whole-library audit covers **15,843 declarations / 8,001 theorems** with only
standard axioms, and the injected-axiom control rejects. Nine kernel examples,
both actual constructor witnesses, four existing invalid-graph controls and the
separate schedule proof pass. An executable check binds the proved package to
the emitter. Fresh core/package MLIR and interface metadata match the retained
mapping artifacts exactly. The full protocol executable suite was not rerun.

The `paired-formal-01` receipt takes **9.191 seconds**, with **zero CAD calls**.
Its UTC timestamp is September 28, still September 27 in America/New_York.
Campaign CAD usage remains **8,412.163 seconds**; three A routes are used and
two B routes reserved. All work is local.

Manifest: `physical/experiments/paired-formal-results.json`, SHA-256
`0bae814be784cafb2b238f66dcb5aef42fdee8f773b13ddeb25daef93358df39`.
Full report: `build/validation/paired-formal-01/report.json`, SHA-256
`454a717d470c0c178c81bd056220a6abcab89d4c30317d0145301024d750a92b`.

## 2026-09-28 — Accepted uploads establish the paired resident image

The [upload gate](../storage/paired-upload-coverage.md) closes the first two
obligations from the graph/package checkpoint. `PairedLoader` tracks a
mathematical ledger of accepted words for the 290-word protocol. `PairedUpload`
proves the actual graph's acceptance, commit, control and storage updates agree
with that protocol. `PairedCoverage` carries the invariant through arbitrary
decoded-command histories after initialization and transfers it to the retained
typed controller under the explicit SRAM contract.

A valid active bank now matches a complete transcript: all 32 parameter words,
256 SRAM rows, boot token and idle configuration. The image checker binds its
E64 certificate to those actual stored values. Every write preserves the old
active bank, including parameters and metadata. Enabled reads of a valid image
return the loaded row for the token installed on the edge. Initial register
values, contents and Q remain arbitrary; initialization invalidates ownership
without requiring physical memory to clear. The ledger adds no hardware state.

The first `paired-upload-01` attempt built but correctly failed the whole-library
axiom audit: `bv_decide` introduced a compiled-check assumption in a control
proof. The failed receipt retains its original source hashes and diagnostics.
The proofs were rewritten using finite cases, bit-vector lemmas and arithmetic;
the audit policy and memory premise were not weakened. The passing attempt has
its own source freeze.

The `paired-upload-02` receipt passes in **26.192 seconds**. The full library
build and import check cover **215 reachable modules**; the audit checks
**16,152 declarations / 8,219 theorems** with only standard Lean axioms. An
injected axiom still rejects. The previous nine contract/ordering examples,
both core constructor witnesses, four invalid-graph controls and schedule proof
pass. New retained-controller executions cover two complete images, every
storage slot, invalid words in each region, short/extra/busy commands, abort,
both reset forms, restart, replacement, reinitialization, row 255 and old-Q
dispatch. The full protocol executable suite was not rerun.

Fresh core/package MLIR and interface metadata are byte-identical to the
retained mapping artifacts. All 233 passing-run source inputs, 14 artifacts and
three failed-run artifacts retain their recorded hashes. The previous formal
manifest, proposed memory contract, chip and installed PDK are unchanged. There
are **zero CAD calls**; campaign usage remains **8,412.163 seconds**, with three
A routes used and two B routes reserved. All work is local.

The next gate is a running-state invariant for usable Q, the current token and
cached parameters on every edge, followed by timed dispatch/capture/guard/wait
and terminal behavior. It must then compose with package and host-delivery
conditions. The enabled-read theorem alone does not establish that full timing
claim. Physical SRAM qualification, compatible fast timing, accepted A/B and
clean-source physical replay remain open; [status](status.md) owns the current
decision.

Manifest: `physical/experiments/paired-upload-results.json`, SHA-256
`cfba577201e3dc6e4ef8c410d8b688c53ede047c64dd4cee73ba418e8f494b7a`.
Passing report: `build/validation/paired-upload-02/report.json`, SHA-256
`346e7746ba6d1996831cdfe5d3cfea4668cbb146c4c85c92d194864ac2b9256e`.
Failed report: `build/validation/paired-upload-01/report.json`, SHA-256
`0603017efec8d4784b9046260482a254df7540336bcf2ced945d61a6f0034dba`.

## 2026-09-28 — Running instructions own their parameters and SRAM responses

The [running-state gate](../storage/paired-runtime-ownership.md) closes the
next invariant in the timed execution plan. `PairedRunning` proves validity,
parameter lookup, response ownership and current-token provenance from the
actual graph equations. `PairedRuntime` combines that invariant with upload
coverage for every finite initialized decoded-command history and transfers it
to the retained typed controller under the explicit SRAM behavior law. Prior
registers, memory contents and Q remain arbitrary; no global axiom or hardware
state is added.

The graph requests a read on **every edge whose resulting state is running**.
Countdown and blocked-wait edges refresh the same current row. An instruction
transition consumes old Q and refreshes Q for the new token; stopped states may
hold stale Q. This resolves the earlier concern about Q availability across
running hold cycles. With a certificate for the active accepted transcript,
the current token denotes its canonical source instruction. Actual dispatch
installs the certified successor selected by the actual branch wire.

The `paired-runtime-01` receipt passes in **62.091 seconds**. Its build/import
check covers **217 modules** and whole-library audit checks **16,268 declarations
/ 8,328 theorems**, using only standard Lean axioms. An injected axiom rejects.
Previous graph/package witnesses, memory/ordering examples, upload controls,
invalid-graph controls and schedule proof pass. New retained-core controls load
a certified image into both banks and compare **100 edges / 82 running edges**
with the independent E64 reference. Six paths cover captures, wait and
qualification success/timeouts, guard failure, both branch outcomes, an invalid
target, halt, ignored busy commands, reset and restart. Stale-Q, parameter and
invalid-token mutations reject in both banks. These finite tests do not replace
the remaining universal timing proof.

Fresh core/package MLIR and interface metadata remain byte-identical to the
retained mapping artifacts. The report freezes **236 source inputs / 15
artifacts**; prior reports and manifests retain their own source freezes.
The proposed memory contract and chip are unchanged. There are **zero CAD
calls**; campaign usage remains **8,412.163 seconds**, with three A routes used
and two B routes reserved. The full protocol executable suite was not rerun.
All work remains local.

**Next:** prove timed control and observations from the E64 reference. The
current successor theorem uses an actual entry edge and actual branch wire;
derive those from capture, guard, countdown, wait and qualification behavior,
then prove the mode/counter/sample/pin relation through start, terminal and
reset. Package and qualified host delivery must then compose. Physical SRAM
qualification, compatible fast timing, accepted A/B and clean-source replay
remain open; [status](status.md) owns the next decision.

Manifest: `physical/experiments/paired-runtime-results.json`, SHA-256
`7a54e8b94aab65c43d999c1d794e66db0ac24f00788d6692dabe403e5f4f2634`.
Report: `build/validation/paired-runtime-01/report.json`, SHA-256
`bbe831bf9085d67ab519dcda708e482240b0b92cb15d7e5c454391a300414238`.

## 2026-09-28 — Retained paired execution agrees with E64 on every segment edge

The [timed execution gate](../storage/paired-timed-execution.md) closes the
control and observation obligation left by running-state ownership. The proof
derives actual dispatch, guard, wait and qualification decisions and interprets
the resulting counters, captures and pin commands. Checked branching uses the
terminal capture before successor entry capture, including when both captures
write the same slot. Deadline success, guard priority, qualification retries,
maximum-width counters, start, reset and terminal idle commands follow E64.

`PairedTimed.retained_trace` compares the retained controller's actual public
execution outputs before and after every edge. `initialized_segment` connects
this result to arbitrary power-up registers, SRAM contents and Q, through
initialization, an arbitrary upload history, active validity and an independent
certificate for the actual accepted transcript. A real reset establishes the
initial execution relation. The subsequent finite history may contain any
inputs with `init = 0` and `command != 3`; program replacement begins another
certified segment. Loops need not terminate. The SRAM law remains an explicit
parameter, with no free graph-wire premise or new global axiom.

The `paired-timed-02` receipt passes in **123.265 seconds**. The full build and
import check cover **226 modules**; the audit checks **16,564 declarations /
8,585 theorems**, with standard Lean axioms only. An injected axiom rejects.
Existing contract/ordering, exact graph/package, upload, 100-edge runtime,
invalid-graph and schedule controls pass. New retained-output controls certify
the actual accepted transcripts and compare **686 before/after edge pairs**
across both banks. Six scenarios cover capture/branch/entry overwrite,
maximum duration, zero-budget deadlines and timeouts, guard priority,
reset/restart and repeated backward jumps. Eight live counter, pin, sample or
capture-parameter corruptions are run through another edge and rejected.

The first `paired-timed-01` receipt failed on a missing dependent type annotation
in the new mutation-test harness; its library build and axiom audit passed.
The corrected test has a new source freeze. Both receipts are retained; no
proof premise, memory contract or audit policy was weakened.

Fresh core/package MLIR and interface metadata remain byte-identical to the
retained mapping artifacts. The passing report freezes **246 source inputs /
16 artifacts**. Fourteen existing graph-wire lemmas were made public without
changing their statements or proofs: reversing only those visibility edits
reconstructs the prior source hash. The predecessor runtime manifest/report and
component proposal remain unchanged. All work is local, with **zero CAD calls**;
campaign usage remains **8,412.163 seconds**, three A routes used and two B
routes reserved. The full protocol executable suite was not rerun.

**Next:** compose this execution theorem with the actual package adapters,
result observer and qualified host delivery. Establish the relation at the
existing commit/start boundary without relying on an additional reset, and
account for certified replacement between segments. Physical SRAM qualification,
compatible fast timing, RTL/source-to-GDS correctness, accepted A/B and clean
physical replay remain separate. [Status](status.md) owns that decision.

Manifest: `physical/experiments/paired-timed-results.json`, SHA-256
`fe7aceef2e9bad1e55213355c07e5e92c114d77233db1410a078c2056e419b8c`.
Passing report: `build/validation/paired-timed-02/report.json`, SHA-256
`af8df88415148d29b4395675457234accdaf619c6fbdb6a4f77de71e1b5cb5b5`.
Failed report: `build/validation/paired-timed-01/report.json`, SHA-256
`9d7218ba6553ed28cd476c2a610109bf9bba456b0910a9639d4501d379ea003e`.

## 2026-09-28 — Accepted commit starts E64 through the actual package and mailbox

The [package and host lifecycle gate](../storage/paired-host-lifecycle.md)
connects the prior timed-core proof to the retained paired package. Accepted
commit clears execution mode/counters/samples and selects the new certified
image's idle commands, establishing the E64 relation without an additional
reset. `PairedPackage` interprets every actual adapter, controller/SRAM and
mailbox edge. `PairedHost.retained_initialized_commit_segment` starts with
arbitrary represented state, initializes through three reset-low samples,
constructs accepted-write ownership through an arbitrary host prefix, and
proves all three package output ports before and after each subsequent segment
edge. The same commit boundary supports later certified replacements with an
occupied mailbox.

E64 supplies execution state and busy. Loader status and speculative read
addresses retain their graph interpretation. `session_delivers` connects the
existing qualified digital serial-session theorem to the command stream
actually consumed by this package. The SRAM law remains an explicit parameter;
no global axiom, hardware state or added cycle is introduced.

The `paired-host-01` receipt passes in **199.413 seconds**, with **229 reachable
modules**, **16,736 declarations / 8,696 theorems**, standard axioms only and
successful rejection of the injected unapproved axiom. Existing graph/contract,
upload, 100-edge runtime, 686-edge timed, graph-fault and schedule controls pass.
The new actual-package test passes **794 before/after pin-edge pairs** and
rejects **three executed mutations** of mailbox sample data, drive enables and
page-pipeline state. It prepares two images using real accepted decoded writes,
then drives two serial commit frames and three serial start frames. Immediate
start, capture pages, unread retention across replacement, halt-only completion,
overrun, consume/clear and restart pass. Full 290-word uploads are not replayed
bit by bit by this finite test; delivery is covered by the universal theorem.

Fresh core/package MLIR and assembly metadata match the retained mapping bytes.
The report freezes **250 source inputs / 17 artifacts** and all inputs remain
unchanged during the run. Previous timed manifest/report/proofs/test and the
component proposal keep their recorded identities. The full protocol
executable suite was not rerun. Work remains local, with **zero CAD calls**;
campaign usage stays **8,412.163 seconds**, three A routes used and two B routes
reserved. Physical qualification and acceptance are unchanged.

**Next:** prove total certified-upload admission: a qualified host
begin/290-word/commit sequence from stopped initialized state must establish the
actual accepted transcript and commit required by this theorem. Delivery alone
does not establish acceptance. SRAM internal qualification, compatible fast
conditions, analog/board behavior, RTL/source-to-GDS correspondence, A/B and
clean-source replay retain their separate gates. [Status](status.md) owns the
next decision.

Manifest: `physical/experiments/paired-host-results.json`, SHA-256
`859aac7a2a260ed381861994d7465122293b210feca57ac90efa10ec3451f1e7`.
Report: `build/validation/paired-host-01/report.json`, SHA-256
`08465d6def861ef7d1dc9f04731b73a06f4d0db1a49a696cf3b3b8707192d92b`.

## 2026-09-28 — Certified delivery derives actual upload acceptance

The [certified upload-admission gate](../storage/paired-upload-admission.md)
discharges the successful-upload premises of the package lifecycle theorem.
`PairedAdmission` proves the actual word-validation decisions from the source
certificate. `PairedSession` uses accepted-prefix ownership to establish the
inactive parameter table after the first 32 words, then admits every row, boot
token and idle word. A delivered begin/290-word/commit sequence necessarily
reaches accepted commit and ready E64 state. Arbitrary quiet gaps, nonzero quiet
data, producer-chosen parameter locations and unused noncanonical table entries
are permitted. There is no assumed admission decision or accepted transcript.

`retained_initialized_session` prepares arbitrary represented controller,
adapter, mailbox and SRAM state with three reset-low samples and two idle
release samples. It composes qualified serial delivery, two sampler-drain pins,
derived admission and every subsequent package execution/observation edge.
Commit needs no extra reset before start. The decoded/package upload theorem
also covers replacement from any stopped initialized state. The SRAM law,
digital `Serial.Session` and execution-segment rule (`init = 0`, `command != 3`)
remain explicit. Loader sideband retains its graph interpretation.

The `paired-admission-01` receipt passes in **235.829 seconds**. The default
build and import check cover **231 modules**; the whole-library audit checks
**16,808 declarations / 8,757 theorems** with standard Lean axioms only. The
injected unapproved axiom rejects. Existing memory/graph, upload, 100-edge
runtime, 686-pair timed, 794-pair package, graph-fault and schedule controls pass.
The new retained-core controls take **28.409 seconds** and check two certified
parameter permutations across both banks: **580 accepted pushes**, **168 quiet
edges**, every stored parameter/row/metadata value, and ready E64 state directly
after commit. Four executed refusals cover a corrupt inactive capture parameter
and premature commit in each bank. Two canonical wrong-source guards fail the
source certificate; these are not hardware syntax rejections. Replacement
preserves the previous active image. The finite test does not replay a complete
290-word upload bit by bit; qualified serial admission is proved universally.

Fresh core/package MLIR and assembly metadata remain byte-identical to the
retained mapping artifacts. The passing report freezes **253 source inputs /
18 artifacts**, with all inputs unchanged during validation. The previous host
manifest/report, all 26 of its proof/test sources and the component proposal
retain their recorded identities. Root imports and the runner have a new source
freeze. The full protocol executable suite was not rerun. All work is local,
with **zero CAD calls**; campaign usage stays **8,412.163 seconds**, three A
routes used and two B routes reserved. Physical acceptance is unchanged.

**Next:** consolidate one reproducible acceptance report binding the actual host
source certificate, this digital proof, retained emitted implementation and
physical candidate by identity. Missing SRAM internal qualification, compatible
fast operating conditions and source-to-GDS evidence must continue to refuse
complete-chip acceptance. Resident SHIFT/KEEP, analog sampling, accepted A/B
and clean physical replay retain their separate gates. [Status](status.md)
owns the next decision.

Manifest: `physical/experiments/paired-admission-results.json`, SHA-256
`ab15aa2d908c26d2c7e2d617d4e92b97bb4d8377fcb6643e080743e25a63c451`.
Report: `build/validation/paired-admission-01/report.json`, SHA-256
`1808375202825f9c103b0f2b78e31125fdcd1d6a71311053fc192936ff6afa6a`.

## 2026-09-28 — One identity-bound assessment connects host, proof and physical candidate

The [combined acceptance gate](implementation-acceptance.md) now provides one
reproducible report for the exact retained A implementation. Nine pinned roots
connect the actual host programs and certificates, conditional admission/session
proof, retained emission, scoped mapping/physical checks, filled circuit and
component evidence. The command creates JSON and readable Markdown and refuses
missing, changed or disconnected evidence. A completed assessment is distinct
from chip acceptance; `--require-accepted` returns 2 for the present open gates.

The original paired host RTL is byte-identical to the baseline side of the
validation-isolation SAT comparison. Its isolated side matches the emission
bound by the new Lean proof. Further mapping SAT and the implemented circuit's
own SAT receipt consume the selected balanced readback. Input identities and
fresh structural comparisons connect the routed circuit, electrical repair and
finishing. The repair check accounts for five noninverting buffers and one
declared input-only protection diode bound to its receiver. Final timing is
recomputed from metrics tied to the selected ODB/netlist/SDC/SPEF, and exact
Liberty operating conditions are reread and joined to the inspection inputs.
The exported-GDS SRAM boundary and proposed component views retain their own
scope; none becomes an internal-memory proof.

`design-acceptance-03` completes in **111.130 seconds**, checking **572 input
files**, **58 evidence connections** and **eight fresh kernel certificates**.
Every captured host program re-renders the exact retained image/upload
certificate before the kernel checks it. The report retains **16 new artifacts**
and confirms unchanged inputs. Its 11 requirement rows contain six scoped
passes, one conditional digital proof and **four A blockers**: SRAM internal
and behavioral qualification, compatible fast timing conditions,
typed-circuit-to-RTL correspondence, and package power qualification. A, B and
complete iteration remain unaccepted. The 64-record B change and clean-source
physical replay remain additional iteration gates.

All **17 focused tests** pass normally and under `python -OO`. The controls
cover artifact custody, cross-candidate joins, actual consumed inputs, executed
checks, complete requirement tables, program/certificate identity, physical
readback corruptions, protection receiver/master restrictions, Liberty
conditions and refusal/output behavior. The optimized controls have their own
source and command receipt. The new report's refusal checks remain active under
optimized Python.

The earlier `design-acceptance-01` intake is retained as an invalid-evidence
receipt (**88.518 seconds**). Its eight certificate checks passed, but the new
consolidation replayed buffer contraction without the existing protection-diode
check. The corrected intake includes that declared check plus direct receiver
binding and rejection controls. The candidate, older physical checks and proof
premises were not changed or weakened.

The second intake completed with the same four blockers in **103.172 seconds**.
A final source audit added the indirectly loaded execution grammar to the
explicit checker freeze and historical host-source comparison. The third
intake independently repeated all eight kernel checks and now covers 572 input
files. Both completed assessments are retained in the manifest.

The preceding proof receipt, all nine selected manifests and the SRAM proposal
remain unchanged. The full Lean library gate is reused by source/artifact
identity; host and final-netlist simulation, mapping SAT, physical CAD and
extraction were not rerun. Work is local, with **zero CAD calls**, no additional
route and no hardware edit. Campaign usage remains **8,412.163 CAD seconds**,
three A routes used and two B routes reserved.

**Next:** connect an interpretation of the exact paired emitted artifact to the
typed circuit and session theorem, reusing the backend readback machinery.
External component evidence, compatible timing and package power retain their
independent qualification requirements. [Status](status.md) owns allocation.

Manifest: `physical/experiments/design-acceptance-results.json`, SHA-256
`52416347f4773313e4424694f746e35b63bc2e13d4418e98fb2c11df998b15d3`.
Report: `build/validation/design-acceptance-03/report.json`, SHA-256
`0dc56778c6c80f818bcc983e4e300998ea6ddc4991e05048e84b5c8bd8827226`.
Controls: `build/validation/design-acceptance-controls-02/report.json`, SHA-256
`a6a4d47f03f7dbb914042a813ec9b2a989e9a6bdff612ffc19aee86c9a2a2d95`.
Failed intake: `build/validation/design-acceptance-01/report.json`, SHA-256
`edc93b476614047048e1604a37467520b69df67350713ea22ddb4924c706b4f2`.


## 2026-09-28 — Retained paired RTL interpretation and refreshed acceptance

The [artifact-interpretation gate](../storage/paired-rtl-interpretation.md) now
connects both exact retained emitted modules to their typed components and
composes the package interpretation with the certified upload/E64 session
proof. It checks all 81 controller register fields and 37 outputs, and all
110 package register fields and seven outputs, for arbitrary represented
state and two-state inputs. SRAM Q is independent at the component boundary;
the complete session retains the explicit memory law and digital premises.

The fresh `paired-readback-02` run passes in **315.149 seconds**: **264 frozen
inputs**, **160 source/log artifacts**, **69 recorded validation commands**, and **1,082 local
bit-vector equivalences**. The compiled-environment audits cover 18,645
controller-context and 19,542 package-context theorems with standard axioms
only; these overlap and are not a unique combined count. Both unchanged
reimports pass. Six altered RTL artifacts fail against the original certificates
(cursor, parameter bank, write enable, sampler, mailbox valid and package
output); both injected-axiom controls fail as required. All seven importer
tests pass normally and under optimized Python.

During proof development, the default native-evaluation reconstruction was
rejected by the axiom audit. The final proofs retain predicate/bit correlations
and use explicit cursor, slice-assembly and modular-subtraction lemmas. The first
packaged run (`paired-readback-01`) remains a failed receipt: adapting the
already-typed package-to-core projections changed their return types, and Lean
rejected the result. The final generator adapts only reused backend graph/link
code. No hardware expression or proof premise was weakened.

The [refreshed acceptance intake](implementation-acceptance.md) consumes the new
interpretation and the same selected raw RTL, original formal receipt and final
physical candidate. It completes in **80.463 seconds**, checking **740 files**,
**75 evidence connections**, and **eight fresh host certificates**. The formal
interpretation requirement now passes. **A remains unaccepted** with three
blockers: exact-version SRAM internal/behavioral qualification, compatible fast
conditions and qualified package power assumptions. All 20 acceptance tests
pass normally and under optimized Python, including refusal of partial
interfaces, missing session or fault checks, and physical-gate waivers.

The original nine evidence roots, candidate and resource ledger are unchanged.
Local Yosys frontend imports and untrusted Z3 proof proposals were used for
readback; no physical-design run, hardware edit, external action or route slot
was added. The acceptance intake itself runs no CAD. The physical campaign
remains **8,412.163 CAD seconds**, three A routes used and two B routes reserved.
The new v2 selection and report preserve the initial v1 four-blocker assessments.
[Status](status.md) owns the next qualification decision.

Readback manifest: `physical/experiments/paired-readback-results.json`, SHA-256
`0be933835d54b5f543d53c4d92e0784f29d7cd3932e5e1578afed426556c1cc2`.
Readback report: `build/validation/paired-readback-02/report.json`, SHA-256
`666c1a75e56cc8d1a6ab598e1038338d708e5010f77d802b8c68c27d4abe16cd`.
Acceptance selection: `physical/experiments/design-acceptance-readback-inputs.json`, SHA-256
`13ab5917f59147e9944da5ff016eb6dd064149340164af78584ff9f037496e8e`.
Acceptance manifest: `physical/experiments/design-acceptance-readback-results.json`, SHA-256
`54b1ca809f61e9da33cf632861fb7de5ceab2f5e188c860924a3ecfff5fa0f19`.
Acceptance report: `build/validation/design-acceptance-readback-01/report.json`, SHA-256
`1adca18c69f62bcd99fea37073572e273eb44b8bd38633f587cc62a727cb911e`.

Final local verification also passes the six existing backend-readback tests
with `PYTHONPATH=scripts`, 775 local links / 116 anchors across the 11 affected
documentation pages, and `git diff --check`. The first narrow legacy-test
invocation lacked the scripts import path; its configured rerun passes. The
status page retains the historical official-outline anchor used by the journal
and competition brief. Final identity checks confirm both new report hashes and
all 264 readback / 740 acceptance inputs remain unchanged.

## 2026-09-28 — Physical qualification dependencies made concrete

The user approved the bounded three-blocker assessment. The
[study](../physical/physical-qualification-assessment.md) and
[manifest](../../physical/experiments/physical-qualification-results.json)
record the local inventory, public source captures and next experiment's
admission conditions. The [read-only recipe](../../physical/fixtures/physical-qualification/README.md)
replays the assessment without network or CAD.

All six CMOS5L standard-cell libraries and all three exact-macro libraries
match their pinned Git blobs and the captured development tree at
`0488153564fdae82164201091e1c4375b97e61ad`. Fast temperatures remain −40°C and
−55°C. The current unmerged lvsres proposal is no longer a draft; its 47-file
diff retains our bit-cell widths while adding Metal1 labels inconsistent with
the retained metal2/metal3 witnesses. The original unsent maintainer report is
preserved; supplemental layer and fast-characterization questions are in the
new study. No maintainer communication occurred.

Pinned power-source code first uses block-pin shape nodes. The candidate DEF
has 86 VPWR and 85 VGND shapes spanning the straps. The saved run lacks explicit
source files and workload activity; its 9.119430 mW estimate and 0.257/0.285 mV
rail drop/rise remain conditional observations. The next local power experiment
needs source geometry, voltage/impedance and activity inputs tied to the timing
voltage budget. Runtime source-node count was not newly measured.

The first source-inventory audit refused a commit/tree-ID comparison. GitHub
echoed the requested commit ID in the tree response; the corrected recipe
reconstructs the actual root and all subtree objects before comparing against
the commit's tree. Final inventory checks 64 files and nine libraries, and a
fresh output is byte-identical. Earlier development inventory is retained as
`inventory.json`; `inventory-02.json` is the complete selected assessment.

This pass adds **zero CAD seconds** and no route. Campaign use remains
**8,412.163 seconds / 140.20 minutes**. The acceptance report and its three
blockers remain unchanged; A is unaccepted, B is not admitted, and clean-source
physical replay remains open.

Local validation passes 64 inventory input identities, 16 pre-validation
manifest references, byte-identical replay, 723 local links / 113 anchors across
nine affected documentation pages, and `git diff --check`. The final manifest
also binds the validation result and its recipe. No new formal or CAD run is
claimed by these checks.

## 2026-09-29 — saved-layout power boundary and activity sensitivity

Completed the [frozen power study](../physical/power-boundary-experiment.md) on
A's unchanged filled layout. The [results](../physical/power-boundary-results.md)
and [manifest](../../physical/experiments/power-boundary-results.json) retain
sixteen bounded invocations and exact source, waveform and implementation IDs.
Baseline worst rail drops reproduce exactly. Default sources resolve to
7,912 VDD and 7,832 ground nodes; four explicit audited contacts per rail raise
conservative combined loss from 0.541793 to 8.636490 mV. At those contacts,
illustrative 1/10 Ω per-node resistance yields 12.634790/47.224500 mV.

Three finite workloads after both banks are loaded draw 6.817498, 7.028776 and
6.835193 mW for idle, replacement and a running branch loop. All 38,497 signal
pins are natively annotated, with no unknown connected waveform bit. Combining
replacement, the highest observed workload, with 10 Ω feeds gives 36.620100 mV
conservative loss. These are static nominal sensitivities, not package
qualification, a universal activity bound or a transient/timing result.

Two failed runner setups remain recorded. The first trace set left an unwritten
bank unknown; the second initialized both banks but its initial analysis
annotated zero pins. Those three successful tool exits are rejected as workload
measurements. Corrected cell-pin VCDs use the pinned reader's slash-separated
scope and refuse incomplete annotation before interpreting power. The evidence
audit checks 273 input identities and 220 artifacts, including all failed and
rejected attempts. A byte-identical report replay and targeted refusal controls
are retained with the study validation.

Continuation cost is 430.957 CAD seconds; campaign cost is now 8,843.120 seconds
of 28,800. All native containers are absent, frozen inputs are unchanged, no
physical/PDK/Lean edit occurs, and no route is added. A remains unaccepted; B is
not admitted. Actual parent connection geometry, supply tolerance/impedance and
an applicable activity/voltage envelope are the next power inputs. SRAM and
fast-condition provider questions remain unresolved and unsent.

## 2026-09-29 — portable A, fresh-source interpretation and power request

Completed the authorized [local continuation](local-iteration-continuation.md)
from merged source `727525954dd170cc41279acdf99aecaa35493e87` on local branch
`codex/portable-paired-iteration`. The
[manifest](../../physical/experiments/local-iteration-results.json) binds new
checker/test sources and all decisive receipts. Original acceptance and
physical-study manifests are unchanged; no external publication occurred.

The retained source had dangling tool/PDK links after an earlier worktree's
retirement. Pinned official archives and five standard-cell files were recovered
locally with exact historical hashes. Complete preflight recovered **749 files /
602,275,665 bytes**; a preliminary 742-file inventory remains recorded. The final
bundle moved from `build/retained/` to `build/portable/` before replay. The first
replay compiled its snapshot but refused an absolute own-root receipt reference;
the failed `current-a-portable-01` output is retained. The correction derives the
original root from eight commands in the pinned saved assessment, allows only
indexed lookups and changes no receipt/inventory bytes.

The corrected `current-a-portable-02` receipt SHA-256 is
`b9896d8699dccd92c11fb5c6448395531e422e815486922c3a5b2ead24f83bad`.
All 247 current design/format pins match the snapshot; its build invocation
reuses the first run's `.lake` cache. **Eight fresh kernel certificates** pass.
The detailed preserved-checker assessment verifies 740 inputs in **103.385 s**,
returning exactly SRAM qualification, timing conditions and package power as
blockers. Every bundle input remains unchanged. This demonstrates local
assessment portability with retained physical observations, not a physical rerun.

Fresh-source interpretation independently emits both modules and passes
**1,082 local equalities**, the complete session proof and standard-axiom
audits in **475.265 s**. Both unchanged reimports pass; six actual RTL corruptions
and two axiom injections reject. All 252 frozen inputs remain unchanged. Its
schema-2 receipt SHA-256 is
`e98d86f7dce0c5d2c0722166b638a942291517232b73fc24468b0b62012bea79`;
it makes no retained-candidate identity claim.

The power request verifies all 14 retained references from both the surviving
source and recovered local support with identical assessments. Thirteen files
are copied read-only; the unchanged tracked power manifest supplies the final
reference. `package-power-request-02.json` SHA-256 is
`a840316d0af9f8c7a80b8c128da486ad2c3f2fbff5e958ca9e25ca1c85926276`.
Exactly eight absent input classes remain explicit; request readiness and
qualification stay false. Three finite activity summaries are reused; no
waveform simulation or native power analysis is added.

The current clean Lean build passes **233 jobs**. Before the alias correction,
the Python suite passed 596 tests with two skips; final regression passes
**599 total / 597 passed / two platform skips**, with all **46 focused optimized
controls** passing. The final regression receipt SHA-256 is
`9ff54f8c90e16b7b3e864f9ce2134963ff61059683a062d17c9721e17e43d36c`.
Independent final read-only review found no actionable alias/wrapper finding.
The owning studies record commands and limits. Ignored bundles and receipts
remain local dependencies, not durable remote backups.

This continuation adds **zero CAD seconds and zero routes**. Campaign use
remains **8,843.120 seconds**, with three A routes used and two B routes reserved.
A remains unaccepted, B unadmitted and the complete iteration unfinished.
The next local work is a declared activity domain and supported bound; component
qualification and actual integration-source inputs remain external gates.

## 2026-09-29 — Four-mode SPI and a resolved package interface

Delivered the first [established-protocol capability](established-protocol-continuation.md)
on `codex/spi-transaction-refinement`, based on `8ba6b4f`. The
[SPI study](../protocols/spi-transactions.md) defines all four modes, one or two
bytes, continuous CS and the explicit sampler/peer-delay boundary. Universal
reference/compiler/canonical-E64 proofs cover all logical periods and payloads.
The fixed output mapping moves to `uio2–4`, separating SPI MOSI and MISO.
I²C uses explicit pulled-up drive/sense joins; UART and SPI leave them open.

The resolved-wire gate passes twenty matrix cases, delay and capture-slot
controls, active reset/recovery and nine legacy cases in **547.180 s**.
Thirty-three valid program uploads have fresh certificates. Fresh interpretation
passes **1,082 equalities** and component/session proofs in **429.635 s**;
the exact chip RTL and MLIR match the wire gate. The foundation passes all
**33 executable suites and one kernel suite**, with **8,924 theorems** using
standard axioms only, in **1,489.273 s**. Python passes **621 of 623 tests**
with two platform skips and all **39 optimized controls** in **20.584 s**.
All frozen input inventories match at final closeout. Receipt hashes and
source/artifact identities are bound by the additive
[manifest](../../physical/experiments/established-protocol-results.json).

Preserved attempts precede these passes. `pads-regression-probe-01` stopped
after emission because the exact behavioral SRAM model cache was missing.
After hash-checked recovery from the unchanged movable bundle,
`pads-regression-probe-02` ran the legacy cases and correctly refused a changed
SPI compiler source at closeout. Both invoked `pinwheel-host.py demo` with
`--backend paired-validation` and their respective tags; logs/artifacts remain,
but full failure stderr was not saved. The first SPI wire gate was interrupted
with exit 130 to add retained-copy identity checks. The first final Python
wrapper passed its tests but failed metadata parsing on singular `test`; it
produced no success receipt. Corrected fresh-tag runs pass. Earlier discovery
logs retain the old mock-format failure and incomplete test-stub syntax error.

The current-A replay refuses this new source inventory before reusing historical
physical evidence. All **216 historical manifest/fixture artifacts** retain
their base bytes; only the catalog README changes. This is a new digital
candidate with **zero additional CAD or routes**. SRAM qualification,
compatible fast timing and package power remain open; campaign consumption
stays **8,843.120 seconds**, three A routes used and two B routes reserved.
The next capability is bounded I²C recovery and two-payload-byte writes.

## 2026-09-29 — Bounded I2C writes and bus clear

Delivered the second [established-protocol capability](established-protocol-continuation.md)
from SPI base `2837d3e`. The [study](../protocols/i2c-capabilities.md) records
one/two payload bytes, independent ACK flags and first-NACK STOP, plus a separate
nine-attempt bus-clear program. Universal Lean compiler/reference and canonical
E64 proofs cover all timing configurations and consumed digital histories.
External target timing/liveness and raw-wire recovery-edge bounds remain separate.

| Gate | Recorded result |
| --- | --- |
| Lean foundation | 240 imported modules, 18,070 declarations and 9,589 theorems audited with standard axioms only; 35 executable suites, one kernel suite and untrusted-axiom rejection pass. 329 frozen inputs match; 1417.024 s. |
| Resolved I²C package wires | 11 write and 12 bus-clear cases pass, including every first-NACK position, release on pulses 1–9, stuck SDA, bounded stretching and stuck-SCL timeout. Two guarded-high fault controls, active-write reset/reload and clear→write without an intervening chip reset pass. 33 fresh kernel certificates cover 29 positive/control uploads and four canonical altered programs rejected for the intended reasons. 264 frozen source inputs, tools, models, consumed copies and generated artifacts match; 458.911 s. |
| Fresh RTL meaning | 1,082 equalities, component and initialized-session proofs, standard-axiom audits, two unchanged controls, six RTL corruptions and two axiom injections pass. 261 frozen inputs match; 361.618 s. Emitted chip MLIR/RTL equal both the wire gate and the prior SPI checkpoint byte-for-byte. |
| Python regression | 648 tests: 646 pass and 2 platform skips. All 47 focused optimized tests pass; 218 frozen inputs match; 19.764 s. |

Receipt paths and SHA-256 digests:

- `build/host/i2c-capabilities-02/report.json`: `424a2a04ac205c7c0e0a634285e4bfab04573937ac5b9099069ac942edb3da28`.
- `build/validation/i2c-source-readback-01/report.json`: `d08dfa4dfb8cc8ef1bac879855f7750299cc4b0dd76b40cff31d0080e7bd8461`.
- `build/validation/i2c-foundation-01/report.json`: `14f62b2513860f637ae61912837b317220abd83a2dc725eebc13c34b7fd93256`.
- `build/validation/i2c-python-final-02/report.json`: `4482526985c2b9e5870f3791c193d17e5b0bb72388941fee37f316f47d2cfad4`.

The initial debug probe passed two-byte transmission and pulse9 release against
the existing SPI executable. A second probe failed its intended guarded-high
control because immediate SCL resinking could hide the high pulse from the
sampler. Holding high for two callback intervals fixed the test; a new debug
probe and the final fresh gate both produce fault status 7. All probe logs and
debug observations remain retained and hash-bound in the additive
[manifest](../../physical/experiments/i2c-capability-results.json). Debug runs
supply no fresh upload or emitted-chip receipt.

The first fresh wire gate passed, but final review found it fingerprinted only
the simulator launch wrappers. Its passing receipt and the first Python receipt
remain preserved with their narrower source/tool scope. The final rerun binds
actual executables, backend assets, VPI modules and bundled shared libraries,
checks inventory membership at closeout, and pins the compiler backend. System
libraries, loader, shell and Python/Lean runtimes remain environment assumptions.

The final gate freshly emitted/compiled the chip and certified all actual
uploads. Its MLIR/RTL match both the new interpreted artifact and the prior SPI
checkpoint exactly; VVP executable byte equality is not claimed. Four semantic
mutants receive valid image certificates and then fail capture, status,
open-drain or wire-order checks. Wrong capture/status controls preserve clean
bytes, ACKs and STOP, so their rejection is distinct from a wire-format defect.
Recovery→write uses the same Host/Simulation, consumes both retained mailboxes
and has zero intervening chip resets. It does not retry an interrupted write.

All 217 prior physical manifests/fixtures match base `2837d3e`, with only an
additive catalog README row. Zero physical CAD seconds/routes are added; campaign
use stays at 8,843.120 seconds, three A routes used and two B reserved. SRAM
internal qualification, compatible fast-corner conditions and package power
remain open. Next: UART supervisor/buffer circuitry, with unread-result,
rearm and dropped-arrival ownership resolved before integration.

## 2026-09-29 — UART supervisor and retained-result circuitry

Delivered the third [established-protocol capability](established-protocol-continuation.md)
from I²C base `855fd94`. The [study](../protocols/uart-supervisor.md) records the
command-6 arm/stop policy, one-bit session ownership, delayed actual-mailbox
arrival, drop-newest/sticky-overrun rule and abort-versus-flush boundary.

| Gate | Recorded result |
| --- | --- |
| Lean foundation | 243 imported modules, 18,852 declarations and 9,893 theorems audited with standard axioms only; 37 executable suites, 1 kernel suite and untrusted-axiom rejection pass. 336 frozen inputs match; 1453.859 s. |
| Resolved UART/package wires | 30 resolved UART stream cases, 148 actual-mailbox RTL vectors, 8 session controls, terminal modes 6/7, three disabled legacy protocols and 5 semantic corruptions pass. 23 fresh upload and 18 sufficient-clock certificates are kernel checked. 269 source inputs and consumed tool/model/generated bytes match; 371.490 s. |
| Fresh RTL meaning | 984 local equalities connect fresh core/package RTL to the typed circuit for all represented state and inputs; exhaustive state/output proofs and standard-axiom audits pass. Two unchanged controls, eight RTL corruptions and two axiom injections behave as expected. 555 frozen source inputs match; 1098.455 s. Wire/readback chip MLIR and RTL are byte-identical. |
| Python regression | 703 tests: 701 pass and 2 platform skips. All 89 focused optimized tests pass; 224 frozen inputs match; 23.563 s. |

Receipt paths and SHA-256 digests:

- `build/host/uart-stream-supervisor-01/report.json`: `af4a463714e1370bb200c3207c82b48e81713b16c99db3ef95c2b6c7ebcae88a`.
- `build/validation/uart-source-readback-03/report.json`: `1f3989a082e70df6ca441602bbbcbd90646e2c195ee2b22027cec94b133c2f28`.
- `build/validation/uart-foundation-01/report.json`: `c743215b04dcbef09317ad4a2138e4d4eda509b2f397f8c812324d6a46e4066c`.
- `build/validation/uart-python-final-03/report.json`: `766280a1de4331d634ff4a6bf617fc82bce42095f310bb7726a6516591b230cd`.

The fresh wire peer schedules external values independently of DUT state.
Review corrected host decoding to validate before consumption and extended
reservation coverage to the stopped edge immediately after completion. The
RTL interpretation freezes imported JSON before consumption and rejects changes
after import; all exact state, parameter banks, captures and ports are covered.
Successful generated `.olean` imports are frozen before and after dependent
compilation and again at closeout; tampering is rejected.

Development attempts and the failed first full RTL proof gate remain in the
manifest. That gate reached the final core equalities, then the kernel rejected
a generated tactic proof term involving a closed 64-bit equality. The corrected
helper generalizes wide scalar equality predicates and applies small
kernel-proved facts for one-bit guards and padding before proving the surrounding
logic. The imported equalities retain the same circuit claim. Large package
helpers use typed let-bound DAG propositions whose exact expansion is checked
against the original expression trees; their Lean statement text is compacted.
Unchanged endpoint connections must still close in the kernel, and the
standard-axiom audit retains the same trust boundary. The second full gate
passed the core helper and endpoint equalities, then stopped at the observation
theorem because the generated top-level declaration was indented into the prior
proof. The adapter restores that declaration boundary. A subsequent private
package helper compile reached its 600-second bound. Another bounded package
batch exposed a threshold-selection bug: checking each side separately omitted
two equalities whose combined tree size exceeded the compact-proof threshold.
The adapter now uses total equality size, with a regression for that boundary.
A further full package compile exposed two smaller helpers whose generated
closed 64-bit zero-equality reduction was rejected by the kernel; their
proof-local normalization was repaired without changing the imported claims.
Field cuts are proposed from exact bit requirements through masks, slices and
concatenation; finite signatures remain untrusted hints. Small cuts use explicit
kernel-proved index and mask-bit facts, and only checked cuts can be reused.
These diagnostics are retained, and the final gate independently regenerates
all dependencies. The final private package compile passed all 449 helpers,
endpoint connections and the whole standard-axiom audit. Its wrapper then
miscounted axiom-free helpers as missing audits; the original reporting failure
is preserved alongside a separately checked receipt counting all 449 helpers.
The official gate is regenerated independently of those private receipts. Private timeout wrappers that stopped only Lake could leave
its Lean children running; cleanup targeted exact owned probe paths, and those
diagnostics now terminate their owned process groups on timeout. Recorded
seconds are observed wall time, not a performance qualification.
The isolated probes are
debug evidence only. Initial generated Design probes
needed explicit dependent-function application and the Boolean/Prop overlay
bridge; source-equation probe01 failed only an unused-simplification warning.
Direct early compile stderr was not retained in full, so those sources are
debug evidence only. Wire development02 corrected a terminal-fault fixture;
development03 had a duplicate-key report serialization error after detecting
the reservation mutant. Fresh final gates regenerate and certify all uploads.

No universal initialized continuous paired-package theorem is inferred from
the conditional UART observer, logical delayed stream or all-state circuit
theorem. No analog, board-frequency, metastability or lossless-stall claim is
made. All 218 historical physical manifests/fixtures retain base bytes. New
chip bytes differ from the old SPI/I²C checkpoint. Zero CAD/routes are added;
SRAM internal qualification, compatible fast-corner conditions and package
power remain open. Next formal gate: continuous initialized package composition.

## 2026-10-05 — Initialized UART package/lifecycle closeout

Implemented all six checkpoints of the [approved plan](uart-session-proof-plan.md)
on the `07be98c` UART candidate. The [study](../protocols/uart-session.md) owns
the exact domain and reproduction; the
[manifest](../../physical/experiments/uart-session-results.json) binds receipts.
Actual reset/upload/ARM derives execution, memory coverage, policy and observer
correspondence. Resident segments, decoded STOP/certified replacement and
external restart compose every finite prefix; fresh ghost epochs preserve old
packet origins and exact occurrence receipts. The strong timing endpoint includes
the admitted edge's original serial suffix and actual two-edge sampler.

Fresh validation passes: 255 modules, 10,543 standard-axiom
theorems and 39 executable suites; 30 wire cases,
148 mailbox vectors, 23 upload and
18 timing certificates; 984 RTL equalities;
701 Python passes, 2 platform skips and 89 optimized passes.
The failed 600-second readback and interrupted foundation retain their partial
evidence; isolated/fresh replacements supply the completed receipts.

Chip MLIR/RTL remain byte-identical to the existing UART candidate. All 230
historical physical inputs are preserved; zero hardware bits, CAD seconds or
routes are added. The lawful-memory and digital timing contracts remain explicit;
SRAM internal qualification, fast-corner characterization and package power are
separate open gates.

## 2026-10-06 — Reusable programs and compact register reads

Implemented the [reusable-program continuation](../protocols/reusable-programs.md)
on `codex/reusable-protocol-programs`. Named outputs, sampled inputs, captures
and labels expose the existing instructions. A separate resident source grammar
lowers SHIFT/KEEP to the existing paired upload ABI; accepted START supplies a
new byte while the UART/SPI program remains resident. The chip and emitter
sources remain unchanged.

The one/two-byte I²C register-read frontend resolves the capture-capacity
decision: successful payload owns all sixteen slots; timeout or aggregate
NACK/guard fault discards captures. Prefix ACK slots are overwritten only after
all three succeed. Each prefix NACK emits STOP before structural fault. Exact
NACK stage is a reference diagnostic rather than part of the public result;
the earlier precise-ACK one-byte frontend remains available.

The foundation gate passes 261 modules, 20,800 declarations and 11,224
standard-axiom theorems, 41 executable suites, one kernel suite and the
untrusted-axiom rejection. Python has 740 passes, two Linux-only skips and 34
new optimized passes. Resident image certificates cover two positives and eight
proved corruptions. Typed graph tests cover 4,608 SHIFT and 640 KEEP cases.
The source dispatch theorem and local node equations do not yet compose a
universal initialized resident UART/SPI lifecycle proof.

Resolved resident package tests cover every UART/SPI byte, 19 ownership/serial/
reset controls, two certified semantic negatives and five upload certificates.
Actual CLI runs carry `0xa6` through the same UART image and exercise one custom
named ready/branch/pulse image in completed and timeout cases. Sixteen I²C
scenarios, all three first-NACK stages, stretching/timeout, guard loss and
reset/reload pass with 23 certified uploads and four semantic negatives.
Success uses 36/45 clocks; prefix NACK uses 9/18/27. The I²C reference/compiler/
E64 refinement and 196-position bound are universal; fixture capacity is
certified per upload, with 32 canonical records and 23 paired parameters.

Fresh paired core/package interpretation passes all 1,082 local equalities,
standard-axiom audits and corruption controls. Its chip MLIR/RTL match the I²C
pin gate byte-for-byte. Fresh stream core/package interpretation passes all 984
local equalities, standard-axiom audits and corruption controls; its chip bytes
match the resident pin gate and actual CLI runs. The additive
[manifest](../../physical/experiments/reusable-protocol-results.json) binds all
ten final reports. Their closeout rechecks 601 source inputs and preserves all
231 historical physical files. Interrupted source-freeze attempts, failed peer
probes and the 600-second stream proof timeout retain separate diagnostics;
the fresh stream gate passes with the same proof/checks and a recorded
1,800-second per-module bound, in 1,351.138 s.

Resident and I²C chip bytes also match the previous UART
and I²C candidates respectively. SRAM qualification, compatible fast timing and
package power remain open; the new software capabilities add zero hardware bits
and zero physical runs. A JTAG sequence can next exercise the generic builder;
longer dynamic payloads require a separate buffer and ownership decision.

## 2026-10-06 — Unified transactions and a bounded JTAG challenge

Implemented the [transaction workflow](../protocols/transaction-workflow.md)
on `codex/unified-transactions`, with incremental commits. A shared request,
compile, load, run and decode API carries exact program bytes, named pin
requirements, timing, capacities and result interpretation. Fixed SPI/I²C
requests use a static production Lean exporter; resident UART/SPI/JTAG use the
generic builder. Artifacts recompile their request on import. Compiler-owned
construction rejects unrelated request/program pairs before I/O; host image
generations reject stale sessions, including identical reloads. Failed decoding
preserves the unread packet.

The typed resident language adds SHIFT/KEEP beside ordinary Reactive
instructions. Fifteen public proofs cover canonical encoding, source validity,
ordinary compatibility, entry/hold effects and START/reset ownership. Local
selected-graph checks pass 4,608 SHIFT cases, 640 KEEP cases and 35 control edges.
These are admitted-source execution snapshots, not a complete initialized
loader/SRAM/mailbox protocol lifecycle theorem.

The shared package gate passes every START byte for UART, SPI and JTAG without
reuploading between transfers, eight fixed SPI mode/length cases and fourteen
I²C success/stretch/NACK/timeout/guard cases. Eleven controls include pre-I/O
capacity/payload/session refusals and three canonical JTAG semantic negatives;
nineteen actual images receive fresh kernel upload certificates. The independent
JTAG target covers all sixteen initial TAP states and checks a nineteen-clock,
eight-bit LSB-first DR scan. Its 39-half-period wire sequence is distinct from
exact package busy completion. The fixture assumes an eight-bit DR selected by
reset; IR selection, chains and 32-bit IDCODE remain absent. Larger requests
expose the actual eight-bit operand/sixteen-capture limits before chip I/O.

Fresh foundation passes 264 modules, 21,045 declarations, 11,332 standard-axiom
theorems, 43 executable suites, one kernel suite and the untrusted-axiom
rejection. Normal and optimized Python discovery each pass 799 tests with two
platform skips. The public CLI passes UART compile/inspect/run with `0xa6` and
two-byte I²C compile/inspect through the production frontend. Its elapsed host
edge count includes framing, polling, readback and consumption.

The [manifest](../../physical/experiments/unified-workflow-results.json) binds
five completed reports and their source/artifact closeout across 611 unchanged
inputs. Earlier probes and
the failed optimized package-name invocation retain separate records; final
discovery and frozen-source replacements supply acceptance. Chip MLIR/RTL are
byte-identical to the prior paired-stream candidate, whose exact-artifact RTL
interpretation is retained without a new proof or broader lifecycle claim.
All 232 preceding physical files remain unchanged. Zero hardware bits or
physical runs are added; SRAM qualification, compatible fast timing and package
power remain open. The next programming decision is longer data ownership and
its hardware cost, alongside initialized resident refinement.

## 2026-10-06 — Finite-transfer ownership and longer wire models

The [buffered-transfer study](../protocols/buffered-transfers.md) implements the
decision to preload one finite transaction. TX is copied before START, RX space
is reserved, engine access is exclusive and completion stays immutable until
matching release. A pending handle separates submit/wait/read/release; the normal
run copies a result before release. Host timeout preserves execution. Engine
failure preserves diagnostic RX separately from successful payload. Reset and
slot reuse reject stale handles; Python also rejects handles from another slot.

Twenty-three Lean proofs establish parametric per-step/history bounds and
identity provenance, exact TX consumption/RX append, retained completion,
admission, release/reuse/reset. The executable suite checks 21 lifecycle cases,
494 engine bit operations and 798,660 adversarial command edges. Actual Lean
exports agree with Python on 75 cases and 2,630 transitions, including 1,475
rejections. This is finite differential evidence, not a universal Python proof.

The reference engine has generic timed operations and no protocol cases.
Independent resolved-pin peers pass 1,024 four-byte SPI transfers on one unchanged
program and 192 JTAG scans over widths 1/7/13/32 and all sixteen initial TAP
states. Total accepted modeled wire duration is 304,256 edges. Sampling, CS,
final-bit TMS and wire-order mutations are rejected. Normal and optimized Python
each pass 849 tests with two platform skips. Review found and repaired stranded
ownership after callback failure and cross-slot identity collision. A callback
failure after engine completion remains an observation error; the published
completion is not rewritten.

The [manifest](../../physical/experiments/buffered-transfer-model-results.json)
binds the buffered and foundation reports. The target is `buffered-reference-v1`,
with no paired upload/command encoding or changed chip. Its 32 TX + 32 RX bits
are a 64-bit data storage floor before metadata/control, not measured area.
All earlier hardware evidence remains preserved. Dedicated registers versus
an explicit SRAM partition/schedule, versioned engine operations and indexed
readback are the next implementation decision. Longer I²C also exceeds the
current unrolled program limit; physical qualifications retain their gates.

## 2026-10-06 — Shared buffered reactive execution

The [shared execution study](../protocols/buffered-reactive.md) closes the split
between linear buffered data and reactive control. `Program.Buffered` normalizes
into Reactive/Fetch and composes instruction-entry TX consumption/RX append with
Transfer ownership. A generalized counted schedule retains reusable bodies;
the old counted grammar has proved equal span and lookup. Fifteen composed
safety/entry/retention statements, two embedding statements and three I²C
geometry statements use standard axioms. The executable suite checks seven
I²C raw-control scenarios and 4,096 input histories.

Actual Lean/Python differential execution passes 143 cases and 12,240 edges,
including self reentry, wait deadline, guard/capture/dispatch priority, malformed
normalization, exhaustion and partial results. All 270 virtual instructions and
stored geometry of the default four-byte typed I²C factory agree with the
independently wire-checked Python factory in seven cases, with four-cycle phases
and a 32-cycle wait budget. This is finite differential and frontend-binding
evidence; it is not a universal Python or protocol-success theorem.

The same reference interpreter executes the prior SPI/JTAG programs and a
four-byte I²C combined register read. That I²C program stores 50 instruction
leaves and 55 control descriptors for 270 virtual positions without expanding a
bank; quiet wire duration is 993 modeled edges. The independent gate passes
1,036 I²C cases: 1,029 complete, three lawful-STOP NACK faults and four timeouts.
A held clock retains nine RX bits without claiming STOP; failed STOP qualification
retains all 32 bits with timeout. Six framing/data/timing mutations are rejected.
Combined with 1,216 retained SPI/JTAG cases, the gate covers 2,252 wire cases and
1,333,640 modeled edges. Normal and optimized Python each pass 889 tests with
two skips. The full foundation gate builds 269 modules and passes all 45
executable suites, one kernel suite and the whole-library axiom audit.

Review corrected malformed-normalization data effects and distinguished them
from invalid terminal dispatch, which preserves the current instruction's effects.
The [accepted manifest](../../physical/experiments/buffered-reactive-model-results.json)
binds the focused and foundation reports and preserves the preceding physical
evidence. No buffered circuit, current paired image extension, serial transport,
mapped area or physical timing is established. The next gate is a versioned
digital engine with counted lookup, owned data admission and indexed readback.
