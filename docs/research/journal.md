# Research journal

Concise reconstruction index. [Results](results.md) owns interpretations and
[status](status.md) owns current priorities. Detailed commands and hashes stay
with the technical study and run artifacts. Append decisive receipts; do not
replace a failed attempt with its successful retry.

## 2026-09-15 — Continuous UART reception with unequal clocks

Closed the [continuous clock milestone](../uart-stream-clocks.md), based on
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

Closed the [continuous receive milestone](../uart-stream.md), based on `c133af9`
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

Added the [digital receive contract and compiler](../uart-receive.md) in the
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
- **Disposition:** the [study](../structural-timing.md) owns the model, its
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
- **Disposition:** the [study](../register-enables.md) owns the construction,
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

## Future receipt shape

Record the actual date, study/run identity, source commit or candidate digest,
evidence location and digest, completion/interruption state, concise result,
resource accounting when available, and link to the result or current status.
For outside research, link the source interpretation and adoption decision in the
owning study. Interpretation-only updates need no fabricated run identity.
