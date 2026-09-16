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

## Future receipt shape

Record the actual date, study/run identity, source commit or candidate digest,
evidence location and digest, completion/interruption state, concise result,
resource accounting when available, and link to the result or current status.
For outside research, link the source interpretation and adoption decision in the
owning study. Interpretation-only updates need no fabricated run identity.
