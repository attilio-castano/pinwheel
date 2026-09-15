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

## Future receipt shape

Record the actual date, study/run identity, source commit or candidate digest,
evidence location and digest, completion/interruption state, concise result,
resource accounting when available, and link to the result or current status.
For outside research, link the source interpretation and adoption decision in the
owning study. Interpretation-only updates need no fabricated run identity.
