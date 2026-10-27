# 8×4 curated integration boundary — 26 October 2026

This branch prepares the completed 8×4 work for review. It retains the earlier
completed flow and the latest completed nominal extraction reference component,
while deferring the unfinished 48-hour campaign machinery. Routing has completed
on a preserved seed; the extraction model and qualified timing remain open.
This preparation does not publish a PR, restart a campaign or confer tapeout
acceptance.

## What is included

The integration starts from main `df48101b2d94a5b1cdaadd3680e0342dcb257ed1`
and imports the completed tree at
`6d5d66f505a67efe9588c8cb068285ae85f580ce`, then the exact additions listed
below. The 131 research commits are preserved separately; they are not the
curated branch's ancestry. Historical producer identities must therefore be
recovered from the preserved history when a validator requires them.

The completed tree retains the 8×4 implementation, earlier physical-flow and
extraction experiments, correspondence proofs, physical and official-check
readers, tests and reports. The design keeps its 64×64 bank, depth-two queues,
6,039 semantic bits, declared protocol capacities and 20 ns/full-I/O contract.
Historical producer files are retained byte for byte.

The additional source set is deliberately small:

| Exact files retained from the latest campaign | Reason |
| --- | --- |
| `scripts/streaming_8x4_closure48_reference_completion.py`, `streaming_8x4_closure48_reference_context.py`, `streaming_8x4_closure48_reference_readback.py` | Produce and independently reopen the completed nominal reference component. |
| `scripts/streaming_8x4_closure48_policy.py`, `streaming_8x4_closure48_resources.py` | Preserve the component's exact policy and resource authority. |
| `scripts/streaming_8x4_antenna48_probe.py`, `streaming_8x4_antenna48_probe_readback.py` | Preserve source/input dependencies sealed by the reference execution; their presence does not accept an antenna repair. |
| `test/test_streaming_8x4_closure48_reference_completion.py`, `test/test_streaming_8x4_closure48_resources.py`, `test/test_streaming_8x4_antenna48_probe.py` | Retain focused controls for those exact sources. |

The three retained reference documents are the
[completion protocol](streaming-8x4-closure48-reference-completion-20261025.md),
[reference checkpoint](streaming-8x4-reference-checkpoint-20261026.md) and
[golden-reference request](streaming-8x4-golden-reference-request-20261026.md).
The seven source files are the reference job's complete post-baseline source
dependency set. The three tests cover those retained sources; retaining them
does not qualify the rest of the campaign.

The full committed research diff contains 69,099 added lines across 457 files.
The earlier completed tree accounts for 51,054 lines; the selected seven sources,
three tests and three reference documents add 2,046. The initial curated
integration at `7352330`, including recovery tooling and documentation, had
**54,079 added lines across 380 files**. Later review repairs add self-contained
test inputs; they are recorded separately below. The 85 deferred campaign files remain recoverable. The
original checkout also retains 5,367 untracked draft lines, outside either
committed diff. The curated branch is `codex/streaming-8x4-curated` in
`/Users/attiliocastano/.codex/worktrees/pinwheel-curated-8x4/pinwheel`.

## What the evidence establishes

Acceptance remains tied to the exact target database
`f516ffbca3cd86e5cd214c515ca0be457a91a517dbe715caa47336aec907eee0`.
The [completed campaign report](streaming-8x4-closure24-morning-report-20261025.md)
owns the detailed baseline receipts. A changed layout needs its own affected
proof, physical and model-applicability checks.

| Gate | Current conclusion | Remaining condition |
| --- | --- | --- |
| G1: routed physical target | Ordinary detailed routing completed from the preserved seed with zero route DRC. | The OpenROAD antenna check remains open at one net/two failing pins. Full fresh clean-start reproducibility is also open. |
| G2: qualified extraction model | A new nominal numerical reference component passes; all eight original model-coverage rows remain open. | Independent physical references, complete stack/context/range coverage, corners and heldouts, with accepted consumer comparisons. |
| G3: qualified extracted timing | Open; diagnostic nominal hold failures remain. | An admitted extraction model and passing timing on the same target with justified RC/cell corners. |
| G4: digital correspondence | Passed on the exact f516 target, including the private audit and finite public-wire checks. | Reopen affected obligations for any adopted target change. |
| G5: physical and official checks | Passed on the exact f516 target: GDS DRC, foundry GDS antenna, transistor LVS, power connectivity/views and all nine applicable official checks. | Reopen affected checks for any adopted target change; these checks do not close the separate OpenROAD antenna or qualified-timing gates. |

The full-closure and predefined partial-closure verdicts remain false. The
foundry GDS antenna pass and the remaining OpenROAD cumulative antenna failure
are separate observations with different scopes.

### The extraction progress retained here

The new nominal composite independently reopens 27 historical successful grids
and joins five fresh completed grids: **32/32 grids across eight exact nominal
TYP finite-2D cases**. Maximum mesh change is **0.983710%** and maximum domain
change is **0.853374%**, both below the unchanged 2% gates. Complete 1×1/2×2
matrices, ground-row sums and coupling entries are included. The original timed
out grid 027 and its incomplete expanded packet remain failed.

The independent component readback is
`rc-reference-completion48-independent-readback-01.json`, SHA-256
`00e7efa944330f70a9a9b321ab6334c811ba1e38118541e3922d75fe2e6eac99`.
The composite audit is `rc-reference-composite32-independent-audit-01.json`,
SHA-256 `4d75e83da017dcd6b810f3e0062ea8b19bed62fca53f9e1d0ddcbc04f2936c32`.
Their raw observations remain in the original ignored build evidence owner.

This closes a bounded numerical component. It does not establish continuum
error bounds, finite-wire/3D physics, foundry process corners, actual-route
accuracy or a qualified extraction model. The eight still-open rows are
resistance, ground capacitance, coupling capacitance, via resistance, dielectric
interfaces, layer coverage, width/spacing range and consumer units/semantics.
The [checkpoint](streaming-8x4-reference-checkpoint-20261026.md) states the
missing authority in each row. The first-reference decision was NO-GO for full
model regeneration; no renewed FasterCap conditioning search is admitted.

### The latest antenna attempt remains unfinished

The latest repair applied the exact net840 change and produced database
`e982e1a2949db8d6f34ef2666002b31be2a770093a0631e98b3442a27387c8f4`.
Its fresh Tcl checker then aborted on the literal `$out/fullbox.drc` path
(`ODB-0269`) before accepted DRC/antenna results. A proposed Tcl boundary repair
was exercised with stubbed leaves; it is not a native physical pass. No new
target was accepted and no full Policy-2 routing run followed. The f516 results
remain the accepted target-specific evidence.

The remaining 48-hour antenna drivers, observer/envelope work and unfinished
new-target proof/signoff helpers are deferred from the active PR. Neither their
source preservation nor the integration imports promote them to accepted
tools. The two registered physical policies and the original campaign clocks
remain unchanged. This curation launches no CAD work.

## Preservation and recovery

The original research checkout at
`/Users/attiliocastano/.codex/worktrees/dc52/pinwheel` remains unchanged, including
its 20 untracked drafts. Its branch is
`codex/streaming-8x4-extraction-48h-20261025` at
`2f0524c30c50c647a987154b583554a68a72e194`.

The complete source history is additionally preserved in the local bundle:

```text
/Users/attiliocastano/Developer/pinwheel-archives/pinwheel-research-2026-10-26/pinwheel-research-2f0524c.bundle
bytes: 27148780
sha256: 198dcf8a21c8184aec6472dda856eabb9b0692b7d2f4b7a00257ce2f63fa1caf
```

The 20 untracked drafts have a separate 90,608-byte archive in the same archive
directory, `untracked-drafts-2f0524c.tar.gz`, SHA-256
`1e34352f6ae34b3cc73d8d17fb34c1458613750181b36f228275f257831fcedc`.
Untracked files are outside the Git bundle and tracked-source catalog. The
[source catalog](local-evidence/streaming-8x4-curation-20261026/source-catalog.json)
records the tracked source sets, bundle identity and recovery boundary. The
[source recovery CLI](../../scripts/streaming_8x4_source_recovery.py) provides
the corresponding verification/recovery entry point. Deferred files remain
research sources recoverable from that history, rather than active curated
drivers.

For source recovery, first create a new ignored parent directory. Both outputs
below must be fresh paths; existing repositories or directories are refused:

```sh
mkdir -p build/streaming-8x4-source-recovery/manual
python3 -B scripts/streaming_8x4_source_recovery.py verify \
  --bundle /Users/attiliocastano/Developer/pinwheel-archives/pinwheel-research-2026-10-26/pinwheel-research-2f0524c.bundle \
  --repository "$PWD/build/streaming-8x4-source-recovery/manual/source.git"
python3 -B scripts/streaming_8x4_source_recovery.py restore \
  --repository "$PWD/build/streaming-8x4-source-recovery/manual/source.git" \
  --destination "$PWD/build/streaming-8x4-source-recovery/manual/source"
```

The helper authenticates the bundle and complete tracked tree, then restores
raw blob bytes and executable modes without checking out or executing archived
source. The compact index separately pins all 85 deferred files. Its success
output keeps physical acceptance, model qualification and timing acceptance
false; the recovered directory has no `.git` or runnable evidence context.
Failures may leave partial owned output; preserve it and retry at new paths.

Recovery of source history is distinct from relocation of physical evidence.
The bundle does not contain ignored build outputs, raw PDK files, container
images, runtime installations or hardware observations. A local archive and
its digest do not establish an off-host backup or make missing bytes available.
The separately preserved drafts likewise establish no completed execution.

Historical validators may require both immutable producer Git objects and
exact source-file hashes, as well as the original evidence paths. Use the
preserved historical source checkout and original evidence owners unless a
relocation has been separately verified. Do not substitute current curated
source bytes, rewrite receipt metadata or transfer target-specific acceptance
to make a historical reader pass. Restoring source does not constitute a fresh
proof, physical rerun or portable hardware-evidence package.

## Initial curation validation — 26 October 2026

The code candidate was local commit
`28fd1efde94c2428fb2a3ea992a53e44f42935a7`; subsequent changes complete this
report and its status/index links. Those checks preceded publication of PR #17.
This dated section retains the original failed result; current validation is below.

| Curation check | Result |
| --- | --- |
| Exact retained bytes | All 359 baseline paths and the 13 selected later paths match their original Git blobs. |
| Original research preservation | Original HEAD and tracked tree unchanged; all 20 draft paths, hashes and modes unchanged; bundle and draft-archive digests verified. |
| Reference/probe/resource controls | 36 tests pass. |
| Source-recovery controls | 19 tests pass normally and with Python optimization enabled. |
| Actual source recovery | A fresh bare repository verifies the complete bundle; all 3,628 files / 75,784,978 bytes restore. An independent comparison against the original Git tree matches every SHA-256, mode and path. |
| Portable physical-host workflow | Guard self-tests and all four suites pass: 52 + 16 + 21 + 26 = 115 tests, zero skips; repository build tree absent during these checks. |
| Artifact publication | All 25 policy tests pass. Staged and committed-range checks pass with the retained baseline policy; no new exceptions or enlarged budgets. |
| Explorer | `python3 -B scripts/build-explorer.py --check` passes. |
| Independent source review | Retained import closure and frozen source hashes match; no missing local imports in retained 8×4 test modules. |
| Complete fresh-source Python discovery | **FAILED**: 2,852 tests in 112.975 seconds; 2 failures, 46 errors, 15 skips. |
| Whitespace | One preserved baseline fixture has a blank final line at `test/fixtures/streaming_8x4_pg_diode_profile.lef:113`; its bytes were retained. Curation-owned files pass the whitespace check. |

The broad discovery result is deliberately retained as failed. Its 46 errors
comprise 40 missing ignored campaign-fixture dependencies, four tests requiring
`git rev-parse HEAD` inside the intentionally Git-free archive, and two legacy
clean-source fixture errors. That clean-source fixture also causes the two
failures: its frozen authority rejects the retained baseline
`tools/artifact-policy.json` bytes. Both files remain unchanged from their
respective source versions; the old authority has not been resealed to accept
new bytes. These fixture/isolation seams must be resolved before claiming a
portable green repository suite. The earlier working-checkout 8×4 discovery
likewise failed: 675 tests, 40 errors and one skip.

The full discovery ran from the exact committed-source archive with no copied
build fixtures or parent Git discovery. Membership was verified before and
after, and the Python executable identity was unchanged. Local receipts remain
ignored under:

```text
build/validation/curated-8x4-20261026-01/report.json
build/validation/curated-8x4-20261026-01/logs/python-unittest-discover.log
build/validation/curation-audit-20261026.json
build/streaming-8x4-source-recovery/curation-20261026-01/verify.json
build/streaming-8x4-source-recovery/curation-20261026-01/restore.json
build/streaming-8x4-source-recovery/curation-20261026-01/independent-comparison.json
```

The integration is prepared for source review, with the broad validation gate
open. No CAD, Lean proof, extraction solve or signoff campaign was launched.
Historical execution receipts above remain historical evidence and were not
rerun during curation.


## Review repairs — 27 October 2026

Commit `9271ffc14df36bcc5dae2ed8ec7f1cbf15951d60` repairs the two review findings.
Portable controls now use compact committed geometry, parser and arithmetic
inputs. Reference suites share a fixture helper rather than importing another
discoverable test module. Exact historical plans, source captures, leases and
execution receipts remain explicit replay checks. The new inputs include
87,682 bytes of authenticated policy/LEF/rule/JSON fixtures, rather than the
ignored campaign directories. Synthetic matrices and counters establish
software behavior only; they are not physical observations.

The authenticated `retained-rules.txt` fixture preserves 17 trailing-space
lines from its original parameter bytes. Whole-diff whitespace checks report
those lines and the earlier LEF fixture's blank final line; neither input was
reformatted to silence the check.

The clean-source fixture uses the original 38,068-byte publication policy,
authenticated against the unchanged historical authority, instead of today's
42,744-byte policy. The current policy and production admission checker remain
unchanged. Four source-body controls now supply an explicit synthetic commit
identity to their existing non-admitting mode, so they do not discover a parent
Git repository. Real committed-source admission still requires its original
Git object and byte checks.

Before repair, the focused clean-source suite had two failures and two errors;
8×4 discovery had 40 errors. After repair, the clean-source suite passes all
19 tests in normal and optimized Python. The 8×4 suite passes 750 tests with
22 reported skips. Historical replay requested against missing evidence fails
with zero skips; the replay-switch controls also verify rejection of changed
inputs. Independent review found no production-script, physical-authority,
current-policy or numerical-threshold changes.

Complete committed-source Python discovery **passes**: 2,896 tests in
120.273 seconds, zero failures/errors and 35 explicit skips. Twenty skips are
the opt-in historical checks; the other fifteen retain unavailable tool or
integration prerequisites. Selected archive membership was verified before and
after, with unchanged Python executable identity. The receipt SHA-256 is
`4502414a93277ec9f7f11b00cfd9333784a5587072d30397f7615887c77a6ffc`.
This closes the portable Python regression gate for this source commit; it does
not claim historical replay, native Lean/CAD validation or physical acceptance.

Focused logs are under `build/validation/review-fixes-20261027-01/`; the new
committed-source receipt belongs to
`build/validation/review-fixes-8x4-20261027-01/report.json`.

Portable discovery uses the standard command, with no campaign build outputs:

```sh
python3 -B -m unittest discover -s test -p 'test_*.py'
```

Historical replay is a separate explicit request:

```sh
PINWHEEL_RUN_HISTORICAL_TESTS=1 python3 -B -m unittest discover -s test -p 'test_streaming_8x4*.py'
```

The explicit replay runs the original checks and fails if their authenticated
inputs are absent or changed. It does not relocate machine-specific paths or
launch a new CAD, proof or numerical campaign. Default historical skips must
remain visible in reports; portable success supplies no replay or physical
acceptance claim.

## Next workflow-debt cleanup boundary

The causal problem is shared context: current software controls, immutable
historical replay and expensive physical acceptance have depended on the same
checkout and campaign directories. The repair separates the first two at the
test boundary. Further cleanup should keep that separation explicit:

1. Maintain one documented portable discovery command and one explicit replay
   mode. Require the committed-source archive check in the PR validation path;
   keep its skip inventory. Stop at a reproducible source regression gate.
2. Resolve historical inputs through their existing immutable source/evidence
   owners, while current code evolves normally. Never reseal an old receipt to
   accept today's bytes. Stop after demonstrating recovery and rejection on one
   representative old workflow, not after building a new archive framework.
3. For one future active preparation/readback operation, replace source-string
   rewriting and patched shared globals with explicit input/context arguments.
   Require equivalent ordering, units, error handling and admission decisions on
   positive and negative controls. Stop after that one operation; preserve old
   adapters for historical replay rather than refactoring the entire archive.

The retained tree has 192 `streaming_8x4` script modules, including 19 combining
runtime compilation and source-text transformation. Those counts identify where
to inspect, not a deletion target or proof of incorrectness. The objective is a
shorter reliable iteration loop. It does not supply missing CMOS5L references,
corner authority or qualified extracted timing.
