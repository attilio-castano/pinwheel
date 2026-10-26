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

The full research diff contains 69,099 added lines. The earlier completed tree
accounts for 51,054; these seven sources, three tests and three reference
documents add 2,046. That gives an estimated **53,100 added lines before the new
recovery tool, catalog and integration documentation**. Final review statistics
must be measured on the completed curated branch. This boundary removes about
16,000 lines of unfinished campaign machinery from active review while retaining
its recovery path.

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

The 20 untracked drafts have a separate 90,608-byte archive; untracked files are
outside the Git bundle and tracked-source catalog. The
[source catalog](local-evidence/streaming-8x4-curation-20261026/source-catalog.json)
records the tracked source sets, bundle identity and recovery boundary. The
[source recovery CLI](../../scripts/streaming_8x4_source_recovery.py) provides
the corresponding verification/recovery entry point. Deferred files remain
research sources recoverable from that history, rather than active curated
drivers.

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

## Validation of this integration

Validation is pending on the completed curated branch. The integration owner
will record the measured final diff, recovery/catalog checks and focused test
results here before the branch is presented for review. Historical execution
receipts above remain historical evidence; this guide does not claim they were
rerun during curation.
