# Clean streaming TT branch: local PR preparation

The source branch is `codex/streaming-tt-clean`, based on recorded local main
`a2bbdb122d2212ef0221fea6179ba83cc616eb9d`. Implementation and migration
validation selected commit `227117fa394cf287d77c84c5bdfe720d9eb8df3c`. The final
preparation commit adds this report only. Nothing was pushed or published.

## What changed

The original 21.68-million-line branch remains preserved. The clean history
excludes 8,610 raw execution files (1.15 GB uncompressed) and retains exact
path/mode/blob/size/SHA recovery metadata for their local bundle. Historical
source bytes and receipts remain recoverable at their original commit; the five
validation adapters are versioned separately on the clean branch. No old result
is relabelled.
See the [cleanup record](streaming-tt-cleanup-20261019.md) and
[recovery guide](local-evidence/README.md).

The repository already ignored `build/`. The campaign also copied raw payloads
into documentation trees and explicitly force-staged ignored archives. Thus both
the output conventions and the publication check needed repair. New execution
outputs belong under ignored `build/<owner>/<attempt>/`; compact conclusions and
reviewed fixtures are promoted separately. Generic ignores now cover future
campaign dates. A read-only artifact gate checks actual staged blobs and every
introduced version across a PR range, including files later deleted. The PR
workflow uses exact event base/head SHAs. No hook or global Git configuration
was installed.

The gate caps ordinary blobs at 1 MiB, non-exempt changed bytes at 25 MiB and
changed paths at 1,000. Its 105 exact legacy exceptions preserve 32,455,490 bytes
of existing fixtures and compact evidence. The one recovery index has a strict
4 MiB/16,000-row limit. These bounds block another gigabyte-scale payload under the current policy;
policy/checker changes remain subject to ordinary review.

[Explicit clean-v1 validation](streaming-tt-clean-validation.md) admits a fixed
reviewed source projection without requiring original history objects. It pins
2,601 original source inputs, five adapter replacements and five additions;
the executed checker and manifest bring the selected projection to 2,608 files.
The recipe baselines are exact compact fixtures, included in the read-only
producer dependency map. Historical mode remains the default. Every fresh raw,
archive, worker/kernel, axiom-audit, tool/runtime, generated-source, complete
state/pin and physical-SV reimport check remains required. Source identity is
not proof acceptance.

The Python snapshot runner now blocks upward Git discovery and inherited Git
context/object overrides. This closes a gap where an archive retained inside a
repository could silently borrow the enclosing repository's objects. Earlier
results retain their original, weaker isolation scope.

## Completed validation

| Check | Result and execution scope |
| --- | --- |
| Lean foundation | Passed the unchanged standard fresh-snapshot gate at `227117fa`: 649 modules; 44,383 declarations / 25,323 theorems audited; eight kernel and 65 executable suites; both injected-axiom controls rejected. All 729 command records closed as expected, including two deliberate rejection exits. Elapsed 3,799.002 seconds. |
| Exact foundation input bridge | All 793 consumed checker inputs plus the snapshot driver are unchanged between the executed source and the final documentation-only tree. The separately retained input bridge checks exact committed bytes; the receipt keeps its executed commit identity. |
| Committed-source Python | 2,142 tests run, 13 explicit skips, no failures; selected and producer commit `227117fa`, 114.827 seconds. Source/archive membership and Python identity passed before/after. |
| Independent checkout | Original `99f75b65`, `787260b0`, `d7a5c0d9`, `71decd66` objects absent; no object alternates. Snapshot Git probe refused upward discovery with exit 128. |
| Portable physical host checks | 115 tests, zero skips/failures; nine guard refusals; no child process/CAD execution or build fixture use; checkout remained without `build/`. |
| Artifact and migration controls | 25 artifact-policy and 17 clean-source groups passed in normal and optimized Python. Rewritten-history fixtures also omit clean provenance commit `31a8f62`. |
| Actual artifact policy | Staged check: 17 files, 896,807 budgeted bytes. Implementation range `a2bbdb12..227117fa`: 771 paths, 777 versions, two commits, 10,263,183 budgeted bytes, no errors. The final preparation commit adds this report only; its staged gate and final range are recorded in local closeout. |
| Explorer | Nine recording tests and committed input/trace/source consistency check passed. |

The 13 Python skips cover absent pinned RTL/SRAM/Yosys fixtures, two Linux-only
process observations, absent native Lean integration libraries in the separate
Python archive, and an optional official geometry template. The complete skip
inventory is retained in the Python receipt. Lean runs in its own fresh source
archive; its outcome does not silently turn those Python skips into passes.

The first attempt stopped at Lean's configured 3,072 MiB compiler limit in
`SpiCoordinates.lean`; that is not a host-OOM claim. A fresh 4,096 MiB attempt
compiled and audited the whole library, passed eight kernel and 33 executable
suites, then the resource guard stopped it when free disk fell below its
unchanged 12 GiB floor. It remains stopped and has no success receipt.

A distinct-inode APFS copy preserved all 5,861 files of that stopped snapshot.
An authenticated continuation passed the remaining 32 suites, with source,
library, original snapshot and input identities unchanged. Its composed receipt
explicitly remains outside the standard fresh-snapshot and runtime-companion
schemas. Independent data review verified all commands and preservation maps.

Disk space later recovered without our deleting anything. The final standard
attempt used an entirely fresh Git archive of `227117fa` and completed the
unchanged gate in one run. All attempts and the separate continuation remain
preserved. All four resource owners closed with confirmed cleanup and no owned
process residue. The disk-floor cause was not established.

All new detailed receipts remain under ignored local preparation/validation
owners. Important identities:

| Receipt | SHA-256 |
| --- | --- |
| Independent local checks, `build/pr-preparation/20261019-01/local-checks-report.json` | `4afd0c87fe7e4bb87b61299d6c852e3b6e3c05b7bfd9bfb5fdde20a14b9f5b19` |
| Python, independent checkout `build/validation/pr-clean-227117f-isolated-python-01/report.json` | `cdd5e3b784659eb7376e9e1f020eedeb49d3eb78587489953e4f7bd2ca741dc1` |
| Foundation, `build/validation/pr-clean-foundation-227117f-04/report.json` | `fc64ab861d5029285d826339820014db8c03f0fea744bebc64708a8a14e65f40` |
| Preservation, `build/pr-preparation/20261019-01/preservation-check.json` | `2e8de198a60a65a8ea37c1d1da6f49724a81bd3a4440ad7a4d37f7ac12152bd0` |

## Preservation and remaining limits

The original candidate and evidence safety refs both remain at `99f75b65`. Both
inherited dirty documents, the 148,580,352-byte bundle and the payload index
match their recorded SHA-256 values. Original ignored build artifacts remain
in place. No disk reclamation or original-history deletion occurred. The clean
worktree is attached to this task.

This preparation validates source and storage/migration boundaries. It is not
a correctness review of every accumulated implementation line. The branch
still has a large source/documentation change and needs normal design review.
No new raw/optimized proof worker, RTL/Yosys integration or CAD/solver job was
run. This fresh source foundation does not establish the separate runtime
companion or a newly source-bound raw/optimized receipt.

A completed clean route, correspondence to the final implemented netlist,
qualified extracted RC/timing, physical signoff and official Tiny Tapeout
precheck remain open; see the [routing campaign outcome](streaming-tt-routing-rc-report-20261019.md).
The local raw bundle is not distributed by a future source-only PR. External
reviewers need separately arranged access if they require those payload bytes.

The proposed PR title/body are saved locally under
`build/pr-preparation/20261019-01/pr-title.txt` and `pr-body-draft.md`. No remote
fetch or CI execution occurred, so current remote-main compatibility is not
claimed. Git whitespace checking still reports 11 inherited warnings in exact
source/captured patches; preparation-authored changes pass whitespace checks.
