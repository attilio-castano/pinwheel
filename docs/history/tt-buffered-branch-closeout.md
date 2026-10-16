# Buffered Tiny Tapeout branch closeout

Recorded 2026-10-16 on `codex/tt-buffered-physical-research`. The work started
at `c46786f`; current main's license and explorer changes through `463053e`
were merged locally. The executable source snapshot validated below is
`af64522134f000abb89ceead5a46d69f7cdab671`. Later custody and documentation
records do not change those executable sources.

The progressive commits separate the TT wrapper and public-pin gates, frozen
physical preparation, historical helper sources, placement comparisons,
routing/RC/timing studies, native preservation and campaign execution,
postroute qualification, diagnostic observers, evidence retention, research
closeout, attribution and platform-specific test guards. Historical failed
attempts stay failed. The source archive preserves 936 exact helper snapshots;
they are not 936 newly accepted implementations.

## Validation and remaining check

| Check | Result and scope |
| --- | --- |
| Final serialized Python suite | **Passed: 1,151 tests, six skipped.** Includes the four explorer tests added by current main. |
| Physical-tool host tests | **Passed: 255 tests**, across campaign, qualification, three observer versions and evidence retention. These use temporary/fake execution or declared retained fixtures; no CAD was launched. The final retention suite was repeated after its macOS guards changed and passed all 33 tests. |
| Historical helper retention | All **936** mirrors match their original files and manifest. |
| Campaign evidence anchors | All **34** explicitly listed anchors rehashed exactly; this is distinct from full CAS verification. |
| Fresh Lean library and axiom audit | Build passed **301 jobs**; audit passed **26,569 declarations / 14,357 theorems**, standard axioms only. The injected untrusted axiom was rejected. |
| Full foundation executable gate | **Incomplete.** The in-worktree attempt was stopped during UARTRx after recognizing shared fixture paths. Run the complete gate in a fresh isolated source snapshot before pushing, as required by the [validation guide](../validation.md). No new formal theorem or full-gate pass is claimed. |

The first final-snapshot Python run failed one unchanged EOF test: the child
process did not exit within its 50 ms deadline, yielding `TimeoutError` instead
of the expected `RuntimeError`. Concurrent Lean compilation is a plausible
scheduling cause, not a demonstrated one. The serialized complete rerun passed
without a code change. Both logs are retained; the scheduling-sensitive test
remains a future test-maintenance issue.

The stopped foundation attempt created `build/uart/0x53-4cycles.csv` and an empty
`build/uart-rx/`. Source review and filesystem birth times indicate new outputs,
with no observed overwritten historical evidence. The partial gate's receipt
records the limit; the full executable gate remains pending. Lean sources,
core RTL and the serial ABI were unchanged by this closeout.

Validation logs and JSON receipts are under ignored
`build/validation/tt-research-closeout-20261016-01/`,
`tt-research-final-snapshot-20261016-01/`,
`tt-research-serialized-tests-20261016-01/`, and
`tt-closeout-foundation-20261016-01/`.

## Custody and resumption

The [retention receipt](../../physical/experiments/tt-buffered-worktree-retention.json)
owns the actual whole-build copy, manifest pin and verification result.
The [tools guide](../../tools/README.md) explains missing external runtimes,
historical absolute paths and the difference between selected CAS evidence and
whole-build retention. A same-host copy survives managed-worktree removal but
is not an offsite backup or a complete executable environment.

Use the [campaign study](../physical/tt-buffered-overnight-campaign.md) for
physical results and the [research backlog](../research/tt-buffered-next-experiments.md)
for remaining competition and stronger research gates. C14 is a routing
reference, not a physically accepted chip. No new CAD experiment, push, pull
request, submission or worktree removal was performed during this closeout.
