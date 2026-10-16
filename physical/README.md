# Physical inputs and experiment records

Start at the [current research decision](../docs/research/status.md), then use the
[technical index](../docs/README.md) to find the study that owns the measurement.
That study gives the prerequisites, comparison conditions, and reproduction
command. This directory holds inputs and tracked records, not a single current
physical design.

| Path | Role |
| --- | --- |
| [`core.json`](core.json), [`core.sdc`](core.sdc) | General-core flow configuration and synchronous timing assumptions. |
| [`chip.json`](chip.json), [`chip.sdc`](chip.sdc) | Whole-chip flow configuration, SRAM macro placement, package timing, and load assumptions. The digital input sampler is not an analog crossing guarantee. |
| [`tt_um_pinwheel_buffered.sv`](tt_um_pinwheel_buffered.sv) | Tiny Tapeout pin boundary for the reloadable buffered SRAM serial engine; see the [contract and current validation](../docs/protocols/tt-buffered-sram.md). |
| [`buffered_tt/`](buffered_tt/) | Exact SRAM supply integration and pinned native placement profile using actual routing capacities; the [historical single-buffer experiment](../docs/physical/tt-buffered-fanout2803.md) retains its rejected comparison. The preceding [two-buffer experiment](../docs/physical/tt-buffered-two-buffer.md) preserves timing but rejects higher coarse congestion. The preceding [42-cell access experiment](../docs/physical/tt-buffered-access-incremental.md) retains its rejected comparison. The canonical recipe stays unchanged. Earlier [fences](../docs/physical/tt-buffered-access-placement.md), [mirroring](../docs/physical/tt-buffered-sram-access.md) and [locality](../docs/physical/tt-buffered-locality.md) studies retain their measured references. |
| [`experiments/tt-buffered-overnight-campaign-results.json`](experiments/tt-buffered-overnight-campaign-results.json) | Latest completed routing campaign: retain C14's 1,732 native records versus 22,115 matched control; C17 regresses. GDS DRC/LVS, antenna and conditional extracted timing fail. [Study](../docs/physical/tt-buffered-overnight-campaign.md) and [backlog](../docs/research/tt-buffered-next-experiments.md). |
| [`experiments/tt-buffered-worktree-retention.json`](experiments/tt-buffered-worktree-retention.json) | Authority for off-worktree build-artifact custody and verification; [source history](../tools/pinwheel-physical-history/README.md) retains producer snapshots. Git source alone is not the measured CAD payload. |
| [`targets/control.json`](targets/control.json), [`targets/paired.json`](targets/paired.json) | Frozen choices of mapped source, macro organization, and state roles for the control and paired comparisons. |
| [`targets/comparison-overrides.json`](targets/comparison-overrides.json) | The retained control comparison's implementation constraint; use it with the owning study's command. |
| [`experiments/`](experiments/README.md) | Tracked selections, policies, repair plans, Tcl edits, and compact result manifests. |

The physical flow generates larger netlists, databases, logs, and reports under
ignored `build/`. A tracked result manifest may name and hash those files even
when a fresh checkout does not contain them. Keep the manifest and its source
paths together when reproducing or comparing a run.

**Evidence boundary:** a successful check or local repair does not by itself
establish whole-chip routing, extracted timing, electrical qualification, or
silicon behavior. Read the manifest's specific decision and the owning study
before reusing its numbers.
