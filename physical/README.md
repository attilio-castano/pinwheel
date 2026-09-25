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
