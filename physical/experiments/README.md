# Tracked physical experiments

These files preserve the inputs and compact decisions for experiments described
in the [technical studies](../../docs/README.md). For the active question, begin
with [research status](../../docs/research/status.md); an older result's proposed
next step is historical context.

## Find an artifact by role

| Role | Examples | How to read them |
| --- | --- | --- |
| Comparison results | [`fetch-results.json`](fetch-results.json), [`map-tile-results.json`](map-tile-results.json), [`paired-controller-results.json`](paired-controller-results.json) | Measurements and source identities for a bounded candidate or comparison. The corresponding study explains which gate was run. |
| Saved physical results | [`physical-target-results.json`](physical-target-results.json), [`paired-route-results.json`](paired-route-results.json), [`paired-locality-route-results.json`](paired-locality-route-results.json) | Receipts for specific physical stages. Check the decision and per-stage admission fields; a `status` of `passed` can mean evidence collection succeeded while route qualification failed. |
| Selection, contract, and policy | [`paired-route-selection.json`](paired-route-selection.json), [`paired-path-contract.json`](paired-path-contract.json), [`paired-locality-policy.json`](paired-locality-policy.json) | Freeze the source checkpoint and scope of a proposed comparison; they are not measurements by themselves. |
| Repair plan and edit | [`paired-signal-repair-plan.json`](paired-signal-repair-plan.json), [`paired-locality-edits.json`](paired-locality-edits.json), [`paired-locality-repair.tcl`](paired-locality-repair.tcl) | Describe or apply edits to a named saved layout. Tcl files depend on exact cells, nets, and checkpoint identity. |
| Flow variants and diagnostics | [`clock-gated.json`](clock-gated.json), [`sram-corridor.json`](sram-corridor.json), [`routing-diagnostics.json`](routing-diagnostics.json) | Explicit configuration changes for a controlled run or diagnosis. |

File families help narrow a search: `sram-*`, `fetch-*`, `map-*`, and
`paired-controller-*` cover architecture and mapping; `paired-signal-*`,
`paired-distribution-*`, `paired-path-*`, `paired-organization-*`, and
`paired-locality-*` follow later physical investigations. Within a family,
`*-results.json` is usually the receipt, while files named `*selection*`,
`*contract*`, `*policy*`, or `*plan*` declare what was selected or allowed. Read
the file's actual fields before inferring its role from its name.

From the repository root, search filenames with
`rg --files physical/experiments | rg 'paired-(signal|distribution|path|organization|locality)'`.
Search the [technical index](../../docs/README.md) or the owning study for a
manifest reference and reproduction instructions.

Larger run outputs live under ignored `build/`. Tracked manifests record paths,
hashes, status, and decisions; they do not make missing generated artifacts
available in a new checkout. Do not rename a historical input or receipt merely
to tidy this directory: other manifests and study commands may bind its literal
path or digest. A local repair, coarse route, and extracted whole-chip result
are separate evidence gates.
