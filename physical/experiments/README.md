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
| Seven-net electrical repair | [`balanced-electrical-results.json`](balanced-electrical-results.json) | Declared buffers, conservative import controls, exact edit/revert, full coarse screen and actual circuit checks. [Study](../../docs/physical/balanced-electrical-experiment.md). |
| SRAM interface and internal qualification | [`sram-extraction-results.json`](sram-extraction-results.json) | Qualified 351-pin spelling adapter, passing GDS boundary LVS and rejected wiring faults. Internal SRAM qualification remains rejected; [study](../../docs/physical/sram-extraction-results.md) preserves failed controls and exact geometry evidence. |
| Final layout and SRAM extraction | [`chip-finalization-results.json`](chip-finalization-results.json) | Finished repair preserves original circuitry/wires and passes timing, full-rule GDS DRC and functional checks. GDS extraction/LVS fails; matched pre-repair and standalone SRAM controls identify the next gate. [Study](../../docs/physical/chip-finalization-results.md) retains all failures and boundaries. |
| Chip electrical integration | [`chip-closure-results.json`](chip-closure-results.json) | Five buffers and one diode clear fresh all-corner electrical/timing checks, preserve clocks and pass native DRC/antenna plus independent circuit/pin checks. [Study](../../docs/physical/chip-closure-results.md) retains failed controls and remaining final-signoff gates. |
| Live protection/electrical repair fixture | [`live-closure-results.json`](live-closure-results.json) | Qualified small-fixture repair/reroute/extraction, independent identity and protection checks, rejected native controls, costs and prepared chip intake. [Result](../../docs/physical/live-closure-results.md), [frozen protocol](../../docs/physical/live-closure-experiment.md). |
| Protection/electrical closure assessment | [`protection-closure-results.json`](protection-closure-results.json) | Additive reserve costs, exact source failure reproduction, rejected native restart, router-state diagnosis and proposed integration control. No new route. [Result](../../docs/physical/protection-closure-results.md), [frozen protocol](../../docs/physical/protection-closure-experiment.md). |
| Transport refinement and third A layout | [`transport-split-results.json`](transport-split-results.json) | Two measured-route repairs, passing coarse admission, final layout/circuit checks, remaining electrical rejection, complete load inventory and consumed third A slot. [Result](../../docs/physical/transport-split-results.md), [frozen protocol](../../docs/physical/transport-split-experiment.md). |
| Antenna-load follow-up | [`antenna-load-results.json`](antenna-load-results.json) | Rejected 41-buffer coarse candidate, exact circuit/resource controls, calibrated pin-versus-wire diagnosis, full-flow refusal and preserved allocation. [Result](../../docs/physical/antenna-load-results.md), [frozen protocol](../../docs/physical/antenna-load-experiment.md). |
| Second A detailed layout | [`balanced-detailed-results.json`](balanced-detailed-results.json) | Final layout, extracted timing, remaining electrical failures, independent final-netlist checks, explicit all-corner rejection and consumed A allocation. [Study](../../docs/physical/balanced-detailed-experiment.md). |
| Balanced signal distribution | [`paired-buffer-balance-mapping.json`](paired-buffer-balance-mapping.json), [`buffer-balance-results.json`](buffer-balance-results.json) | Opt-in mapping selection and completed physical experiment. Matched initial stages clear coarse overflow; completed repair gives positive screening timing. Seven electrical nets remain before detailed-route admission. [Study](../../docs/physical/buffer-balance-experiment.md). |
| Validation-isolation mapping | [`paired-validation-mapping.json`](paired-validation-mapping.json) | Frozen prephysical selection for the new opt-in controller. Both mapped corners remove SRAM-to-rejection reachability; the [study](../../docs/physical/validation-isolation-experiment.md) keeps mapped evidence separate from physical admission. |
| Validation-isolation experiment | [`validation-isolation-results.json`](validation-isolation-results.json) | Binds the local proof, RTL/mapped/physical equivalence, failed routing attempts, clock-width control, measured unrepaired coarse checkpoint and resource ledger. Retain the architectural result; physical admission fails. [Study](../../docs/physical/validation-isolation-experiment.md). |
| Complete-design-iteration campaign | [`design-iteration-results.json`](design-iteration-results.json) | Binds the audit, first detailed layout, matched DRC import control, failed calibrated alternatives, image/host/final-netlist checks and resource ledger. [Study](../../docs/physical/design-iteration-experiment.md) records why A remains unaccepted and the next architectural discriminator. |
| Coupled placement, routing and repair | [`routed-repair-results.json`](routed-repair-results.json) | Matched native repair on the retained and coordinated layouts, separately measured preparation/final checkpoints, complete cell-driven signal-net inventory and two failed continuations. The [study](../../docs/physical/routed-repair-experiment.md) separates electrical/setup gains from remaining hold and routing limits. |
| Protected-load hold repair | [`hold-repair-results.json`](hold-repair-results.json) | Twelve native regression checks, a pinned isolated extension and one complete continuation. The [study](../../docs/physical/hold-repair-experiment.md) separates passing timing/electrical screens from five reserve shortfalls and 25 reconciled congestion units. |
| Qualified import and one signal buffer | [`route-import-fix-results.json`](route-import-fix-results.json) | Four native controls, two isolated builds and one buffer candidate. The [study](../../docs/physical/route-import-fix-experiment.md) records exact resource restoration, shortfalls 5 → 4, unchanged clocks/global timing, local hold cost and remaining 25 overflow units. |
| Saved-route import controls | [`incremental-routing-import-results.json`](incremental-routing-import-results.json) | Two unchanged controls preserve route geometry but fail complete resource identity; fresh timing reproduces. The [study](../../docs/physical/incremental-routing-import-experiment.md) records the blocked signal edit and import-repair gate. |
| Routing policy and electrical reserve | [`routing-policy-results.json`](routing-policy-results.json) | Three complete routes, two fresh three-corner collections, an ineffective grid-offset option and a rejected timing-priority follow-up. The [study](../../docs/physical/routing-policy-experiment.md) preserves the zero-electrical-violation hold-repair checkpoint as the reference. |
| Coordinated status/decode placement | [`status-region-placement-results.json`](status-region-placement-results.json) | Two placement candidates, three complete routes, 4,199 connections, an exact new hold-path diagnosis and retained tool failures/recoveries. [Study](../../docs/physical/status-region-placement-experiment.md) records the failed qualification. |
| Control distribution and competing read paths | [`control-distribution-results.json`](control-distribution-results.json) | Two additional variants fail qualification; up to 1,319 connections, actual readbacks, complete-route regression and an explicitly retained interrupted control. [Study](../../docs/physical/control-distribution-experiment.md) records the regional-placement hypothesis tested by the follow-up above. |
| SRAM distribution and write timing | [`sram-distribution-results.json`](sram-distribution-results.json) | Two local buffer variants, unchanged/candidate coarse routes, all 1,252 connections and minimum pin access. [Study](../../docs/physical/sram-distribution-experiment.md) records the gains, new failures and router/grid discrepancy. |
| Regional decoding exploration | [`regional-decoding-results.json`](regional-decoding-results.json) | Two actual variants and one coarse reroute, with explicit size overage, exact-copy evidence and failed final qualification. The [study](../../docs/physical/regional-decoding-experiment.md) separates local gains from complete-route results. |
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
