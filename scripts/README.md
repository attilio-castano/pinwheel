# Script entry points

Use [research status](../docs/research/status.md) to identify the current
question and the [technical index](../docs/README.md) to find its owning study.
The study supplies the exact command, prerequisites, comparison artifact, and
evidence limits. Run commands from the repository root; many paths and output
tags are repository relative.

| Task | Entry points | What they establish |
| --- | --- | --- |
| Portable local gate | [`check-foundation.py`](check-foundation.py) | Pinned Lean build, axiom audit, and executable model contracts without CAD tools or prior fixtures. Run the Python unit suite separately as shown in the root README. |
| Protocol, component, and RTL checks | `check-uart-rx.py`, `check-i2c.py`, `check-core.py`, `check-chip.py`, `check-backend.py` | Different model, emitted RTL, oracle, mutation, or synthesis gates. Pick the exact checker and prerequisite chain from the owning study. |
| Interactive host demonstration | [`pinwheel-host.py`](pinwheel-host.py) | Load programs through the chip's serial interface and read retained results from one RTL design. [`pinwheel_host.py`](pinwheel_host.py), [`pinwheel_sim.py`](pinwheel_sim.py), and [`host_demo.py`](host_demo.py) supply transport and peers. |
| Paired image certificate | [`check-paired-image.py`](check-paired-image.py) | Kernel-check canonical E64 to exact paired upload/dispatch correspondence, with six positive images and ten proved corruptions. The paired host checks its actual images before upload. |
| Physical run | [`prepare-physical.py`](prepare-physical.py) or [`prepare-chip-physical.py`](prepare-chip-physical.py), then [`run-physical.py`](run-physical.py) and [`report-physical.py`](report-physical.py) | Freeze inputs, execute the selected core or whole-chip flow, and collect evidence. CAD/PDK setup and the run's scope come from its study. |
| Physical target, saved-layout checks, and repair | [`physical_target.py`](physical_target.py), [`check-mapped-physical.py`](check-mapped-physical.py), [`probe-physical-repair.py`](probe-physical-repair.py), [`check-physical-organization.py`](check-physical-organization.py) | Bind a mapped source to physical state or test one declared repair or organization on a matching checkpoint. These checks have narrower claims than full routing. |
| Explicit timing acceptance | [`physical_timing_acceptance.py`](physical_timing_acceptance.py) | Require setup/hold and cap/slew/fanout evidence for every requested corner; reject failures and missing data independently of flow exit status. Artifact identity, parasitics, corner qualification and layout checks remain caller obligations. [Measured use and tests](../docs/physical/balanced-detailed-experiment.md#completion-checks-and-the-flow-status-trap). |
| Route and timing diagnosis | [`diagnose-routing.py`](diagnose-routing.py), [`check-routing.py`](check-routing.py), [`check-targeted-timing.py`](check-targeted-timing.py) | Inspect retained evidence and exact launch or routing conditions; diagnosis alone is not sign-off. |
| Design alternatives | `check-sram-*`, `check-prefetch.py`, `check-map-tile.py`, `check-tiled-chip.py`, `check-paired-*` | Bounded functional, mapping, timing, or physical comparisons. Their names do not imply that a variant became the retained design. |
| Mapping hierarchy comparison | [`check-tiled-chip.py`](check-tiled-chip.py) with `--organization combined --fanout-limit 8 --compare-flat`; [`synthesis_hierarchy.py`](synthesis_hierarchy.py) | Compare the same RTL with and without retained storage tiles. Check exact instance boundaries and cell ownership through flattening and Verilog read-back; record cost and actual sink loads. [Prerequisites and scope](../docs/physical/map-tile-study.md#explicit-hierarchy-comparison--september-25). |
| Bounded combinational placement | [`physical_region_placement.py`](physical_region_placement.py) | Select a declared status cone, fix state/clock/hold/package boundaries, render an OpenROAD placement, and independently verify actual cells, connections, legal rows and unchanged area. [Measured comparison and limits](../docs/physical/status-region-placement-experiment.md). |
| Independent routed-repair checks | [`physical_routed_repair.py`](physical_routed_repair.py) | Check actual native buffer/delay additions and same-family drive changes against pinned functions at every corner, signal identity, protected geometry, legal rows and power binding. The [hold-fix follow-up](../docs/physical/hold-repair-experiment.md) adds all-corner `buf_16` checking and measures timing/routing separately. |
| Saved-route import qualification | [`physical_route_import.py`](physical_route_import.py) | Compare native segments, complete clock routes and every saved capacity/usage entry; reject false-clean or partly restored imports even when timing and overflow match. [Study and regression evidence](../docs/physical/incremental-routing-import-experiment.md). |
| Native saved-route continuation | [`openroad-route-import`](../tools/openroad-route-import/README.md) | Pinned isolated adapter plus independent edge-demand oracle. Exact no-edit/removal/edit-revert controls precede a measured one-buffer continuation; [study](../docs/physical/route-import-fix-experiment.md) retains physical and tool boundaries. |
| Transparent signal distribution | [`physical_signal_buffering.py`](physical_signal_buffering.py) | Validate declared buffer branches and legal sites, emit a bounded edit, and check actual ODB plus independent Verilog readback. [SRAM experiment and tests](../docs/physical/sram-distribution-experiment.md) include both timing directions and complete-route comparison. |
| Regional combinational copies | [`physical_decoder_replication.py`](physical_decoder_replication.py) | Validate two pinned gate types and optional shared input buffers, render an exact edit, then check independent ODB and Verilog readbacks. [Measured experiment and portable tests](../docs/physical/regional-decoding-experiment.md). Physical timing and complete qualification remain separate. |

Other files here provide independent oracles and vectors (`*_vectors.py`,
`*_oracle.py`), result parsing and reporting (`report-*`, `routing_*`), physical
admission and receipt logic (`physical_*`), and shared command execution
([`validation_run.py`](validation_run.py), [`process_group.py`](process_group.py)).
Some are callable tools; others are imported by the entry points. Use the
owning study's command rather than guessing from a filename.

Most checkers write logs and receipts under ignored `build/`. Use a fresh tag
where the command supports one and inspect the receipt's source identities
before comparing it with a tracked manifest in
[`physical/experiments/`](../physical/experiments/README.md). Proof/model
checks, RTL simulation, mapping, local physical probes, routing, and silicon
each answer a different question.

`check-paired-validation.py` checks the opt-in upload-validation lookup against a hash-bound retained paired-controller report. It reproduces baseline RTL, proves complete emitted core/package equivalence with arbitrary current state and SRAM response, checks independent traces and both mapped corners, and rejects a residual SRAM-to-rejection path. Supply a fresh tag, the baseline checkout and the installed cell-model directory. See the [validation-isolation study](../docs/physical/validation-isolation-experiment.md).

`check-paired-distribution.py` tests one opt-in balanced buffer mapping of that verified circuit. Supply a fresh tag, frozen mapping selection, completed physical receipt and its hash-bound placement context. `mapped_buffer_balance.py` contracts known positive signal buffers and uses the existing distribution helper to build shallow, spatially ordered trees. It excludes clock trees and requires identical nonbuffer connectivity. Both mapped corners, a corruption control and pin replay must pass; fresh physical evidence is separate. See the [balanced-distribution study](../docs/physical/buffer-balance-experiment.md).
