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
| Physical run | [`prepare-physical.py`](prepare-physical.py) or [`prepare-chip-physical.py`](prepare-chip-physical.py), then [`run-physical.py`](run-physical.py) and [`report-physical.py`](report-physical.py) | Freeze inputs, execute the selected core or whole-chip flow, and collect evidence. CAD/PDK setup and the run's scope come from its study. |
| Physical target, saved-layout checks, and repair | [`physical_target.py`](physical_target.py), [`check-mapped-physical.py`](check-mapped-physical.py), [`probe-physical-repair.py`](probe-physical-repair.py), [`check-physical-organization.py`](check-physical-organization.py) | Bind a mapped source to physical state or test one declared repair or organization on a matching checkpoint. These checks have narrower claims than full routing. |
| Route and timing diagnosis | [`diagnose-routing.py`](diagnose-routing.py), [`check-routing.py`](check-routing.py), [`check-targeted-timing.py`](check-targeted-timing.py) | Inspect retained evidence and exact launch or routing conditions; diagnosis alone is not sign-off. |
| Design alternatives | `check-sram-*`, `check-prefetch.py`, `check-map-tile.py`, `check-tiled-chip.py`, `check-paired-*` | Bounded functional, mapping, timing, or physical comparisons. Their names do not imply that a variant became the retained design. |

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
