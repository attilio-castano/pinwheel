# Saved-chip power sensitivity

This recipe audits the [power study](../../../docs/physical/power-boundary-results.md).
It does not qualify a package or change the implementation acceptance policy.
The [protocol](../../../docs/physical/power-boundary-experiment.md) freezes the
900-second continuation budget and exact analysis scope.

## Recheck retained evidence

From the repository root, choose a new report filename:

```sh
python3 -B physical/fixtures/power-boundary/summarize.py \
  build/validation/power-boundary-01 /tmp/pinwheel-power-replay.json
```

This verifies input and output identities, exact baseline drops, declared versus
resolved sources, complete activity annotation and the resource ledger. It
consumes retained waveform/unknown-bit audits through their run input hashes;
it does not regenerate simulation or prove a workload bound. The result manifest
also binds the structured circuit readback, and the retained validation connects
that readback to the original final-netlist lowering receipt.
Compare the result bytes with the manifest-bound `report.json`.

`normalize-vcd.py` rebases the delayed dump without editing values, checks the
known 20 ns window and counts clock transitions. `audit-unknowns.py` connects
unknown waveform bits to the retained Yosys circuit readback and refuses any
unknown connected bit. `summarize.py` additionally checks the actual VCD time
unit. Original and normalized waveforms are retained separately.

## Native reproduction

Use `run-case.py STUDY CASE CAP_SECONDS` with a fresh case directory and a frozen
`request.json`, `case.json` and `worker.py`. The final workers are retained in
`build/validation/power-boundary-01/activity-*-02/`; contact CSVs and all native
Tcl/logs/metrics/PG exports are beside them. A fresh request must bind the exact
chip, libraries and helpers, and account for prior campaign usage. The launcher
requires the pinned image, no existing Pinwheel container, offline execution,
read-only inputs, 4 CPUs, 6 GiB and remaining budget. It refuses reused outputs
and records failure/cleanup costs. Functional simulation uses the same bounded
receipt mechanism with `kind: simulation`.

The native VCD scope must be `power_tb/dut`, with leaf-pin declarations. Check
`vcd 38497` and `unannotated 0` before interpreting any workload result. A tool
exit of zero alone is insufficient. CSV contact dimensions are micrometers;
the solver resistance is per resolved source node. PG SPICE exports audit
source identity only because this pinned exporter omits the external resistance.

`run.py`, `native.py`, `launch.py`, `analyze.py` and `power_tb.sv` are frozen
historical setup inputs, retained to preserve the initial attempt identities.
Use `run-case.py` and the final per-case workers/testbench for native replay;
the historical testbench captures top-level nets only. Preparation scripts,
including the final cell-pin testbench generator and exact workload windows,
are retained under the study's build directory and bound by the result manifest.
