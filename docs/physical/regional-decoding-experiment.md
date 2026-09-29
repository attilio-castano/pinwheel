# Regional decoding experiment — September 25

The subsequent [SRAM distribution experiment](sram-distribution-experiment.md)
completes the full-watchlist and write-interface comparison identified here.
This page retains the regional experiment's original result and remaining work;
[research status](../research/status.md) owns current priorities.

**Regional decoding produces a measured timing gain, but the chip remains
physically unqualified.** Two small logic copies improve the selected
mode-to-status setup path by **0.656426 ns** in the local comparison. Adding two
input buffers removes the copies' new fanout violations while retaining that
gain. A complete coarse reroute retains the improvement and reduces congestion,
but another SRAM path becomes critical and upload-to-SRAM hold margin decreases.

The [result manifest](../../physical/experiments/regional-decoding-results.json)
binds `build/validation/regional-organization-01/report.json`, the plans, actual
databases, readbacks, reports, tool versions and preserved unsuccessful attempts.
It follows the [saved-chip organization study](physical-organization-study.md)
under the [exploratory size policy](../research/README.md#exploration-with-temporary-size-overages).

## What changed and why

A shared logic gate must drive wires to all of its consumers. Computing the
same Boolean value near a second consumer group can shorten those output wires,
at the cost of an extra gate and more work for its input drivers. This experiment
tests that tradeoff without adding state or changing the execution schedule.

The first variant copies `_05733_` (`sg13cmos5l_xor2_1`) and `_09533_`
(`sg13cmos5l_nor2_1`) into nearby empty row sites, splitting each gate's complete
immediate consumer set. It adds **21.7728 µm²**. Two parents then drive nine loads
against the limit of eight. The second variant adds two `sg13cmos5l_buf_2`
branches; each branch drives the original gate input and its copy. The parent
again sees eight loads. Total added area is **39.9168 µm²**.

Every original cell, state element, clock connection, hold-delay cell, macro,
package connection and placement stays fixed. The saved 20 ns timing constraints,
technology views and three corners are retained. Placement checks and actual ODB
power-net bindings pass; detailed pin access is not qualified by these checks.

## Measured comparison

Higher slack gives more timing margin. All values below are estimates from
global routes, including the local probes' incrementally updated routes.

| Measurement | Saved chip | Copies only, local | Copies + input buffers, local | Same buffered candidate, coarse reroute |
| --- | ---: | ---: | ---: | ---: |
| Placed cell/macro area, µm² | 359,371.6704 | 359,393.4432 | 359,411.5872 | 359,411.5872 |
| Selected slow mode → status setup, ns | −0.055813 | +0.600613 | +0.600613 | +1.798552 |
| Worst slow setup, ns | −0.055813 | +0.070047 | +0.070047 | **−0.113646** |
| Worst fast hold, ns | +0.064551 | +0.064551 | +0.064551 | **+0.049847** |
| Global capacitance violations | 4 | 4 | 4 | 1 |
| Global fanout violations | 0 | 2 | 0 | 0 |
| Global slow / fast slew violations | 12 / 0 | 12 / 0 | 12 / 0 | 9 / 1 |
| Complete coarse-route overflow | 33 | — | — | 19 |

The local matched clock paths are exactly unchanged. This supports attributing
the local mode-path gain to the changed data implementation. The full reroute
also changes other wires; no independently rerouted unchanged control isolates
all of its global changes as effects of gate copying alone.

The incremental probes store a partial routing-grid usage view. Their reported
zero grid overflow is **not** a whole-chip congestion result. Only the complete
saved and rerouted grids are compared above; the new grid's 19 overflow units
also match the router's final congestion report.

The original reference area is **358,297.5456 µm²** and the historical +0.3%
allowance is **359,372.438237 µm²**. The buffered candidate adds **0.011141%** of
the reference area and exceeds the old allowance by **39.148963 µm²**; its total
increment over the reference is **0.310926%**. This is an experimental area-cap
overage, not a larger die outline. No complete area-recovery plan was required
before trying it. Later optimization could reuse existing transport cells, but
no buffer removal or area credit is established here.

## What was checked

The two missing XOR-parent measurements and complementary setup/hold checks
are complete. Measurements cover all five previously selected transport families,
the four decoder parents, both old/new gate outputs and both added buffer
branches: **122 / 124 / 126 / 126 connections** across the four variants.
All **1,494 net/corner pin-load checks** reconcile against actual terminals and
pinned libraries. **192 timing witnesses** cover the four selected paths in both
directions, using exact arcs and also unrestricted paths between their endpoints.
All consumed nets have wire estimates; the saved chip's global metrics reproduce.

`physical_decoder_replication.py` validates the declared copies and legal empty
footprints, emits the bounded edit, then independently checks actual ODB and
Verilog readbacks. Identical same-input gates are folded; only declared
noninverting input buffers are contracted. This retains the complete original
signal graph under the pinned cell interpretation. It is a structural checker,
not a new Lean theorem or a new complete package-refinement proof.

The experiment also exposed an OpenSTA report format with a blank fanout slack
column. Count reconciliation caught the missing parsed violations. The shared
reader now accepts that format and rejects malformed or inconsistent rows.
The final portable suite records **463 passed / 2 skipped**, including fourteen
decoder-copy tests and the report-format regression.

Nine CAD container attempts took **169.993 seconds** in total, including one
failed geometry-reader startup. The declared limits were 1,200 cumulative
container seconds, two local candidate variants and one 300-second coarse route,
with two CPUs and 2 GiB per container. No timeout or detailed route occurred.
All containers are confirmed absent. The first signal-Verilog supply-port
expectation, the geometry runtime error and the report-parser rejection remain
recorded with their corrected attempts. Earlier results are untouched.

Portable validation:

```sh
python3 -B -m unittest discover -s test -p 'test_physical_decoder_replication.py' -v
python3 -B -m unittest discover -s test -p 'test_mapped_physical_diagnostics.py' -v
python3 -B -m unittest discover -s test -p 'test_*.py'
```

The manifest binds the run-local preparation, plans, workers, analysis and
sealing scripts. Replaying physical measurements requires those ignored
artifacts, the original saved checkpoint and the pinned CAD/PDK installation;
a fresh checkout cannot reconstruct them from the manifest alone. Use new
output tags and retain every earlier attempt.

## Remaining work and implication for formalization

The coarse candidate still fails the retained **+0.367343 ns setup** and
**+0.079278 ns hold** floors. Its worst setup path is now
`memory.storage/A_DOUT[51] → uo_out[4]`. Its worst hold path is
`r_serial_shift[43] → memory.storage/A_DIN[43]`; `A_DIN[35]` also has a fast slew
violation. The remaining capacitance violation is driven by `_06785_/X`.
The next architectural comparison should address the complete bit-51
distribution and the SRAM write-input timing environment together.

The full **1,152-connection** qualification watchlist and detailed pin-access
checks were not rerun. The narrower family collection and global checks are
enough to reject promotion, not to grant it. The historical fast-corner
cell/SRAM temperature mismatch also remains explicit. Backend promotion,
extracted timing, full layout checks and the paired compiler/admission/package
refinement remain open.

This experiment used the existing Lean-generated circuit; Hardcaml was not
needed for these physical variants. It makes one useful formalization boundary
concrete: one logical computation can have several physical representatives,
with transparent distribution between them. An imported circuit interpretation
should express that relationship while keeping cycle behavior fixed. Generator
choice can remain an exploration tool rather than forcing a rewrite of the
semantic reference.
