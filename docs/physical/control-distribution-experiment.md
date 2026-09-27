# Control distribution and competing read paths — September 26

**Retain the preceding 34-buffer SRAM design as the physical starting point.**
Neither new variant qualifies. Four additional buffers pass local timing and
electrical checks, but complete routing regresses setup, capacitance and
congestion. Three further buffers clear local electrical limits and improve the
targeted read paths; a different path becomes limiting before setup reaches its
comparison floor. The seven-buffer variant has no complete-route result.

The [manifest](../../physical/experiments/control-distribution-results.json)
binds `build/validation/control-distribution-01/report.json`, all completed and
interrupted attempts, source versions and raw measurements. The
[preceding SRAM study](sram-distribution-experiment.md) retains its original
result; [research status](../research/status.md) owns the next decision.

The later [coordinated placement comparison](status-region-placement-experiment.md)
tests the proposed next step and also rejects physical qualification. Its result
supersedes this page's historical next-step text; the measurements below remain
unchanged.

## What was tested

The initial collection extends the preceding 1,252 connections to **1,298**,
covering the complete affected transport families and the fresh bit-53 path.
It finds another reserve shortfall on `_02877_`: its small gate drives three
consumers about 800 µm away. The original capacitance failure on `_04754_` and
reserve misses on `_02966_` / `_05207_` are reproduced.

The first variant adds three `buf_8` cells for control distribution and one
`buf_4` for `_02877_`. Two branches separate distant consumers from nearby ones;
the other two put all consumers behind a stronger driver. All four buffers fit
legal empty sites within **7.38 µm** of their intended source centers.
Added area is **85.2768 µm²**.

After its complete route, `_02974_` and `_03131_` become overloaded. The fresh
bit-53 and bit-51 paths share another long wire, `_02605_`, whose NOR gate now
takes about 1.2 ns to drive it. Before editing, an explicit supplementary
collection adds fourteen connections and two matched path roles, reproducing
all overlapping earlier measurements. The second variant adds two `buf_8`
cells and one `buf_4`, for **seven additional buffers / 146.9664 µm²** in total.

Original logic, state, cell placements, clock and hold cells, macro geometry and power
bindings remain unchanged. Actual ODB and independently reread Verilog checks
validate each edit against its predecessor. No RTL change or execution cycle is
introduced.

## Results

The unchanged complete reroute reproduces every baseline connection measurement,
selected and write-interface path, and the stored routing grid.

| Measurement | Baseline / unchanged reroute | +4 buffers, local | +4 buffers, complete route | +7 buffers, local |
| --- | ---: | ---: | ---: | ---: |
| Cell/macro area, µm² | 359,776.2816 | 359,861.5584 | 359,861.5584 | 359,923.2480 |
| Worst slow setup, ns | +0.321638 | **+0.556623** | **+0.063407** | **+0.116998** |
| Worst fast hold, ns | +0.089025 | +0.089025 | +0.101286 | +0.101286 |
| Capacitance violations at each corner | 1 | 0 | 2 | 0 |
| Slew / fanout violations at every corner | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| Measured connections meeting 20% reserve | 1,294 / 1,298 | 1,302 / 1,302 | 1,314 / 1,316¹ | 1,319 / 1,319 |
| Minimum SRAM write-data hold, ns | +0.161179 | +0.161179 | +0.125640 | +0.125640 |
| Router overflow | 16 | — | **20** | — |
| Saved-grid overflow | 15 | — | **20** | — |

¹ The complete candidate initially measures 1,300 / 1,302 passing connections;
the fourteen supplementary connections all pass. Incremental routing grids are
partial and do not establish whole-chip congestion.

The retained setup/hold comparison floors are **+0.367343 / +0.079278 ns**.
Positive setup under the 20 ns constraint therefore does not make the complete
candidate pass the comparison. All 64 SRAM write-data inputs retain their hold
floor at all stages. Minimum pin access passes on the four-buffer complete route:
**33,686 standard-cell pins**, zero standard-cell or macro no-access counts,
and no off-grid warnings. The seven-buffer layout has no such full-route probe.

The original area reference remains **358,297.5456 µm²**, with historical
allowance **359,372.438237 µm²**. The four-buffer design is **0.436512%** above
the reference and **489.120163 µm²** above the allowance. The seven-buffer design
is **0.453730%** above the reference and **550.809763 µm²** above the allowance.
The die outline is unchanged. These recorded overages are permitted by the
[exploration policy](../research/README.md#exploration-with-temporary-size-overages);
they do not change the failed timing or routing conclusions.

## Why local gains do not settle the question

The first local edit improves the exact originally critical read path from
**+0.321638 to +1.430525 ns**. Another path limits the global result to
**+0.556623 ns**. Complete rerouting then adds **98.018 ps** to SRAM launch-clock
arrival and **438.541 ps** to the original matched data path relative to that
local result. The fresh worst path falls to **+0.063407 ns**. These are measured
clock and data changes; they do not identify one routing-policy cause.

The second local edit improves its newly targeted bit-53 path from
**+0.063407 to +1.433723 ns**, but the unrestricted result reaches only
**+0.116998 ns**. A mux output, `_06603_/X` on `_02788_`, now takes about
**1.083 ns** to drive two consumers roughly 800 µm away. All **108** matched
local launch/capture clock comparisons remain exactly unchanged.

This supports investigating the whole status/decode region: enumerate competing
read paths and long wires, then compare coordinated placement and distribution.
Individual buffers are useful, but a passing matched path does not establish
that the region or complete chip meets timing. Additional placement freedom is
the next hypothesis, not a demonstrated solution.

## Congestion accounting

The baseline discrepancy is reproduced: the router reports **16**, the saved
grid exposes **15**, and native markers sum to **16**. Fifteen native marker
locations reconcile; one at grid index **[71, 71]** does not.

Inspection of the exact installed OpenROAD commit explains why these quantities
need not agree. The saved grid stores preferred-direction capacity with combined
horizontal/vertical usage, while the router computes overflow separately for
each direction and layer. Native markers come from the 2-D routing graph and
contain no per-layer identity. The unmatched 2-D marker therefore cannot be
identified as the extra Metal4 3-D edge from these artifacts alone.
Sources: [grid storage and directional accounting](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/grt/src/fastroute/src/FastRoute.cpp),
[native marker geometry](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/grt/src/fastroute/src/maze.cpp).

The four-buffer complete route has **20** units on all three measures. Every
marker passes the existing strict grid/flow/guide reconciliation, involving
199 crossing nets. Agreement is established for that candidate; congestion
remains. The historical baseline discrepancy is retained explicitly.

## Execution, verification and reproduction

The six timing collections reconcile **23,505** connection/corner loads,
**624** selected path witnesses and **2,304** write-interface witnesses. All
logical leaves survive across ten recorded transport families. The complete
portable suite passes **471 tests / 2 skips**.

Twelve CAD attempts consume **419.640 seconds** under the 1,800-second bound:
eleven finish successfully and one unnecessary repeat control is stopped.
There are two local variants, two completed coarse routes, and one interrupted
route attempt. Every container is absent; no timeout or detailed route occurs.
Each container is limited to two CPUs and 2 GiB. Including the preceding
regional/SRAM experiments, recorded CAD time is **1,019.273 seconds**.

The interrupted attempt is an execution error, not candidate evidence. The
caller continued after the second local setup gate failed; without an explicit
candidate stage, the runner defaulted to the original baseline. That repeat
control was stopped after **20.567 seconds** and produced no final database.
The input is unchanged. The run-local launcher now rejects missing candidate
stages before creating output or calling Docker; both edit and route rejection
checks pass. The failed receipt, log, time and guard checks remain retained.

The manifest binds **2,311 artifacts / 2,003 source versions**, including plans,
workers, scope extension, independent readbacks, primary-source snapshots and
the interrupted attempt. CAD reproduction requires the retained ignored output,
original checkpoint and pinned local CAD/PDK installation; a tracked manifest
alone cannot reconstruct them. Use fresh output tags and check each preceding
gate before launching dependent commands.

Timing uses global-route estimates, with the historical fast standard-cell
−40°C / SRAM −55°C mismatch retained. There is no new Lean theorem, complete
paired compiler/package refinement, extracted timing, detailed routing, antenna,
power-grid qualification or backend promotion.
