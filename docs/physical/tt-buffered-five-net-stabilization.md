# Five-net no-edit stabilization

The two-pass routing test passed. P1 changes only `net8046` from the saved BUF4 checkpoint; P2 exactly reproduces P1. Six fresh native STA cases also passed the 1 ps controls, with zero differences at reported precision across all three corners. No cells, placement, RTL, ABI, clocks or unrelated routes/RC changed.

## Scope and control

The frozen plan permits exactly two dirty reroutes of `_00006_`, `_03109_`, `net8042`, `net8046` and `net9291`, after reproducing the actual BUF4 source in the warm router. P1 may change those five nets; P2 must match P1 in whole inventory, all routes, full native RC, grid usage, raw/saved capacities, NDR and full nominal timing reports. All eight checks passed. All 332 clock routes/RC and unrelated routes/RC remain exact to the original source.

P1 and P2 were each independently loaded for TYP, SLOW and FAST STA. The second set matches the first within 1 ps across global margins, 60 selected terminal contexts, the `_30712_/D` anchor, 6,168 reset contexts and 30 numeric timing/clock metrics. Counts, annotation and full normalized native SPEF also match. These are fresh P1/P2 controls; the original BUF4 timing is a separate diagnostic reference.

## Retained measurements

| Corner | Global setup | Global hold | Setup/hold failures |
|---|---:|---:|---:|
| TYP | 5.674470 ns | 107.727 ps | 0 / 0 |
| SLOW | 39.0763 ps | 265.159 ps | 0 / 0 |
| FAST conditional | 9.068200 ns | 19.5748 ps | 0 / 0 |

Global margins are unchanged from original BUF4. The lowest selected-terminal setup headroom remains 12.524107 ns at `_30602_/D` in SLOW.

`net8046` changes from a 14.4 µm planar connection to a 115.2 µm Metal4 detour: six to eleven segments and native wire capacitance 2.05444 to 11.2978 fF. P2 repeats this exactly. Total native overflow changes 5,230 to 5,229, Metal3 2,285 to 2,284, while capacities stay unchanged; saved preferred-grid overflow is 5,209 in both passes. The detour and native RC also reproduce the prior failed five-net no-edit control, whose failed receipt is preserved.

Only the selected `_30606_/D` timing changes against original BUF4. Its SLOW setup decreases 73.957 ps but retains 15.192603 ns. Its FAST hold increases 27.255 ps to 51.555 ps, leaving 50.555 ps after the 1 ps reserve. That exceeds the target by only 0.555 ps.

| Remaining selected FAST endpoint | Raw hold | After 1 ps reserve |
|---|---:|---:|
| `_30759_/D` | 19.575 ps | 18.575 ps |
| `_30747_/D` | 27.190 ps | 26.190 ps |
| `_30602_/D` | 32.395 ps | 31.395 ps |
| `_34083_/D` | 39.394 ps | 38.394 ps |

## What remains

The global reserved 50 ps hold goal remains unmet. A next bounded repair should reassess these four branches and leave `_30606_/D` and `net8046` frozen, rather than repeat the original five-buffer plan. No hold buffers were added here.

Slew violations remain 2/7/2 at TYP/SLOW/FAST, and fanout violations remain 254 at each corner. Capacitance violation counts are zero. Native global-route RC is estimated, not detailed/signoff extraction. FAST still combines logic at −40°C and SRAM at −55°C; nine selected input/FF-constraint slew-axis excursions are inherited unchanged from original BUF4. Reproducible controls do not establish full model or silicon qualification.

The saved stable P2 checkpoint is `build/physical/tt-five-net-stabilization-route-01/pass2-five/routed.odb` (SHA `0144bcceaef2adb486b85625bc03144bd06341ae8787a4bdc14cb5d5b8d6f39b`), with segments SHA `83f515dc265a5b4a15e8e756ee943ea9c9abf9aec0cef7c2f56d180ab5f485cc`. It is retained for the next experiment, without promoting or changing an existing baseline.

See [results](../../physical/experiments/tt-buffered-five-net-stabilization-results-01.json), [selection](../../physical/experiments/tt-buffered-five-net-stabilization-selection-01.json), [route receipt](../../build/physical/tt-five-net-stabilization-route-01/report.json), [STA receipt](../../build/physical/tt-five-net-stabilization-timing-01/report.json), and [independent final review](../../build/physical/tt-five-net-stabilization-review-01/final-review.json). The total cap includes preparation, CAD, cleanup and closeout; both owned containers are absent and all 507 protected source hashes match.
