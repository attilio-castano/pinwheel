# Two-pass no-edit routing stabilization

The captured second pass exactly reproduces the first pass's routes, observed resources, RC, nominal timing and physical state. Fresh three-corner headroom checks are complete. The provisional routed control has nine slow-corner setup failures, so it is not timing-closed or promoted.

The routing process ran out of container memory after writing the complete stable snapshots and restoring its runtime guard. Its original failed status is preserved. Independent host review verified the completed artifacts before a separately admitted read-only STA run; that run completed successfully. There was no additional routing pass and no cell sizing.

## Selected protocol and stabilization result

The study began at 23:38:11 UTC on 2026-10-13, with a hard deadline of 00:03:11 UTC on 2026-10-14. It used one warm reconstruction of the saved 8c candidate followed by exactly two identical incremental passes: dirty `_11039_`, `net913`, `net914`, run ten routing iterations, and capture the resulting state. All cell masters, positions, orientations, connectivity and status remain frozen after the saved-state reconstruction.

Pass one changes net913/net914 relative to the saved candidate; _11039_ stays unchanged. Native total overflow changes 5227→5230, Metal3 2282→2285, and saved preferred-grid overflow 5207→5210. Pass two changes none of those routes or totals.

All eight pass-one/pass-two comparisons pass: complete native inventory, canonical route multisets, netlist bytes, raw FastRoute capacities, retained full geometry/grid capacity and usage, native route/NDR state, full nominal SPEF, and nominal timing/report bodies. Both passes preserve all 332 CLOCK routes, every unrelated route and RC network, all PG/macro/pad/pin/row geometry, and routing capacities. Final placement and both power-grid checks pass. The 507 protected sources and six saved-candidate fingerprints remain unchanged.

The observed repeatability is limited to these two passes and captured state. It does not prove convergence for arbitrary future routing passes or equality of unexposed optimizer history. No new baseline has been substituted for or promoted over the original saved candidate.

## Routing process failure and verified artifact use

The source routing report remains failed: coordinator exit 1, native OpenROAD exit −9. The owned Docker container emitted an observed out-of-memory event after complete pass2/measurement/runtime-restoration files were written. Original artifacts and failed logs remain unchanged.

Independent review rechecked both captured states, selected source hashes, full resource/RC equality and fresh owner absence. All 96 source-to-pass1 saved preferred-grid usage changes are explained by net913/net914 route geometry; pass1-to-pass2 changes are zero. The latter is the stability observation. There is no claim of a successful native routing exit or a full hidden-usage-state proof.

A new, explicit completed-artifact admission binds the failed report, raw measurement, all required complete captures, restored runtime guard and unchanged inputs. It permits only read-only diagnostic STA on pass2. The native routing and STA bounds remained 420 seconds and 300 seconds respectively, with 480/420-second phase limits inside the original 25-minute study cap. The routing phase recorded 270.744 seconds all-in; diagnostic STA recorded 95.015 seconds all-in.

## Fresh three-corner headroom

The diagnostic STA uses the actual pass2 ODB and route segments with native global-route RC, nine pinned libraries and unchanged constraints. It imports no lossy SPEF and runs no optimization. It covers all 8 × 257 affected endpoint/context paths per corner, 6,168 in total. The earlier 8c timing is an explicit comparison reference, not a reproduction requirement for the changed routes.

| Corner | Global setup (ps) | Global hold (ps) | Affected hold after 1 ps reserve (ps) | Setup failures |
| --- | ---: | ---: | ---: | ---: |
| Typical | 5674.470 | 107.727 | 1059.547 | 0 |
| Slow | -105.738 | 265.159 | 1827.086 | 9 |
| Fast (conditional) | 9068.200 | 19.575 | 624.333 | 0 |

All hold slacks are nonnegative and the affected-path 50 ps floor passes with a worst conservative value of 624.333 ps. Whole-chip fast hold is 19.575 ps, so the stronger whole-chip 50 ps target remains unmet.

The slow corner regresses from +8.953 ps to −105.738 ps of global setup headroom, a 114.691 ps loss versus 8c. All nine failures launch at rst_n and end at SRAM address pins; the worst is SRAM0/A_ADDR[2]. On its matched path, clocks and the setup constraint remain unchanged. Added net913 loading increases fanout913 cell delay by 63.606 ps; the wire to _19896_/B1 adds 14.467 ps, downstream _19896_ cell delay adds 17.646 ps, and fanout914 adds 8.839 ps. Stability therefore removes a routing-control ambiguity; it does not repair timing.

Electrical counts remain unchanged: slew 2/7/2 at typical/slow/fast, 254 clock-fanout violations at every corner, zero capacitance violations, and annotation 167 unannotated drivers with zero partial drivers. The fast libraries retain logic/IO −40 °C versus SRAM −55 °C qualification. Estimated global-route RC remains distinct from extracted signoff.

## Remaining work

The original buf_4 screen used the old 8c wire RC. Its prior 481.105 ps reserve must not be transferred to this different stable control. The next sizing assessment must use the updated RC and address the nine reset-to-address setup failures while protecting hold. The routing memory failure must also be resolved before treating a future physical route run as successful. No buf_4 replacement, cell move, third pass, baseline promotion, commit, push or submission occurred here.

The [machine-readable result](../../physical/experiments/tt-buffered-pair-stabilization-results-01.json) binds the protocol, immutable failed producer, completed-artifact verification, independent reviews, diagnostic STA and original source evidence. The root closeout records final publication time within the cap.
