# Stabilized P2: no-ECO pin-access and detailed-routing probe

The 2026-10-14 probe stayed within the original 25-minute wall cap. Native pin access completed with `stdCellPinNoAp=0` and `macroNoAp=0`. Detailed routing timed out during its initial pass; its last logged observation was **40% complete with 5,994 provisional violations**. There is no completed detailed-route candidate or passing GDS/precheck result.

| Check | Retained result |
| --- | --- |
| P2 source and all 507 protected RTL/ABI/physical inputs | Exact original hashes |
| All 557 staged and bound inputs | Exact original hashes |
| Pre-route cells, placement, net terminals, SRAMs, power geometry, clock topology | Exact saved P2 inventory; 28,970 cells and 332 CLOCK nets |
| Pre-route VPWR/VGND connectivity | Passed |
| Native pin access | Completed; zero reported no-access counts |
| Track assignment | Completed |
| Detailed routing | Pass 0 started; no pass completed |
| Observed detailed-router violations | 5,994 at 30% and 40%; provisional worker-progress counts |
| Final DRC, unroutes and connectivity | Unavailable |
| Violation type, layer, net and location | Unavailable; no marker report written |
| After-route inventory, route layer scope and timing | Unavailable; no after checkpoint written |
| Owned container cleanup | Confirmed absent |

The native command used `-droute_end_iter 2`, allowing inclusive zero-based passes 0–2. The [pinned OpenROAD source](https://raw.githubusercontent.com/The-OpenROAD-Project/OpenROAD/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/drt/src/dr/FlexDR.cpp) initializes the pass index at zero and stops after the inclusive end index. The frozen producer's prose still says `end_iter3`; the actual command and prepared manifest correctly use 2. No fourth pass was possible.

One initial launch failed before pin access because the helper omitted `_PNR_EXCLUDED_CELLS`. The corrected, separately versioned helper retained that failure and used the same original deadline. Preparation, review and initialization repair left a 602-second native subprocess window; execution, cleanup and input verification took 605.092 seconds. The probe then stopped on that bound with exit 124. No additional routing trial ran.

These are actual native observations, not global-route overflow counts. The 5,994 partial violations cannot be compared numerically with the older congestion totals or treated as final signoff failures. Seven `DRT-0349` warnings report unsupported LEF58 enclosure rules without CUTCLASS; a completed native routing run would still require foundry DRC and Tiny Tapeout checks.

The saved P2 remains unchanged. No RTL, ABI, cell, placement, SRAM, power or clock-topology ECO was issued, and no new candidate was promoted. Because the run ended before after-captures, complete preservation of a newly routed database has not been qualified. Clock and signal detailed wires would be new outputs; the retained global-route timing is not extracted timing for those wires.

The next bounded experiment should keep P2 and the same freeze scope, launch the already prepared loader immediately, and request **one complete initial pass** (`end_iter0`) with up to 21 native minutes inside a fresh 25-minute cap. Its acceptance gate is retained DRC markers, connectivity results, detailed ODB/DEF and the complete after-scope audit. Obtain that evidence before choosing a placement or routing repair. This follow-up was proposed, not executed.

Machine-readable results: [tt-buffered-p2-drt-probe-results-01.json](../../physical/experiments/tt-buffered-p2-drt-probe-results-01.json). Native evidence is under `build/physical/tt-p2-drt-probe-02`; source-bound summaries and independent audits are under `build/physical/tt-p2-drt-probe-root-01`.
