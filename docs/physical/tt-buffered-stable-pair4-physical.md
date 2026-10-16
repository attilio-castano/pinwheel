The physical BUF4 pair cleared all nine SLOW-corner SRAM-address setup failures. Fresh native timing measured the actual resized footprints and pin-wire RC after the matched no-edit control. The global zero-failure and affected 50 ps hold gates passed.

Only fanout913 and fanout914 changed from BUF1 to BUF4, growing outward into verified free sites. No neighboring cells moved. The core RTL, serial ABI, clock routes, unrelated routes, macro geometry, rows and power-grid geometry remain frozen. The extra standard-cell area is 14.5152 square micrometres.

| Corner | Control setup ns | Physical setup ns | Control hold ns | Physical hold ns | Setup/hold failures, control to physical |
|---|---:|---:|---:|---:|---|
| TYP 1.20 V / 25 C | 5.674470000 | 5.674470000 | 0.107727000 | 0.107727000 | 0/0 to 0/0 |
| SLOW 1.08 V / 125 C | -0.105738000 | 0.039076300 | 0.265159000 | 0.265159000 | 9/0 to 0/0 |
| FAST conditional | 9.068200000 | 9.068200000 | 0.019574800 | 0.019574800 | 0/0 to 0/0 |

The hold floor applies to the affected reset paths. It is distinct from the chip-wide hold minimum shown above. The full preregistered 1 ps allowance is subtracted from every local minimum.

| Corner | Affected hold raw ps | Reserved affected hold ps | At least 50 ps |
|---|---:|---:|---|
| TYP 1.20 V / 25 C | 844.723 | 843.723 | yes |
| SLOW 1.08 V / 125 C | 1445.675 | 1444.675 | yes |
| FAST conditional | 489.853 | 488.853 | yes |

The nine previously negative address endpoints were:

| Endpoint | Control ps | Physical ps | Gain ps |
|---|---:|---:|---:|
| SRAM0/A_ADDR[2] | -105.738 | 674.751 | 780.489 |
| SRAM0/A_ADDR[5] | -98.259 | 682.229 | 780.488 |
| SRAM1/A_ADDR[3] | -93.054 | 687.434 | 780.488 |
| SRAM0/A_ADDR[4] | -78.392 | 702.096 | 780.488 |
| SRAM1/A_ADDR[2] | -74.992 | 705.496 | 780.488 |
| SRAM0/A_ADDR[0] | -67.198 | 713.291 | 780.489 |
| SRAM1/A_ADDR[0] | -55.028 | 725.461 | 780.489 |
| SRAM0/A_ADDR[3] | -46.651 | 733.838 | 780.489 |
| SRAM0/A_ADDR[1] | -36.938 | 743.551 | 780.489 |

Native congestion remains a separate gate. The capacity arrays, CLOCK routes and every unrelated route/RC network were preserved. Exactly the three permitted signal nets were processed; the actual global-route changes are 0.

| Native overflow | Stabilized P2 control | Physical pair | Delta |
|---|---:|---:|---:|
| Metal2 | 1175 | 1175 | +0 |
| Metal3 | 2285 | 2285 | +0 |
| Metal4 | 1770 | 1770 | +0 |
| Total | 5230 | 5230 | +0 |

Saved preferred-grid overflow changed by 0.0; it is not substituted for the native total.

Fresh control reproduction covered all 6,168 affected path contexts across three corners, with maximum global/affected slack error 0.000 ps at reported precision against the retained native stable reference. Controls ran before the candidate timing processes. Placement, global-route endpoint access, both power nets and the exact two-resize signal-function/inventory scope passed independent checks.

The limiting SLOW setup path is _30953_/Q to engine.memory.storage0/A_ADDR[2] at 39.076 ps. The limiting FAST global hold path is ena (input port clocked by clk) to _30759_/D at 19.575 ps. These remain thin margins. Both stronger chip-wide targets remain unmet: SLOW setup is below 1 ns, and FAST global hold is below 50 ps.
The nine reset paths gain about 780.488 ps, while global SLOW setup improves 144.814 ps as the limiting path migrates. The electrical/check_setup sections are byte-identical at all three corners.

| Corner | Slew violations, control to physical | Fanout violations, control to physical | Capacitance violations, control to physical |
|---|---:|---:|---:|
| TYP 1.20 V / 25 C | 2 to 2 | 254 to 254 | 0 to 0 |
| SLOW 1.08 V / 125 C | 7 to 7 | 254 to 254 | 0 to 0 |
| FAST conditional | 2 to 2 | 254 to 254 | 0 to 0 |

Observed BUF4 input-slew and reported total-capacitance samples stayed within the corresponding Liberty table axes. This check covers those observed BUF4 samples; internal effective capacitance, other cells and endpoint-constraint domains retain their stated limits.

The FAST corner combines logic at -40 C with SRAM at -55 C and is conditional. Detailed routing, pin-access DRC, LVS and extracted-RC signoff remain open. The repaired baseline is not promoted and this result does not mark the competition submission ready.

The accepted routing producer took 307.620 s all-in, followed by 261.286 s for the six-process timing batch. Routing and STA ran sequentially offline at 4 CPUs/5 GiB and 3 CPUs/3 GiB respectively. The initial estimate was extended for helper repairs; earlier failures remain preserved and provide no substitute measurement.

The source-bound [result manifest](../../physical/experiments/tt-buffered-stable-pair4-physical-results-01.json) records selectors, preparations, source/measurement hashes, scope proof and independent reviews. Raw [physical producer](../../build/physical/tt-buffered-stable-pair4-physical-route-07/report.json), [native timing](../../build/physical/tt-buffered-stable-pair4-physical-timing-07/report.json) and [access analysis](../../build/physical/tt-buffered-stable-pair4-physical-root-08/access-analysis.json) remain the measurement authority.
