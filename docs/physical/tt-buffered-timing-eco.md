# Buffered Tiny Tapeout two-driver and terminal-hold ECO

Retain repaired R0 as the reference. The single fixed ECO improves slow setup and clears the eight targeted hold failures, but fails timing and Metal3 congestion gates. Core RTL, serial ABI, clock topology, SRAM/PG/pin geometry and constraints remain unchanged.

Setup headroom was checked first: all eight hold endpoints across all three corners had at least **14.530972 ns** of setup margin. The candidate contains exactly two driver resizes and eight single-sink noninverting delay stages; no neighboring cell moved. Native placement, whole-inventory/function identity, both power-grid checks and finite mapped upload-to-pins validation passed.

| Measure | Fresh R0 control | Candidate |
| --- | ---: | ---: |
| Total native overflow | 5226 | 5209 |
| Metal2 overflow | 1175 | 1214 |
| Metal3 overflow | 2281 | 2306 |
| Metal4 overflow | 1770 | 1689 |
| Zero-capacity overflow | 3265 | 3261 |
| Wirelength (um) | 2527207 | 2539015 |

| Corner | Control setup (ns) | Candidate setup (ns) | Control hold (ns) | Candidate hold (ns) | Setup failures | Hold failures |
| --- | ---: | ---: | ---: | ---: | --- | --- |
| nom_typ_1p20V_25C | 5.674470 | 5.650950 | 0.001912 | 0.028792 | 0 -> 0 | 0 -> 0 |
| nom_slow_1p08V_125C | -0.375264 | -0.241336 | 0.102800 | 0.182015 | 20 -> 12 | 0 -> 0 |
| nom_fast_1p32V_m40C | 9.068200 | 9.033990 | -0.054893 | -0.058031 | 0 -> 0 | 8 -> 10 |

The remaining 12 slow failures all terminate at SRAM address pins. The eight repaired fast-hold endpoints pass, but ten other external-input endpoints now fail. For the new worst endpoint `_30759_/D`, data arrival changes only 0.622 ps while capture-clock arrival increases 78.267 ps. CTS cells/topology are frozen; their routed parasitics change. Native automatic NDR fallback changes from six to eight retries, so this is the combined ECO with the native routing response, not an isolated attribution to one driver.

Full finite mapped validation passed: 21 independent SPI/JTAG/I2C peers, 400 requests/responses, 336,426 interface/wire edges and three negative controls. This uses zero-delay vendor functional models; it is separate from route-based timing.

The initial edit crashed before creating a candidate because Liberty was not loaded for the resize callback. Its evidence is preserved; the successful retry used the identical physical plan with initialization corrected. A sandbox-blocked headroom launch also created no native measurement and is preserved.

These are global-route estimates, not extracted timing or signoff. Fast remains conditional (-40C logic/IO, -55C SRAM). Nonzero congestion, the slow +1ns research target, detailed routing, DRC/LVS and official precheck remain open. The original LibreLane producer remains failed, exit2, with inherited power counter30,396; fresh PSM checks do not relabel that provenance.

Publication elapsed: 1469.954 seconds of 1,500; native phases and owned cleanup completed before the deadline.

Evidence: [result manifest](../../physical/experiments/tt-buffered-timing-eco-results.json), [fixed selection](../../physical/experiments/tt-buffered-timing-eco-selection-02.json), [edit proof](../../build/physical/tt-buffered-timing-eco-edit-02/change-proof.json), [headroom gate](../../build/physical/tt-buffered-timing-eco-headroom-02/headroom-gate.json), [candidate timing](../../build/physical/tt-buffered-timing-eco-candidate-timing-01/report.json), [mapped validation](../../build/tt-buffered/netlist/tt-buffered-timing-eco-01/report.json).
