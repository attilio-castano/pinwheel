# Buffered SRAM incremental ECO attempt

The 2026-10-13 bounded attempt stopped during baseline timing-report capture, before the no-edit incremental control or ECO. No candidate was created. The core RTL, serial ABI and repaired R0 source checkpoint were preserved.

The intended treatment was identical to the preceding study: resize `fanout1946` and `_18965_`, then add the same eight terminal D delay cells. Only routing was to change: one live OpenROAD process, a strict no-edit gate, and incremental work limited to 14 original signal nets plus eight new nets. Every clock and unrelated route was required to remain exact. No fallback full reroute was allowed.

The fresh 10-iteration R0 route reproduced the retained baseline:

| Measurement | Retained R0 | Fresh route |
|---|---:|---:|
| Native total overflow | 5,226 | 5,226 |
| Metal2 overflow | 1,175 | 1,175 |
| Metal3 overflow | 2,281 | 2,281 |
| Metal4 overflow | 1,770 | 1,770 |
| Preferred-grid overflow | 5,206 | 5,206 |
| Wirelength, micrometers | 2,527,207 | 2,527,207 |
| Routed nets | 28,940 | 28,940 |

Raw route segments were byte-exact to the retained 10-iteration baseline (`1cd575c7...f81f05`), including the six clock NDR fallback events in the same order. Native overflow and the saved preferred-grid overflow are different measures.

The helper successfully wrote baseline ODB, DEF, netlist, segments, guide, geometry and estimated SPEF. It then invoked Tcl `redirect`, which is unavailable in the pinned OpenROAD Python command namespace. Strict error handling stopped the native process with exit 2; its container wrapper returned exit 1. Baseline numeric timing was not collected. The no-edit gate, ECO, incremental preservation checks, fresh three-corner STA and finite mapped check were not run. Historical timing measurements are not substituted for them.

The root route phase took 122.197 seconds including preparation and cleanup, used an offline container with four CPUs and 3 GiB, and stopped before the native deadline. The owned container was absent in both the execution receipt and a fresh root query. The full experiment, including helper preparation and closeout, is limited to 25 minutes from 16:46:55 UTC to 17:11:55 UTC.

A subsequent attempt should replace `redirect -file PATH {report_checks ...}` with `report_checks ... > PATH` in a new immutable helper version, keeping the same report options. The repository already uses this syntax in `scripts/check-targeted-timing.py`. Verify the report-command API before CAD, then repeat the same live-process control and identical ECO. This failed attempt must remain preserved. No incremental timing or congestion improvement is established, and no candidate is promoted. The prior full-reroute ECO remains rejected. Detailed routing, extraction, DRC/LVS and the original failed-flow power provenance remain unresolved.

Evidence: [selection](../../physical/experiments/tt-buffered-incremental-eco-selection.json), [results](../../physical/experiments/tt-buffered-incremental-eco-results.json), and [root route report](../../build/physical/tt-buffered-incremental-eco-route-01/report.json).
