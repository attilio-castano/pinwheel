# Conditional fanout914/913 sizing preflight

Fresh three-corner STA completed on the saved timing_eco_hold_30712 candidate. The proposed fanout914/913 buf_1 to buf_4 sizing was **not admitted**, and no physical candidate was created. The mandatory conservative hold guard failed in the typical and fast corners; the physical producer launch window also closed before an admissible gate existed.

The buffers are in series. The experiment therefore required separate paths through each driver, for rising and falling data, with both setup and hold reports. Native structural and timing fanout each contained 257 endpoints per driver. Every one of the eight report groups per corner covered those 257 endpoints, for 2,056 path records per corner and 6,168 across three corners. Full report/ledger equality and serial-path checks are recorded in the separately bound diagnostic evidence.

All values below are slack in ns. Global values exactly reproduce the previous qualified fresh STA. The per-driver columns are minimum hold slack across both data transitions.

| Corner | Global setup | Global hold | Hold through914 | Hold through913 |
|---|---:|---:|---:|---:|
| Typical | 5.674470 | 0.107727 | 1.046728 | 1.252629 |
| Slow | 0.00895284 | 0.265159 | 1.803394 | 2.164565 |
| Fast | 9.068200 | 0.0195748 | 0.616891 | 0.741636 |

There are zero setup or hold failures in the frozen baseline at all three corners. Slow setup remains only 8.95284 ps above zero on rst_n to engine.memory.storage0/A_ADDR[2], through both buffers. Global fast hold remains only 19.5748 ps above zero on a different path; it is not the local sizing reserve.

The preregistered sizing guard required at least 1.05 ns of current through-path hold slack: a conservative 1.0 ns combined speedup/loading allowance plus 50 ps residual slack. Typical fanout914 misses this by 3.272 ps. Fast fanout914 has only 0.616891 ns on _30889_/Q to _30575_/D with falling data; fast fanout913 has only 0.741636 ns on _30889_/Q to _30591_/D with falling data. The source register is engine.controller.r_cached_branch[19]; the endpoints store r_current_control[5] and r_current_control[21], respectively. These are internal register paths, so checking only paths starting at the reset port would miss the limiting hold reserve. Both fast paths fail the guard. This rejects the experiment under its conservative admission policy; it does not establish that an actual physical resize would necessarily fail.

NLDM replacement-delay, downstream slew, endpoint hold-check and wire/loading estimates were not completed after the mandatory numerical hold guard failed. No library-only sizing benefit or physical timing gain is claimed. The initial helper revisions were preserved; the final native collector deliberately separated collection from admission so a later host analysis issue could not suppress one of the three corners.

RTL, serial ABI, placement, cell masters, clocks and all routes remain unchanged. Both buffers remain buf_1 at their original locations. Native imported routes, NDR assignments, logical netlist and normalized full SPEF were preserved, and prior annotation/electrical tables reproduced. Existing slew counts remain 2/7/2 for typical/slow/fast; max-fanout count remains 254 per corner and max-capacitance count zero.

Congestion is the unchanged saved baseline: native total overflow 5,227, Metal3 overflow 2,282; saved preferred-grid overflow is a separate metric at 5,207. No new routing run was performed. The matched three-net dirty no-edit control, sizing, incremental routing and post-resize STA remain unrun, so no candidate timing or congestion comparison exists.

The next bounded step is a preflight-only, path-specific hold-loss assessment of these limiting register paths, including downstream slew and endpoint hold-check changes. SRAM bus-pin models must be handled explicitly before a complete library bound is claimed. Only a bound that leaves at least 50 ps of residual local hold should admit a subsequent physical trial; the fixed guard is not waived in this record.

This is STA with estimated global-route RC, not extracted signoff. Fast logic/IO uses minus40 C while SRAM uses minus55 C. There are 167 unannotated drivers per corner, so complete annotation is not claimed. The fixed 25-minute budget starts at 2026-10-13 19:29:58 UTC and ends at 19:54:58 UTC; the native producer window required a full 360 seconds before the fixed 19:50:58 UTC native stop. CAD ownership absence, current source custody and the final publication timestamp are recorded in the linked machine-readable results and closeout.

Evidence: [results](../../physical/experiments/tt-buffered-fanout913914-results-01.json), [selection](../../physical/experiments/tt-buffered-fanout913914-selection-01.json), [native preflight](../../build/physical/tt-buffered-holdreset-pair-preflight-01/report.json), [headroom admission](../../build/physical/tt-buffered-holdreset-pair-preflight-01/gate.json), [independent coverage](../../build/physical/tt-buffered-fanout913914-coverage-review-01/report.json), and [independent final review](../../build/physical/tt-buffered-holdreset-pair-review-01/final-review.json), and [full closeout](../../build/physical/tt-buffered-fanout913914-root-01/final-closeout.json).
