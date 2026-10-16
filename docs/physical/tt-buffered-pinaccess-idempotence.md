# SRAM pin-access idempotence and incremental ECO

The capacity-credit workaround and genuine dirty no-edit control passed. The same ECO completed with all 332 clock routes, unrelated routes, RTL and serial ABI unchanged. Fresh matched timing and the full mapped upload-to-pins check passed. The experiment is complete within the 25-minute cap; physical signoff and stronger research margins remain open.

The correction is a guarded runtime workaround in the pinned process. The original baseline applies the access credits. Later incremental calls suppress repeated credits only while the macro/pad pin-grid fingerprint stays fixed. The dirty control invalidates one routing cache entry without a physical database edit, and must exercise actual incremental netlist initialization.

The same two driver resizes and eight terminal D delays are preserved. All source, route, capacity, clock, function, placement, power and timing claims are scoped by the linked receipts.

The unmodified original R0 baseline reproduced native overflow 5226 and byte-identical retained route segments. The dirty control actually rerouted singleton signal _03283_ through native incremental netlist initialization while preserving full inventory, all canonical routes, saved capacity/usage, resident FastRoute capacities, SPEF and nominal timing exactly. Baseline, dirty control and candidate raw capacity files are byte-identical (fec3cd2b1c51527187b47ffc25d1f8bf0cec0a93b6e0bff257f654aeae71b053).

The same two driver resizes and eight terminal D delays passed exact whole-inventory, legal placement, all-corner cell-function and both power-grid checks. Fourteen actual signal nets were rerouted; all 332 clock routes and every unrelated route stayed exact. Original function bytes and RX page protection were restored after the run. No capacity or saved-grid values were rewritten.

Fresh six-process baseline/dirty-control timing matched exactly in every corner, including numeric metrics and SPEF. Candidate three-corner estimated route RC has zero setup and hold violations.

| Corner | Baseline setup ns | ECO setup ns | Baseline hold ns | ECO hold ns | ECO setup/hold failures |
|---|---:|---:|---:|---:|---:|
| Typical | +5.674470 | +5.674470 | +0.001912 | +0.107727 | 0 / 0 |
| Slow | -0.375264 | +0.008953 | +0.102800 | +0.265159 | 0 / 0 |
| Fast, conditional | +9.068200 | +9.068200 | -0.054893 | +0.019575 | 0 / 0 |

The original 20 slow setup failures and eight fast hold failures are absent. Slow setup headroom is 8.95 ps and fast hold headroom 19.57 ps. The stronger one-nanosecond slow setup and 50-picosecond hold goals remain unmet. Slew violations are still 2/7/2, fanout 254, capacitance zero. The fast condition combines -40 C logic/IO with -55 C SRAM; global-route RC estimates do not establish extracted timing or signoff.

Fresh native overflow increased 5226 to 5230, entirely Metal3 2281 to 2285; Metal2 1175 and Metal4 1770 are unchanged. Native resources remain 397280. Saved preferred-grid overflow increased 5206 to 5210 and is a separate measure. Zero-capacity native overflow remains 3265; all four additional units occur on positive-capacity resources. The fix eliminated capacity drift, and this ECO did not improve congestion.

The full unchanged canonical mapped upload-to-pins check passed 21 cases (9 SPI, 3 JTAG, 9 I2C), 400 requests/responses and three parser negative controls. Both owned host process groups stopped. This is finite zero-delay functional validation, not exhaustive sequential equivalence or routed timing.

Independent final custody checked 3354 current source/artifact bindings and all 507 protected sources. Six exact owned container labels were freshly queried absent. Producer/control/candidate all-in times were 172.088/149.460/89.756 seconds; the host mapped phase took 134.351 seconds. Physical timing containers overlapped at 3 CPUs/3 GiB each, at most 6 CPUs/6 GiB combined, with a separate host functional process; the route itself used 4 CPUs/3 GiB.

The runtime correction is scoped to the exact pinned binary and frozen macro/pad pin-grid configuration. The first baseline applied the original credits; later calls skipped only the repeated credit function. A validated AArch64 function-entry guard and instruction-cache flush were used, with exact module/prologue checks. This is a reversible per-process workaround, not a rebuilt or upstream OpenROAD fix.

Remaining submission gates include detailed routing, extraction, DRC/LVS and unresolved provenance from the original failed native flow (exit 2, inherited power count 30396). The successful bounded experiment does not relabel that old failure. No candidate, commit, PR or competition submission was promoted.

Evidence: [sealed results](../../physical/experiments/tt-buffered-incremental-eco-results-03.json). The final closeout binds publication, ownership and the complete wall-clock bound.
