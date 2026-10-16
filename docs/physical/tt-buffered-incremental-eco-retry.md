# Buffered SRAM incremental ECO retry

The timing helper was fixed and verified against pinned OpenROAD. The same two driver resizes and eight terminal D delays were applied from repaired R0. The live no-edit control, all 332 clock routes, unrelated routes, protected RTL and serial ABI passed preservation checks. The candidate remains **rejected** because incremental routing changed the capacity map.

Fresh candidate route-based STA has zero setup and hold violations in all three tested corners. Comparison uses the currently verified retained 10-iteration R0 timing; the separate fresh six-process numeric control failed during host staging before CAD and was not safely retried within the cap.

| Corner | R0 setup ns, retained | Candidate setup ns, fresh | R0 hold ns, retained | Candidate hold ns, fresh | Candidate setup/hold failures |
|---|---:|---:|---:|---:|---:|
| Typical | +5.674470 | +5.674470 | +0.001912 | +0.107727 | 0 / 0 |
| Slow | -0.375264 | +0.008953 | +0.102800 | +0.265159 | 0 / 0 |
| Fast, conditional | +9.068200 | +9.068200 | -0.054893 | +0.019575 | 0 / 0 |

The 20 original slow setup failures and eight original fast hold failures are absent. Slow setup margin is only 8.95 ps and fast hold margin 19.57 ps. Slew violations remain 2/7/2, fanout 254, and capacitance zero. The fast models use -40 C logic/IO and -55 C SRAM. These are global-route RC estimates, not extracted timing or signoff; the one-nanosecond slow research margin is not met.

The unchanged fresh route reproduced native total overflow 5226 and byte-identical retained segments. Its live no-edit control preserved full native inventory, all route segment multisets, the complete saved capacity/usage grid, nominal SPEF and timing. Independent host audit recomputed the exact two resizes/eight identity delays, legal declared footprints and all-corner cell functions. Fourteen signal nets appeared in the actual dirty worklist; all clock and unrelated route segments stayed exact.

Saved preferred-grid overflow worsened 5206 to 5210, entirely Metal3 +4. Metal2 capacity increased by 374 units in 154 bins: 77 bins at each SRAM south pin-access row. Metal3 and Metal4 capacity stayed exact. The failed resource gate prevents treating this as an accepted congestion comparison. The candidate's nominal native overflow table is stale, copied from the baseline's last printed table; it is intentionally excluded.

Source inspection supports repeated macro pin-access credits: dirty incremental initialization calls initNetlist, which adds pin-access resources across the macro net map again. The empty no-edit control skips that path. The GRT-0704 message suggests reducing adjustment; it does not apply the suggestion. See the [pinned implementation](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/grt/src/GlobalRouter.cpp#L1788). The wrapper's configured iteration field resets to 50 on omitted arguments, while this warm route path retains the initialized FastRoute core's 10-iteration budget; it does not reinitialize the core.

The failed physical producer and its capacity guard remain intact. Fresh PSM, whole-placement checking and a new mapped upload-to-pins run were not performed after the failure. The control staging failure launched no container; the candidate diagnostic container completed and was removed. Original failed-flow power provenance, detailed routing, extraction and DRC/LVS remain open. No candidate, commit, PR or submission was promoted.

The next bounded step is to make macro pin-access capacity credits idempotent, test a dirty no-edit control, and repeat the identical ECO while enforcing the same resource and route preservation gates. Restore resource consistency before routing rather than rewriting saved capacities afterward.

Evidence: [results](../../physical/experiments/tt-buffered-incremental-eco-results-02.json), [rejection audit](../../build/physical/tt-buffered-incremental-eco-review-02/rejected-candidate-audit.json), [diagnostic timing](../../build/physical/tt-buffered-incremental-eco-candidate-timing-03/report.json), and [timing summary](../../build/physical/tt-buffered-incremental-eco-root-02/timing-summary.json). The final root closeout records the full 25-minute deadline, including cleanup and publication.
