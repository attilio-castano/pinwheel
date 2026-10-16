# Physical fanout914/913 buf_4 trial: stopped at no-edit control

The bounded trial stopped before either buffer was resized. The saved candidate was reproduced, but the matched three-net dirty no-edit reroute changed two permitted signal routes and their RC. The predeclared exact control gate therefore failed. This is a failed control, not a measured buf_4 regression.

## What ran and passed

The warm reconstruction produced the saved candidate's exact routed ODB SHA, `8c3079c61f73f0f2819d4e0d21d0af2775d4afb76c620494e2841ace4b1dd063`, and exact saved routes, inventories, nominal RC/timing, grid resources and NDR fallback order. It then exercised the planned dirty set `_11039_`, `net914`, `net913` without changing any cell.

All 507 protected sources and six saved physical fingerprints remain unchanged. The dirty control preserves every master, placement, orientation, signal connection and power-pin assignment. Raw capacities, all 332 CLOCK routes and every unrelated route multiset remain exact. The owned container is absent. No BUF4 master replacement, candidate checkpoint, physical candidate timing, commit, promotion or submission occurred.

The route phase ended with exit 1 at its strict no-edit assertion after 313.560 seconds including phase staging, native execution, cleanup and source recustody. The study window began at 21:06:35 UTC on 2026-10-13 and retains its 21:31:35 UTC hard deadline. Final analysis and publication are included in the root closeout.

## Control drift

| Metric | Saved control | Dirty no-edit control | Change |
| --- | ---: | ---: | ---: |
| Native total overflow | 5227 | 5230 | +3 |
| Metal3 overflow | 2282 | 2285 | +3 |
| Saved preferred-grid overflow | 5207 | 5210 | +3 |
| Native total demand | 254579 | 254607 | +28 |
| net913 segment count | 54 | 86 | +32 |
| net914 segment count | 64 | 87 | +23 |

`_11039_` is unchanged. Only `net913` and `net914` acquire new route geometry. Their combined added wire is 201.6 µm: 122.4 µm on Metal2 and 79.2 µm on Metal4. Metal3 wire length/demand is unchanged in aggregate, but its distribution shifts and overflow rises by three.

Independent review finds that all 96 changed saved preferred-grid usage bins exactly equal the segment-edge contributions of these two nets, with no unexplained bins. The layer sums agree with native demand: Metal2 +17, Metal3 zero, Metal4 +11. Capacities are identical. These observations support legitimate non-idempotent local rerouting rather than another demonstrated pin-credit or resource-accounting defect. They do not prove every hidden internal router usage field.

## Timing consequence

The nominal global worst setup and hold remain 5.674468167 ns and 0.107726831 ns. The retained 1000-path MIN report is byte-identical. However, the SPEF and MAX report change, so unchanged global WNS does not establish control identity or affected-path invariance.

The reroute adds 14.6456 fF of wire capacitance to net913 and 4.0096 fF to net914. Pin connectivity and real-pin-to-grid resistance are unchanged. On the matched `rst_n → _31078_/D` path, setup slack falls by 71.987 ps: 57.468 ps of added cell delay and 14.519 ps of added wire delay, while capture/required time stays fixed. fanout913's observed load rises from 99.295 to 113.941 fF and slew from 408.272 to 467.905 ps. This is real signal-RC drift, not clock skew or harmless ODB serialization.

Fresh three-corner control and candidate STA were not launched because the physical no-edit admission gate failed. The earlier virtual pair's 481.105 ps conservative hold margin remains valid for that fixed-wire model; it is not a result for this unperformed physical resize.

## Next bounded experiment

Run a routing-only two-pass dirty no-edit study from the saved candidate, changing no cells and dirtying only these three signal nets. Record the first flow-only route, RC, timing and congestion shift; test whether a second identical pass stabilizes. Preserve all clock/unrelated routes, capacities and source evidence. Measure three-corner timing for the resulting control states within the selected cap. Stop if the second pass remains non-idempotent.

Only after establishing a stable matched control should the physical sizing trial be retried against an explicitly selected comparison baseline. The failed exact-control expectation must not be silently relaxed to manufacture an accepted BUF4 result. Detailed routing, DRC/LVS, fast-corner library qualification and stronger whole-chip timing/electrical goals remain separate gates.

The [machine-readable result](../../physical/experiments/tt-buffered-fanout913914-physical-results-01.json) binds the failed producer, immutable preparation, independent review, source-state proofs and prior virtual assessment.
