# Five-terminal hold trial

The bounded trial stopped at its dirty no-edit control before adding any buffer. The saved BUF4 candidate remains unchanged.

Fresh source STA controls reproduced all three corners within 1 ps, including the five terminal endpoints and 6,168 affected contexts. The smallest selected-endpoint setup headroom was 12.524107 ns; the conservative, conditional cost assessment left at least 10.258513 ns after a 1 ps reserve. The source still has 39.0763 ps global setup margin at SLOW and 19.5748 ps global hold margin at FAST (18.5748 ps after the reserve). Its reserved 50 ps hold target remains unmet.

| Gate | Result |
|---|---|
| Fresh three-corner source controls and endpoint headroom | Passed |
| Exact saved BUF4 reproduction in the warm router | Passed |
| Five-old-net dirty no-edit control | Failed |
| Terminal BUF1 additions | Not admitted; zero added |
| New physical candidate / candidate STA / 50 ps reserved hold | Not produced or verified |
| 507 protected sources, inventory, placement, clock and unrelated routes/RC | Unchanged |
| Owned CAD container cleanup and runtime guard restoration | Passed |

The no-edit operation re-enrolled `_00006_`, `_03109_`, `net8042`, `net8046` and `net9291`. Only `net8046` changed its canonical route and native RC network. Its route grew from six to eleven segments and its estimated wire capacitance increased from 2.05444 to 11.2978 fF. Total native overflow decreased from 5,230 to 5,229 and Metal3 from 2,285 to 2,284. These are control drift, not a measured buffer benefit. Global typical setup and hold stayed numerically unchanged, which does not satisfy the stricter route/RC equality gate.

All 332 clock routes and RC networks, all unrelated routes and RC networks, raw capacities, placements, masters and logical netlist stayed exact. The failure occurred before `PINWHEEL_TERMINAL_EDIT_BEGIN`; no terminal candidate exists. Final timing helpers were prepared but not executed.

The next bounded experiment should exercise this five-old-net dirty worklist twice from the saved BUF4 source. Require consecutive exact routes, native RC and capacities, plus fresh three-corner controls within 1 ps, before admitting a hold-buffer treatment. Do not assume the earlier three-net stabilization also stabilizes this different worklist.

Source-domain checks also found seven inherited old-driver input-slew excursions below the 18.6 ps characterization axis. New BUF1 output/flip-flop slew checks remain unmeasured. Numeric source STA is retained separately from full table-domain qualification. All RC here is estimated global-route RC, and the FAST logic/SRAM model remains conditional.

See [results](../../physical/experiments/tt-buffered-five-terminal-hold-results-01.json), [headroom](../../build/physical/tt-five-terminal-headroom-01/report.json), [physical attempt](../../build/physical/tt-five-terminal-physical-route-02/report.json), and [route/RC audit](../../build/physical/tt-five-terminal-postroute-tools-01/dirty-noedit-RC-audit.json). The result receipt records the total elapsed time and immutable source hashes.
