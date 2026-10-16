# Three-corner validation of repaired RC and virtual buf_4 sizing

The repaired per-pin RC export passes all three no-edit transfer controls within 1 ps. The virtual fanout914/fanout913 buf_4 pair also passes the 50 ps affected-path hold gate with a full 1 ps reserve. Its worst raw affected hold slack is 482.105 ps; the conservative result is 481.105 ps. These are fixed-wire STA results. The physical design remains unchanged, including the two original buf_1 instances.

The run reused immutable prepared helper 06 and the repaired export, under a fresh 25-minute window starting at 20:53:30 UTC on 2026-10-13. Six STA processes completed successfully in 333.142 seconds including phase staging, execution, cleanup and source recustody. The native execution limit remained 420 seconds. Independent review and final publication are included in the root closeout time.

## Control transfer

The maximum discrepancy is 0.006436 ps, below the 1 ps limit. Each corner checks global worst setup and hold, all 8 × 257 affected endpoint/context slacks, and the sampled source clock waveforms. Parasitic coverage remains 167 unannotated drivers with zero partial drivers. The full control and virtual endpoint ledgers cover 12,336 path contexts in total.

| Corner | Maximum no-edit discrepancy (ps) |
| --- | ---: |
| Typical | 0.004000 |
| Slow | 0.006000 |
| Fast (conditional) | 0.006436 |

All three no-edit controls passed before any virtual candidate was admitted. Only the two timing-netlist master names changed from buf_1 to buf_4. The same corrected SPEF, clock constraints and routes were used. Native Liberty input-capacitance updates were checked at the affected parent and output drivers. The three control/virtual clock reports are byte-identical, with zero shared clock-waveform drift.

## Timing comparison

| Corner | Control affected hold (ps) | buf_4 affected hold (ps) | After 1 ps reserve (ps) | Global setup: control → buf_4 (ps) |
| --- | ---: | ---: | ---: | ---: |
| Typical | 1046.729 | 835.983 | 834.983 | 5674.468 → 5674.468 |
| Slow | 1803.391 | 1435.789 | 1434.789 | 8.953 → 39.076 |
| Fast (conditional) | 616.890 | 482.105 | 481.105 | 9068.194 → 9068.194 |

The affected hold limiter at every corner is fanout914/fall/min to _30575_/D. At the fast corner, the fanout913 chain retains 494.061 ps before reserve. The pair-affected slow setup minimum improves from 8.953 to 705.635 ps. The global gain is smaller because _30953_/Q to SRAM0/A_ADDR[2] becomes the limiting setup path at 39.076 ps.

Whole-chip hold is unchanged: typical 107.727 ps, slow 265.158 ps and fast 19.573 ps. The passed 50 ps criterion applies to paths affected by this virtual pair; it does not establish a whole-chip 50 ps floor.

## Electrical behavior and remaining gates

The violation identities and counts remain unchanged: 2/7/2 slew violations at typical/slow/fast, 254 clock fanout violations at every corner, and zero capacitance violations. Slow output rise slew improves from 569.382 to 174.091 ps at fanout914 and from 620.043 to 170.681 ps at fanout913. Their parent _17772_/Y rise slew increases from 227.318 to 253.111 ps because the larger buffers add input capacitance. The selected outputs were already within their slew limits, so these improvements do not remove the existing violations.

The seven slow slew violations are SRAM DIN[8] on both banks, SRAM0 DIN[22], _17330_/C, _17329_/Y and WEN on both banks. Their reported rows are unchanged. Buffer sizing therefore does not close the remaining electrical checks.

A focused current-library audit checks the two limiting fast register chains, including their endpoint hold constraints. It does not establish that every path is within every characterization table. The fast run retains its existing mixed-temperature library qualification. All measurements use estimated global-route wire RC, rather than extracted signoff parasitics.

The next physical qualification would need authorization for actual master replacement, footprint legality and pin access, followed by routing and STA. It must protect the 39 ps global slow setup headroom, address the existing fast whole-chip hold margin and remaining slew/fanout violations, and retain the RTL/ABI contract. No physical sizing, placement change, clock edit, route edit, candidate promotion, commit or submission occurred in this assessment.

The [machine-readable result](../../physical/experiments/tt-buffered-fanout913914-rc-validation-results-01.json) binds the selected inputs, native run, independent reviews and current source hashes. Earlier export-repair and lossy-import evidence remain unchanged.
