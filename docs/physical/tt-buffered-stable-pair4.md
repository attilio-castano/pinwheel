# Frozen-RC buf_4 reassessment on the stabilized control

The virtual `fanout914`/`fanout913` `buf_1 → buf_4` pair clears all nine SLOW setup failures. It retains at least **490.266 ps of affected-path hold margin after a 1 ps numerical reserve** across the three declared corners. Whole-chip SLOW setup slack becomes **+39.076 ps**. Whole-chip FAST hold remains **19.573 ps**, so the stronger chip-wide 50 ps hold target remains unmet.

This is a timing-model assessment. The physical checkpoint still contains the original `buf_1` cells. RTL, serial ABI, placement, clocks, constraints and every route remain frozen; no physical sizing, placement or routing occurred.

## Controls and RC transfer

The study started at 23:57:38 UTC on October 13, 2026, with a hard deadline of 00:22:38 UTC on October 14. Native work stops before 00:18:38 UTC. The saved second stabilization pass supplies the ODB, netlist and global-route segments; the fresh native three-corner headroom reports supply the reference timing.

A new read-only RC capture reproduces the original nominal SPEF exactly. Its faithful derivative restores 90,759 native pin-node wire-capacitance attachments across 28,948 nets, including all 332 clock nets. Original CAP records, resistance, connections and all other SPEF bytes are preserved. Net totals agree within the explicitly qualified source serialization precision. Independent review verifies the additions directly against the native high-precision trace.

Three standalone OpenSTA controls run before the virtual pair. All 6,168 affected endpoint/context samples, global slacks and sampled clock waveforms reproduce the native reference within **0.006437 ps**, below the 1 ps gate. The control setup-failure endpoint sets are exactly 0/9/0 at Typical/SLOW/FAST; all three have zero hold failures.

The virtual netlist changes exactly the two named SIGNAL masters. Both buffer sizes have output function `A` in all three pinned standard-cell libraries. The identical faithful `PIN_CAP NONE` wire SPEF allows OpenSTA to propagate the new Liberty input capacitance, loading, slew and cell delay. There is no physical database in the sizing runs.

## Three-corner result

| Corner | Control setup WNS (ps) | Virtual setup WNS (ps) | Global hold (ps) | Affected hold after reserve (ps) | Setup failures before → after |
| --- | ---: | ---: | ---: | ---: | ---: |
| Typical | 5674.468 | 5674.468 | 107.727 | 843.195 | 0 → 0 |
| SLOW | -105.738 | 39.076 | 265.158 | 1443.848 | 9 → 0 |
| FAST (conditional) | 9068.194 | 9068.194 | 19.573 | 490.266 | 0 → 0 |

All three virtual corners have zero setup and zero hold failures. The nine formerly failing reset-to-SRAM address paths improve by 780.978–780.979 ps and retain 675.241–744.038 ps of setup slack. The new whole-chip SLOW limiter launches at `_30953_` and ends at `engine.memory.storage0/A_ADDR[2]`; its 39.076 ps headroom is distinct from the repaired reset-path margins.

On the representative SLOW reset path, `fanout914` cell delay falls from 539.722 to 319.255 ps and `fanout913` from 718.646 to 312.129 ps. Their output slews also improve. The increased upstream `_17772_` load, 6.212 to 7.714 fF, raises its cell delay from 228.456 to 247.088 ps; the full STA includes that loading cost and downstream slew effects.

Affected minimum hold ends at `_30575_/D` through `fanout914/fall` in each corner. The FAST raw minimum is 491.266 ps, leaving 490.266 ps after the reserve and 440.266 ps above the 50 ps floor. Whole-chip hold is unchanged in all three cases; its limiting path launches at `ena` and ends at `_30759_/D`.

The reported input-transition and total-output-capacitance samples for the two virtual `buf_4` cells are inside their Liberty table axes in every corner. This check does not expose internal DMP effective-capacitance lookup values or establish table coverage for every other cell and endpoint.

## Remaining qualification

Slew violations remain 2/7/2 at Typical/SLOW/FAST, and all 254 clock-fanout violation identities remain unchanged. There are no capacitance violations. Annotation remains 167 unannotated drivers and zero partial drivers. Shared sampled clock waveforms have zero control-to-virtual drift.

Congestion is unchanged because the routes and physical cells are frozen: native total overflow 5230, Metal3 2285, saved preferred-grid overflow 5210. The virtual result cannot establish buf_4 physical legality, pin access, or congestion after an actual resize.

The original stabilization routing process remains failed from its observed OOM after saving complete repeatable snapshots. Independently admitted completed artifacts are used here only for diagnostic STA; the failed receipt is preserved. The sandbox-denied first export attempt is also preserved, with a separate verified owner-absence receipt. The successful export and six-case STA containers are absent, and all 507 protected sources and bound input/artifact hashes remain current.

Estimated global-route RC remains distinct from extracted signoff. FAST retains the logic/IO −40 °C versus SRAM −55 °C mismatch. Physical sizing/routing qualification, the thin 39 ps SLOW setup margin, the chip-wide FAST 50 ps hold target, electrical violations and routing-process reliability remain open. No baseline promotion, commit, push or submission occurred.

The [machine-readable result](../../physical/experiments/tt-buffered-stable-pair4-results-01.json) binds the protocol, native export, corrected RC, all six STA cases, exact nine-endpoint comparison and independent control review. The root closeout records final independent review and elapsed time within the cap.
