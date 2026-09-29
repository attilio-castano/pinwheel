# SRAM distribution and write timing — September 25–26

The subsequent [control-distribution experiment](control-distribution-experiment.md)
retains this complete-route design after two further variants fail qualification.
The measurements below remain the original SRAM experiment's result;
[research status](../research/status.md) owns current priorities.

**Retain the 34-buffer candidate as an improved physical starting point.** Its
complete coarse route improves worst slow setup from **−0.113646 to +0.321638 ns**
and worst fast hold from **+0.049847 to +0.089025 ns**. All slew and fanout
violations are removed. Qualification remains open: one different control branch
now violates capacitance, two connections miss the experimental reserve, and
setup misses the retained comparison margin.

This follows [regional decoding](regional-decoding-experiment.md). The
[result manifest](../../physical/experiments/sram-distribution-results.json)
binds `build/validation/sram-distribution-01/report-02.json`, the exact plans,
readbacks, raw measurements, unsuccessful checks and pinned tools. The
[research status](../research/status.md) owns the next decision.

## Mechanism and variants

The SRAM read path had small gates driving long wires and shared decode loads.
One wire spanned approximately 775 µm between its endpoint cells. A buffer near
the source lets the small gate drive a short, light connection while the buffer
drives the long wire. This costs area and another gate delay; the net effect must
be measured.

Write timing has a second requirement: data must remain stable briefly after the
SRAM clock edge. Faster transport alone can reduce this hold margin. Receiver
buffers can improve electrical transitions and delay new data, but the SRAM's
hold requirement also depends on the arriving transition. The first variant's
single added stage did not provide enough margin for every affected bit.

- **20-buffer variant:** isolate two read-side drivers and four weak distribution
  branches; add receiver buffers for write bits 35, 36–47 and 53. Added area is
  **248.5728 µm²**. It clears the electrical collection, but misses both retained
  timing floors.
- **34-buffer variant:** retain those edits, add a second stage for write bits
  36–47, and buffer two gates on the newly limiting bit-53 read path. Total added
  area is **364.6944 µm²**. Local timing clears both floors and every measured
  connection has the 20% electrical reserve.

Every original cell and placement is retained, including clock and hold-delay
cells. The edits add no state, cycles or RTL changes. Both stages are checked
against their actual predecessor ODB and independently reread Verilog. Buffer
contraction preserves the original signal graph under the pinned cell meanings;
power connections, macro pin bindings and fixed geometry are checked separately.

## Measurements

The unchanged control is a separate complete reroute with the same pinned flow.
It reproduces **all** baseline connection and selected/interface path measurements,
and the complete stored routing grid. Local incremental grids are partial and
are not used to claim whole-chip congestion results.

| Measurement | Saved baseline | 20 buffers, local | 34 buffers, local | Unchanged reroute | 34 buffers, complete reroute |
| --- | ---: | ---: | ---: | ---: | ---: |
| Placed cell/macro area, µm² | 359,411.5872 | 359,660.1600 | 359,776.2816 | 359,411.5872 | 359,776.2816 |
| Worst slow setup, ns | −0.113646 | +0.314767 | +0.406100 | −0.113646 | **+0.321638** |
| Worst fast hold, ns | +0.049847 | +0.065236 | +0.098877 | +0.049847 | **+0.089025** |
| Global capacitance violations, each corner | 1 | 0 | 0 | 1 | 1 |
| Global slow / fast slew violations | 9 / 1 | 0 / 0 | 0 / 0 | 9 / 1 | **0 / 0** |
| Global fanout violations | 0 | 0 | 0 | 0 | 0 |
| Connections meeting 20% reserve | 1,212 / 1,218 | 1,238 / 1,238 | 1,252 / 1,252 | 1,212 / 1,218 | 1,249 / 1,252 |
| Router-reported complete overflow | 19 | — | — | 19 | **16** |
| Stored-grid overflow | 19 | — | — | 19 | **15** |

The extra router-reported unit is on Metal4: its final table reports 15 on Metal3
and one on Metal4, while the saved grid exposes 15 on Metal3 and none on Metal4.
Two read-only probes inspected the pinned OpenDB API; its native congestion
matrix views are opaque to the Python interface used here. **The Metal4 difference
is unresolved**, not discarded. Both measurements improve relative to the control,
but they are not interchangeable or evidence of congestion-free routing.

All 72 comparisons of the local variants' matched launch/capture clock paths are
exactly unchanged. Full rerouting changes other wires and clock arrival too; its
effect must be assessed as a complete candidate. The original matched bit-51 path
improves much more than the global worst path, because other paths become limiting.
The final unrestricted bit-51-to-status setup is **+0.704093 ns**.

The original area reference is **358,297.5456 µm²** and the historical +0.3%
allowance is **359,372.438237 µm²**. The new buffers add **0.101785%** of that
reference. Final area is **0.412712%** above it and **403.843363 µm²** above the
historical allowance. The die outline is unchanged. This is a recorded overage
under the [exploration policy](../research/README.md#exploration-with-temporary-size-overages);
no buffer-removal credit or completed area recovery is claimed.

## Complete coverage and remaining failures

The collection includes the inherited **1,152-connection** watchlist, additional
read-path connections, and every added branch. Two distinct bit-51 trees are
covered completely: the captured upload-word tree has **434 logic leaves**;
the decoded read-bit tree has **81**. Their shared bit index does not make them
the same signal. All leaves survive the edits and all final branches are measured.

The five comparisons contain **18,534 independent net/corner load reconciliations**,
**360 selected path witnesses** and **1,920 write-interface witnesses**. Every
write-data bit is checked in both timing directions at all three corners. Both
SRAM output fanout limits absent from the reports remain explicitly unknown;
capacitance, slew and actual load counts are still checked.

The final worst setup path starts at `memory.storage/A_DOUT[53]` and ends at
`uo_out[4]`. Its positive slack meets the saved 20 ns timing constraint, but is
**45.705 ps below** the retained **+0.367343 ns** comparison floor. The fast hold
floor of **+0.079278 ns** passes. Every SRAM write-data input now has at least
**+0.161179 ns** hold slack; the global hold limit moves to
`r_serial_sck_prev → r_serial_shift[28]`.

| Newly weak routed connection | Driver | Worst capacitance before → after, pF | Result |
| --- | --- | ---: | --- |
| `_04754_` | `_09664_/X` | 0.184852 → 0.346915 | Exceeds the 0.300000 pF limit; feeds selection for `r_parameter_b1_w23` |
| `_02966_` | `_06781_/X` | 0.186077 → 0.240327 | 19.891% reserve; distributes upload-word bit 53 |
| `_05207_` | `_10405_/X` | 0.188306 → 0.249863 | 16.712% reserve; serial-shift control |

Their terminal loads remain fixed. These regressions appear only after complete
rerouting, demonstrating why local improvements need whole-chip checks. The next
experiment should address these complete control families and the fresh bit-53
critical path together, retaining the successful write-input environment.

The minimum-one-access-point probe passes: **33,678 standard-cell pins** are
examined, with zero standard-cell or macro no-access counts and zero off-grid
warnings. This does not prove simultaneous routability or detailed-route closure.

## Reproduction and evidence boundary

Twelve CAD containers take **429.640 seconds**, including the two grid-reader
probes; the preceding regional experiment's **169.993 seconds** remain separate
and recorded. The new bounds are 1,500 cumulative container seconds, two local
variants, two complete coarse routes, 180 seconds per timing collection and
300 seconds per coarse route, with two CPUs and 2 GiB. No timeout or detailed
route occurs, and every container is confirmed absent.

The broader measurement set exposed ignored per-bit SRAM address capacitance
overrides and absent macro fanout limits. The readers now preserve these meanings
and reject malformed report sections. Reanalysis with the final readers reproduces
the earlier comparisons. The unsuccessful initial analyses, premature verification
startup and router/grid consistency check remain recorded.

Final review also corrected a bus-pin cache key overwritten by an inherited
attribute name. The cache regression fails before the fix; the corrected reader
reproduces all five saved comparisons exactly. The original sealed report and
manifest are retained, with this verification appended in `report-02.json`.

```sh
python3 -B -m unittest discover -s test -p 'test_physical_signal_buffering.py' -v
python3 -B -m unittest discover -s test -p 'test_physical_connections.py' -v
python3 -B -m unittest discover -s test -p 'test_physical_organization.py' -v
python3 -B -m unittest discover -s test -p 'test_*.py'
```

The complete portable suite records **471 passed / 2 skipped**. The manifest
binds run-local preparation, both plans, workers, analyses and sealing code.
Replaying CAD requires the ignored artifacts, original checkpoint and pinned
local CAD/PDK installation; the tracked manifest alone cannot recreate them.
Use fresh output tags and retain unsuccessful attempts.

Timing remains estimated from global routes; the historical fast-corner
standard-cell −40°C / SRAM −55°C mismatch remains explicit. No backend promotion,
new Lean theorem, complete paired compiler/package refinement, extracted timing,
antenna, power-grid or final layout qualification follows. The experiment uses
the existing Lean-generated circuit. Its formalization lesson is concrete:
transparent signal distribution preserves logical behavior, while physical
planning must satisfy both minimum and maximum delay contracts.

The [committed connection replay command](connection-replay.md) now supports
rechecking these raw reports against their saved measurements. It derives
per-corner absent fanout bounds from the physical driver, pinned libraries and
reviewed comparison constraints, and preserves them as unknown. This replaces
the local analyzer's broad macro exception for diagnostic replay; the original
sealed artifacts remain unchanged and physical admission remains strict.
