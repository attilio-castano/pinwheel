# Routing policy and electrical reserve

Study dated **2026-09-26**. **Retain the saved
[hold-repair checkpoint](hold-repair-experiment.md); reject these routing
policy changes.** A complete reroute changes electrical behavior even when
all cells remain fixed. Giving timing-critical nets routing priority makes
congestion worse. The intended grid-alignment probe was not exercised by the
selected tool option.

| Measure | Saved hold-repair checkpoint | Unchanged-policy reroute | Timing-priority reroute |
| --- | ---: | ---: | ---: |
| Slow setup slack | +0.382789 ns | +0.451521 ns | +0.376218 ns |
| Fast hold slack | +0.143801 ns | +0.151566 ns | +0.160825 ns |
| Capacitance violations, each corner | 0 | 1 | 1 |
| Slew violations, fast / slow / typical | 0 / 0 / 0 | 0 / 7 / 0 | 0 / 7 / 0 |
| Nets below 20% reserve, including failing nets | 5 | 3 | 7 |
| Electrically failing nets within that count | 0 | 1 | 1 |
| Router / grid / native-marker overflow | 25 / 25 / 25 | 29 / 29 / 29 | 40 / 40 / 40 |
| Minimum fast SRAM write hold | +0.145047083 ns | +0.222207367 ns | +0.231851876 ns |
| Total area | 361,583.4240 µm² | unchanged | unchanged |

Both measured reroutes retain the **+0.3673431 ns setup / +0.07927839 ns hold**
floors and all 64 SRAM write-input hold floors. The priority candidate has
only **8.875 ps** of setup cushion. All three corners retain zero fanout
violations and zero reported hold violations. These gains do not compensate
for the new electrical failures and increased congestion.

## Diagnosis and the controlled comparison

The saved source has 25 one-unit horizontal Metal3 markers, concentrated in
repeated x columns. **21 of 25** overlap Metal4 power geometry in projection.
This association does not identify a blockage mechanism: the context extractor
omits power vias, and direct Metal4 overlap does not establish Metal3 capacity
consumption. The five weak nets receive **79–98%** of their measured capacitive
load from wiring at their limiting corners.

The original experiment compared an unchanged-grid complete route with a
half-tile x-offset route. Both start from the exact saved hold-repair database,
SHA-256 `596a2c51189bc3e0abaed68103839973c3043842013787ecde5c3bbd8c6f2114`.
Both retain Metal2–Metal4 signal/clock layers, the 30% layer adjustment,
50 congestion iterations, all placement, all cells and the same constraints.
Neither performs placement, resizing, buffering, hold repair or antenna repair.

The offset option produces a useful tool finding, **not a negative result for
true grid realignment**. `global_route -grid_origin {3600 0}` reports the
requested origin, but all saved grid coordinates, capacity and usage values
remain identical to the control. Instead, **124,888 guide rectangles** move
3.6 µm to the right. The pinned
[OpenROAD implementation](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/grt/src/GlobalRouter.cpp#L2463-L2488)
applies this offset when saving guide boxes. The command's origin is expressed
in DBU, as documented in the
[global-routing reference](https://openroad.readthedocs.io/en/latest/main/src/grt/README.html#global-route).
No fresh timing collection is claimed for the shifted-guide checkpoint.

After recording this failed discriminator, `continuation.json` allocates
**one** timing-priority follow-up from the same saved source. It estimates the
source's saved global routes, then requests priority for the worst-slack 30%
of nets. The total route allowance becomes three, including the ineffective
probe; the **1,700-second cumulative CAD cap stays unchanged**. This is a
recorded change of hypothesis, not a hidden parameter sweep.

## What changed physically

Independent Verilog readback and database comparison preserve **all 11,406
cells**, their coordinates, dimensions, orientation and placement status,
all signal/clock/power connectivity, fixed geometry, rows and stored routing
rules. Added, moved and resized cell counts are all zero. The priority run's
working grid and every capacity entry match the control; routing usage changes.

The wire tradeoff is substantial even without cell edits. In the control,
`_04558_`, driven by `_08884_/X`, sees wire capacitance grow from
**0.155683 to 0.335212 pF**, with unchanged pin loading. Its fast total load
becomes **0.386603 pF**, above the **0.300000 pF** limit. The control resolves
four of the original five weak nets but creates this failure and another
reserve shortfall; `_05213_` deteriorates to **1.240%** reserve. Fewer weak nets
therefore does not mean a better candidate.

The priority candidate has **9,193 / 9,200** timed nets retaining 20% reserve:
six miss reserve and `_04558_` fails. Its weak set is `_04213_`, `_04489_`,
`_04558_`, `_04831_`, `_05213_`, `controller.r_parameter_b1_w2[8]`, and
`memory.mem_q0[16]`. Constant ties without reported limits remain separately
counted: **1,790**, not timing passes.

Total reported wire length rises **1,704,254 → 1,777,708 µm** between the
control and priority runs. Stored nondefault-rule bindings remain identical,
but runtime behavior differs: the control disables the special rule on
`clknet_0_clk_regs`; priority additionally disables it on `clk`. Fixed clock
cells and topology do **not** imply preserved clock wires or routing-rule
application. These internal relaxations are part of the measured result.

Total area remains **361,583.4240 µm²**, an increment of zero in this study.
The inherited overage remains **2,210.9857632 µm²** above the historical
359,372.4382368 µm² allowance, and **0.917081%** above the original
358,297.5456 µm² reference. The permitted exploratory overage is recorded;
this experiment supplies no new area benefit.

## Validation, custody and limits

Two fresh three-corner collections cover all **10,990** consumed cell-driven
signal nets: **65,940** load reconciliations, **264** selected path checks and
**768** SRAM write-interface checks. Independent global reports reconcile
capacitance and hold violations outside that inventory. Regional max-path
records repeat a limiting path and are not independent coverage.

Native markers, directional router totals and saved grids reconcile exactly
for all three routes. Minimum pin access passes for the shifted and priority
checkpoints; unchanged pin geometry does not establish simultaneous routing.
**53 focused tests** and **four launch guards** pass. A verifier initially
refused a convenience-path macro library absent from the frozen path set;
its revision uses the exact frozen experiment path. An initial test runner
shadowed Python's test namespace; explicit file-pattern discovery fixed that
setup error. The earlier helper versions and failed verification remain saved.
No hardware test failed during those setup corrections.

Eight CAD stages take **677.018 seconds**, with three complete routes,
two timing collections, no timeout and all containers confirmed absent.
Combined recorded CAD time with the preceding studies is **4,656.154 seconds**.
The image and default toolchain are unchanged. This study does not invoke the
experimental hold-repair extension or change RTL, Lean semantics or a backend.
The retained fast standard-cell −40°C / SRAM −55°C corner mismatch remains.
Detailed routing, extraction and final layout qualification remain open.

The [tracked manifest](../../physical/experiments/routing-policy-results.json)
identifies the sealed `build/validation/routing-grid-01/report.json`:

```text
0d0090d5cba39aa820cf790d135c9514ad727fd32fe0b9987b3e32406d3a2360
```

It binds **1,606 artifacts** and **1,521 retained source bindings**. An
independent sibling audit, `build/validation/routing-grid-audit-02.json`,
checks **5,867 hash references / 1,616 unique files**, including all seven
historical report references. Its first helper attempt assumed only the newer
report-reference schema; the corrected audit supports both recorded schemas. Recipes,
launchers, source snapshots, failed helper versions, exact readbacks and all
measurements live under that ignored run directory. `request.json` and each
stage freeze the inputs; `continuation.json` records the changed allocation;
`grid-effect.json` verifies the ineffective knob; `comparison.json` owns the
matched measurements. A replay needs a new directory and a new allocation.
The tracked manifest cannot recreate missing ignored artifacts by itself.

## Next discriminator

Return to the saved hold-repair checkpoint. Test a **local signal-distribution
repair that preserves the successful clock routing**. First demonstrate an
unchanged-checkpoint import and incremental-routing control that preserves
untouched routes and reproduces the saved timing/electrical result. Then make
one bounded physical edit and remeasure the complete inventory, both floors,
all SRAM write inputs and congestion. A partial incremental grid is not a
whole-chip congestion oracle. Any later complete reroute remains a separate
comparison because it can erase local gains.

This evidence does not justify another global routing-parameter sweep.
[Research status](../research/status.md) owns the active next gate.
