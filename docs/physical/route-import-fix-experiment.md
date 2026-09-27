# Saved-route import repair and one signal buffer

Study dated **2026-09-26**. Retain `route-import-fix-01/candidate` as the next
physical exploration checkpoint. The saved-route import now passes exact
no-edit and actual edit/revert resource controls. One buffer removes one of
five electrical reserve shortfalls without changing existing cell positions,
clock routes or global worst setup/hold. **Four reserve shortfalls and 25 coarse
routing overflow units remain.** This does not qualify the chip.

[Research status](../research/status.md) owns the next decision. The
[manifest](../../physical/experiments/route-import-fix-results.json) binds the
source, candidate, measurements and sealed report. The
[earlier import controls](incremental-routing-import-experiment.md) retain their
failed verdicts; the [hold-repair checkpoint](hold-repair-experiment.md) remains
the matched reference.

## What changed and why

A saved database contains route geometry, but it does not contain every live
router data structure. The earlier import either erased demand during
initialization or applied macro pin-access capacity twice and omitted 83 units
of effective clock-rule demand. It also lacked the per-net records needed to
release an old route before replacing it.

The isolated [native adapter](../../tools/openroad-route-import/README.md)
initializes capacity once, restores the source route's explicitly recorded
runtime NDR relaxations, and reconstructs removable wire-edge records using
native per-net costs. A dirty signal is released before its replacement is
routed. The local routing path does not repeat global macro-access adjustment.
The final revision also synchronizes derived congestion counters from those
edges. It targets only OpenROAD
`dcf36133a369abc8f3c5e5738cd4d82e4903c0e0` in the recorded image; the default
image is unchanged.

These records are sufficient for the tested bounded edits, not reconstructed
Steiner topologies for arbitrary whole-chip optimization. Only the declared
ordinary signal nets enter the solver. Clock routes and macro geometry stay
fixed. This is physical-tool infrastructure; it does not change Lean semantics,
generated RTL, architectural capacity, or the correspondence proof boundary.

## Controls before the physical result

| Check | Evidence |
| --- | --- |
| Saved route identity | All **11,342 nets / 126,729 segments**, including **342 clock nets**, reproduce in no-edit and reverted controls. |
| Saved resource identity | Every capacity and usage entry on Metal2–Metal4 reproduces exactly. |
| Native accounting | An independent segment-expansion oracle checks **174,035** valid 2-D/3-D edges and the effective costs of all 11,342 routed nets. Source demand is **66,971 / 98,058 / 24,590** on Metal2/3/4. |
| Native removal | Ordinary signal `_04215_`, active-NDR clock `clk_regs`, and runtime-relaxed clock `clk` release exactly **237 / 2 / 151** 3-D demand units. Replaying each restores the full edge snapshot. |
| Actual edit/revert | Insert and route the buffer, then remove it and restore the original connection. Every checked edge, original route, cell, placement and independent circuit readback returns to the source. |
| Fresh timing control | All parsed connection and selected/write-path records reproduce the source across three corners: **32,970 load checks, 132 selected checks, 384 SRAM write checks**. |

The first native build passed edge accounting but left the cached aggregate
overflow at its initialization value after a no-edit import. A second build
corrects that separate state: two repeated controls report **25** at import and
completion while preserving all arrays and routes. Both builds and all four
controls are retained. The corrected build's intermediate edited circuit,
native routes and full edge state exactly reproduce the measured candidate.

The saved 3-D arrays are the historical reference. The 2-D edge accounting is
reconstructed and tested; unrecorded historical optimization state is not
claimed to be bitwise identical.

## The single-buffer experiment

`_08031_/X` previously drove a long wire on `_04215_` into `_08032_/A1`.
A `sg13cmos5l_buf_4` sits immediately beside the XOR driver at
**(348.00, 351.54) µm**, on a checked vacant site. The original driver now sees
the short buffer-input connection; the buffer drives the long branch.
Only `_04215_` and the new `route_probe_signal` are rerouted. All **11,406**
original cells, row/status records, clock routes, NDR bindings/effective costs,
and native capacity/reduction entries remain unchanged. Independent Verilog
readback checks the declared noninverting buffer contraction and power binding.

| Measure | Source | Candidate |
| --- | ---: | ---: |
| Slow worst setup | +0.382789 ns | +0.382789 ns |
| Fast worst hold | +0.143801 ns | +0.143801 ns |
| Electrical reserve shortfalls | 5 | **4** |
| Reported capacitance / slew / fanout violations | 0 / 0 / 0 | 0 / 0 / 0 |
| Target load's slow slew | 2.081871271 ns | **0.355251491 ns** |
| Target path's slow setup slack | +16.287141800 ns | **+17.533334732 ns** |
| Target path's fast hold slack | +0.395975590 ns | **+0.210799932 ns** |
| Minimum of 64 SRAM write hold checks | +0.145047083 ns | +0.145047083 ns |
| Native / saved-grid / marker overflow | 25 / 25 / 25 | 25 / 25 / 25 |
| Cell area | 361,583.4240 µm² | **361,597.9392 µm²** |

The two resulting branches retain **87.5% / 85.83%** electrical reserve, above
the experimental 20% floor. The physical tradeoff is explicit: faster data
reduces local hold margin by **0.185176 ns**, although it still passes. The wire
capacitance of the long branch grows slightly; stronger drive and isolation
produce the slew improvement. Two directly downstream nets inherit changed
slew, with all limits and reserve checks passing. Every other unchanged-net
load and parasitic measurement reproduces.

Fresh coverage includes **10,991** consumed cell-driven signal nets,
**32,973** load checks, **132** selected paths and **384** write checks.
Of 9,201 timed nets, **9,197** retain the reserve. The **1,790** constant ties
without reported timing limits remain separately counted. Remaining shortfalls:
`_01876_`, `_02877_`, `_04597_`, `_05213_`.

The extra cell costs **14.5152 µm²**. The historical allowance is
**359,372.4382368 µm²**; overage grows from **2,210.9857632** to
**2,225.5009632 µm²**. Total area is **0.921132%** above the original
358,297.5456 µm² reference. This is a recorded exploratory overage under the
[agreed policy](../research/README.md#exploration-with-temporary-size-overages).

## Routing and validation boundaries

Complete native demand is independently reconstructed from all saved wires,
including unchanged clock costs. Demand changes only by **+6 Metal2 / +6 Metal4**
units; Metal3 is unchanged. All **25** overflow units remain on Metal3 and
strictly reconcile with native markers and their crossing-net attribution.
The minimum-one-access-point probe finds no inaccessible standard-cell or macro
pins and no off-grid warnings. This is not simultaneous routability, detailed
routing, extracted timing, antenna closure, DRC/LVS or silicon evidence.

**79 focused Python tests**, **10 launcher refusal checks**, independent
actual-netlist/geometry checks and four native controls pass. Thirteen container
invocations comprise **11 CAD stages / 336.314 seconds** and **two native builds
/ 6.100 seconds**. Cumulative CAD time is **5,160.613 seconds**. There are no
full reroutes, CAD timeouts or surviving containers. The first comparison helper
incorrectly demanded identical downstream slew; its rejected attempt and the
six propagated slew changes are retained beside the corrected analysis.

The next experiment should address another declared remaining weak branch while
preserving this checkpoint's clock routing and timing floors. `_01876_` has the
least reserve and geographically separated consumers; an explicit consumer
partition is a useful next hypothesis. Congestion reduction remains a separate
physical question. No backend promotion follows from this result.

## Evidence and reproduction

The run lives at `build/validation/route-import-fix-01/`. Its `request.json`
freezes the source checkpoint, exact libraries/image, runtime NDR relaxations,
recorded size policy and bounded allocation. `native-01` and `native-02` retain
compiler commands, generated friend headers and binary hashes. Each CAD stage
keeps its executed recipe, helper copies, output database and settlement receipt.
The parent hold-repair bundle supplies pinned public/dependency headers;
`dependency-audit.json` verifies all **16,227** files against its sealed manifest.

`control-qualification.json`, `comparison.json`, independent Verilog readbacks,
complete edge TSVs, fresh timing reports and geometry/marker exports separate
tool admission from the physical decision. The report preserves each used
version of an input by digest; the tracked manifest cannot recreate missing
ignored build artifacts on a fresh checkout.

Focused checks from the repository root:

```sh
python3 -B -m unittest discover -s test -p 'test_physical_route_*.py'
python3 -B -m unittest discover -s test -p 'test_physical_signal_buffering.py'
```

Replays require a new output directory and a new source-bound request. Do not
rerun writers over sealed receipts. Rebuild/load the pinned adapter explicitly;
never replace the default tool or infer runtime NDR state solely from persistent
ODB bindings. Every further edit needs exact dirty-net declaration, resource
reconciliation, independent circuit/placement checks and fresh setup/hold and
electrical measurements.
