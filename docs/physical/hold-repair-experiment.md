# Protected-load hold repair and coordinated continuation

Study dated **2026-09-26**. This follows the
[coupled placement/routing/repair experiment](routed-repair-experiment.md).
**The patched continuation completes and passes both retained timing floors
with zero reported electrical violations.** Keep it as the timing candidate,
alongside the preceding lower-congestion checkpoint. Five electrical-reserve
shortfalls and nonzero congestion still prevent physical qualification.

| Measure | Preceding coordinated checkpoint | Patched continuation |
| --- | ---: | ---: |
| Slow setup slack | +0.571241 ns | **+0.382789 ns** |
| Fast hold slack | −0.018681 ns | **+0.143801 ns** |
| Reported capacitance / slew / fanout violations | 0 / 0 / 0 | **0 / 0 / 0** at all three corners |
| Timed nets below 20% reserve | 6 | **5** |
| Router / saved-grid overflow | 13 / 12 | **25 / 25** |
| Total area | 359,950.4640 µm² | **361,583.4240 µm²** |
| Overage above historical allowance | 578.0257632 µm² | **2,210.9857632 µm²** |

The new result adds **1,632.9600 µm²** to its immediate input and is
**0.917081%** above the original 358,297.5456 µm² reference. It has only
**15.446 ps** setup margin above the retained floor, versus **64.523 ps** of
hold margin above that floor. This is a measured timing/congestion tradeoff,
not final timing closure or permission for detailed routing.

## Question and fixed comparison

Can correcting the pinned hold optimizer's protected-load selection let the
strongest coordinated checkpoint complete its +0.20 ns hold-target repair,
then preserve that improvement through a new complete global route?

The input is the prior coordinated result, ODB SHA-256
`18dab93b857f9452ab19c02f037c051aa2a887ff66aeac18ec65f5015eb542c0`:
**+0.571241 ns setup / −0.018681 ns hold**, zero reported electrical violations,
six timed-net reserve shortfalls, **13/12** router/grid overflow and
**359,950.4640 µm²** total area. The original 34-buffer reference and
**+0.3673431 / +0.07927839 ns** setup/hold floors remain the comparison rules.
The selected electrical reserve is 20%. Temporary area overages are permitted
and measured against the original **359,372.4382368 µm²** historical allowance.

## Tool failure and narrow repair

The native optimizer selects loads with insufficient hold slack. Previously,
it included protected pins in that selection and in its slack calculation,
then removed them immediately before insertion. When the selected subset was
entirely protected, insertion received no loads and failed with
`RSZ-3015` / `RSZ-3009`. A net can have editable loads while its failing
timing-selected subset contains only protected pins; skipping whole nets
does not address that case.

The [patch](../../tools/openroad-hold/protected-loads.patch) excludes protected
pins at selection time. Their capacitance remains in the excluded-load
calculation, and unrepairable protected timing checks remain reported.
The exact pinned OpenROAD source is commit
`dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`.

An [experimental native adapter](../../tools/openroad-hold/README.md) builds
both unchanged and patched hold implementations against that revision's
headers and dependencies. The image's existing router, timing engine and
resizer objects remain in use. The adapter refuses other revisions; its
binary and native regression receipt are hash-bound before the chip run.
The default tool image is unchanged. This is not a general plugin ABI or an
upstream release qualification.

The chip readback adds a `sg13cmos5l_buf_16`, which the earlier repair validator
had not admitted. Its input/output directions and identity function are
checked in all three pinned libraries before extending only the routed-repair
cell set. The earlier buffer-only policy remains unchanged. A negative test
rejects a wrong slow-corner function and an unlisted drive strength. The first
failed verification, the prior support bytes, and the support revision are
retained; this changes neither the candidate nor any timing threshold.

## Native regression evidence

The same four circuits run through the native command, unchanged extension,
and patched extension: **12 checked executions**.

| Circuit | Native / unchanged extension | Patched extension |
| --- | --- | --- |
| All failing loads protected | Both reproduce the empty-load failure. | Returns without changing the circuit; the +0.011827 ns slack remains below the requested +0.20 ns margin. |
| Protected failing branch plus passing editable branch | Both fail on the input driver even though its net has an editable load. | Leaves both branches unchanged, with +0.011827 / +0.751994 ns hold slack. |
| Protected and editable failing branches | Both reproduce the empty-load failure. | Adds eight buffers to the editable branch, raising its hold slack +0.012058 → +0.210929 ns; protected connectivity and timing stay unchanged. |
| Unprotected control | Both repair successfully. | All three implementations produce identical final netlist, geometry and +0.210310 ns hold slack. |

The verifier checks original cell geometry, all protected connections, the
new buffer chain, actual timing reports, and each expected failure's cause.
The tests distinguish a successful tool return from achieving the requested
margin. Two earlier fixture setup attempts failed before timing because port
shapes and routing tracks were missing; both are retained and excluded from
the passing matrix. All fixture executions total **8.234 seconds**.

The first compiler invocation failed on Boost diagnostics because external
headers were treated as project headers. Marking dependencies as system
includes allowed the original and patched builds to complete in **13.253
seconds**, after the retained **7.289-second** failed invocation. No dependency
source was changed. A repository archive exceeded its 150 MB download bound;
the retained partial download was not extracted. An exact sparse source fetch
replaced it. These are recorded preparation failures, separate from CAD time.

## Physical protocol and evidence limits

One candidate uses the same legalization, complete routing, electrical/setup/
hold repair, legalization and final complete-route sequence as its predecessor.
The requested hold margin is +0.20 ns, setup margin +0.50 ns, electrical margin
20%, and buffer limit 3%. State, clock, existing hold cells, macro placement,
power bindings and final original placement statuses retain their protections.
Independent Verilog and database checks precede fresh saved-checkpoint STA.

Actual readback finds **90 delay cells, five `buf_8` cells and one `buf_16`**,
with no original cell resizing. All **11,310** original cells remain;
**125** move within the declared bounds, at most 11.04 µm horizontally and
15.12 µm vertically, and 30 change orientation. All **3,732** protected cells,
clock topology, power bindings, legal changed footprints and final original
placement statuses pass independent checks. Initial preparation changes no
original cell geometry or connectivity.

The optimizer reports only 37 inserted hold buffers. Its native journal
rollback branch resets the hold counter, while previously accepted additions
remain in the circuit. The study therefore uses the independent 90-cell
readback count. All 96 additions fit the declared 3% insertion budget when
checked against the original cell count; the native progress counter is not
used as an area or acceptance oracle.

Fresh measurements cover **10,990** consumed cell-driven signal nets:
**9,195 / 9,200** timed nets retain 20% reserve, and **1,790** constant ties
have no reported timing limits and are counted separately. The five reserve
shortfalls are `_01876_`, `_02877_`, `_04215_`, `_04597_` and `_05213_`;
the smallest reserve is 7.895%. Global reports show no hold or electrical
violations outside that inventory either. All 64 SRAM write inputs retain
their hold floor; their minimum is **+0.145047083 ns**.

The two formerly negative paths now have **+0.563293457 / +0.367332965 ns**
fast hold slack. The new worst path is `_12052_/Q → _12052_/D`, at
**+0.143801 ns**; the next is the SRAM write path ending at `A_DIN[5]`.
The slow setup limit starts at SRAM output bit 53 and ends at `uo_out[4]`.
The status-region reports repeat that same limiting data path 64 times, so
those records are not independent coverage.

All 25 final overflow units are on Metal3. Native marker, router and saved-grid
accounting agree, passing strict reconciliation. Five of the 25 markers
include nets incident to newly added transport cells; that association is
not causal attribution. The initial complete route already had 25 overflow
units before repair. Minimum pin access passes for **33,886 standard-cell
pins**, with no no-access pins or off-grid warnings; simultaneous routing
remains unproven.

The unchanged-circuit preparation measures **+0.518838 / +0.100468 ns**
setup/hold, already above both retained floors, but introduces two capacitance
violations at every corner and two slow-corner slew violations. Repair and
the final reroute clear those violations and add **43.333 ps** of worst hold
slack while spending **136.049 ps** of setup slack. The original negative hold
becoming positive cannot be attributed solely to the new delay cells. The
patch's direct achievement is allowing the protected-load optimizer to finish;
the physical benefit belongs to the measured combined sequence.

The campaign permits one completed candidate, two complete routes and 1,800
aggregate CAD seconds; the edit command has a 360-second cap. Each measurement
has a 240-second cap and geometry/pin access a 120-second cap. Containers use
two CPUs and 2 GiB. Build resources and native fixture time are recorded
separately. All earlier reports and manifests retain their hashes.

These are global-route estimates under the existing 20 ns clock constraint.
The historical fast standard-cell −40°C / SRAM −55°C mismatch remains.
Constant tie nets without reported timing limits are counted separately.
Clock topology can remain identical while clock arrival times change after
routing. No RTL or Lean source change, extra pipeline cycle, full compiler/
package refinement, detailed route, extracted timing, or backend promotion
follows from this experiment.

## Decision, checks and reproduction

Retain this result as the timing reference and the preceding coordinated
checkpoint as the lower-congestion comparison. The next discriminator is a
congestion-directed physical change around the **25 reconciled Metal3
markers and five reserve shortfalls**, followed by matched remeasurement.
Preserve both timing floors, protected cells, all SRAM write inputs, actual
added-cell accounting and the original area reference. The remaining setup
cushion is small; a local electrical gain alone cannot admit another route or
establish final feasibility.

Two fresh three-corner collections provide **65,652** pin/net/corner
reconciliations, **264** selected-path checks, **768** SRAM write-interface
checks and **36** targeted branch witnesses. The portable suite passes
**486 tests / 2 skips**, including eight routed-repair tests. The native
matrix has 12 checked executions and four launch guards reject missing or
changed evidence before CAD.

Four CAD stages complete in **604.601 seconds**, including the **286.901-second**
edit, two saved-checkpoint measurements and geometry/pin access. One candidate
and exactly two complete routes are produced. There are no timeouts; all
experiment containers are absent. Combined retained CAD time is
**3,979.136 seconds**. Compiler invocations total **20.542 seconds**, separately
from CAD and the **8.234 seconds** of native fixture executions.

The [manifest](../../physical/experiments/hold-repair-results.json) binds
**17,343 artifacts / 1,002 retained source versions**, including **15,914
dependency headers**, failed fixture/build setup, the checker revision, exact
native binaries and the unchanged source checkpoint. The sealed report is
`build/validation/hold-repair-01/report.json`, SHA-256
`7616001e95b92b3139519132d56f4527ac97cd181ab39985f49c42c3a365a691`.
Historical manifests and reports remain unchanged.

```sh
python3 -B -m unittest discover -s test -p test_physical_routed_repair.py
python3 -B tools/openroad-hold/verify_regression.py build/validation/hold-repair-01/regression-03
```

The [native build and regression instructions](../../tools/openroad-hold/README.md)
describe the pinned image and mounts. Reproducing the physical experiment
requires the retained ignored dependencies, predecessor checkpoint, PDK and
fresh output lineage; do not overwrite sealed outputs. The tracked manifest
identifies those bytes but does not recreate missing local artifacts.
