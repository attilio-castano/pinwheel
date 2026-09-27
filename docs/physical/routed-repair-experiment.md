# Placement, global routing and repair — September 26

Follow-up: the [tested hold-repair continuation](hold-repair-experiment.md)
fixes the tool failure and passes both retained timing floors. It retains this
study's coordinated result as the lower-congestion comparison.

**Keep the coordinated repaired layout as the leading experiment; retain the
34-buffer SRAM checkpoint as the comparison reference. Neither completed
repair qualifies physically.** Coordinated repair reaches **+0.571241 ns setup**,
clears reported electrical violations and lowers router overflow to **13**.
Two hold violations remain, with worst margin **−0.018681 ns**, and six timed
nets miss the chosen reserve. Increasing the hold target exposes a pinned
OpenROAD failure; both continuation attempts stop without a final candidate.

This experiment compares the retained 34-buffer SRAM checkpoint with the
coordinated status/decode placement using the same routed electrical, setup
and hold repair sequence. The purpose is to test whether the placement gain
survives repair against the changed wire estimates. The
[preceding study](status-region-placement-experiment.md) retains its original
placement-only results; [research status](../research/status.md) owns the active
decision.

## What changes

The saved flow disables both `RUN_POST_GRT_DESIGN_REPAIR` and
`RUN_POST_GRT_RESIZER_TIMING`. Inspection of the pinned Librelane installation
confirms that its repair steps load all configured timing corners. The custom
experimental recipe uses that native resizer context, initializes detailed
placement, performs a complete global route, repairs electrical limits and
setup/hold, legalizes the result and performs another complete global route.
Fresh, separate STA then reads the final saved database at all three corners.

The first-pass targets are 20% capacitance/slew reserve, +0.50 ns setup and
+0.10 ns hold. Existing registers, SRAM, clock cells, hold/delay cells and
clock topology remain protected. Combinational cells may legalize and change
drive strength within the same gate family; new cells must be pinned
noninverting buffers or delay cells. Independent Verilog and ODB checks
establish those actual changes, all-corner cell functions, signal identity
after contracting transport cells, legal footprints, protected geometry and
power bindings. These checks are separate from timing and routing acceptance.

The initial legalization flips 3,410 cell orientations on the retained source
and 3,000 on the coordinated source, without changing original coordinates.
Those flips change pin positions. Consequently this experiment evaluates a
legalization/routing/repair sequence; its final gain cannot be attributed to
buffer insertion alone. Separately measured prepared checkpoints distinguish
the initialization effect from subsequent repair.

## Measurement coverage

Every consumed, cell-driven signal net receives independently reconciled pin
loads and wire estimates. Package-input-driven and clock nets are outside this
electrical inventory; global reports and selected clock-expanded timing paths
remain separate checks. Constant tie nets have finite measured loads but no
reported STA limits or paths, so they are counted separately and never treated
as passing timing or reserve checks. All 64 SRAM write-data inputs retain
minimum and maximum timing checks at three corners. Exact historical paths,
competing status branches and newly failing hold paths retain distinct roles.

Qualification retains the earlier +0.3673431 ns setup / +0.07927839 ns hold
comparison floors, the experimental 20% electrical reserve, congestion and
minimum pin-access checks. Native optimizer messages do not establish that
the final route passes those gates. Temporary cell-area growth is recorded
under the [exploration policy](../research/README.md#exploration-with-temporary-size-overages).

## Completed comparison

| Measurement | Retained reference | Same repair on reference | Same repair on coordinated layout |
| --- | ---: | ---: | ---: |
| Worst slow setup, ns | +0.321638 | +0.178522 | **+0.571241** |
| Worst fast hold, ns | +0.089025 | −0.022618 | **−0.018681** |
| Fast hold violations | 0 | 1 | 2 |
| Capacitance violations, every corner | 1 | 3 | **0** |
| Slew / fanout violations, every corner | 0 / 0 | 0 / 0 | 0 / 0 |
| Router / saved-grid overflow | 16 / 15 | 27 / 27 | **13 / 12** |
| Additional cell area, µm² | 0 | +127.0080 | +174.1824 |
| Minimum SRAM write-data hold, ns | +0.161179 | +0.209883 | +0.245713 |

The matched flow is sensitive to its starting layout. On the reference it
adds five buffers and resizes three gates but worsens timing, capacitance and
congestion. On the coordinated layout it adds six buffers and two delay cells,
with no original gate resizing. The final independent inventory contains
10,891 and 10,894 connections respectively, including 1,790 constant tie nets
in each. Among timed nets, **9,094 / 9,101** meet reserve on the reference
repair, versus **9,098 / 9,104** on the coordinated repair. The original
reference's smaller 4,199-connection inventory is not used as a whole-chip
reserve denominator.

Coordinated reserve shortfalls are `_01706_`, `_01715_`, `_02353_`, `_02974_`,
`_05213_` and `net1922`. They pass reported electrical limits. The two fast
hold failures are `_12260_/Q → _10768_/D` at **−0.018681 ns** and
`_12268_/Q → _10880_/D` at **−0.005832 ns**. Global violation lists are
reconciled separately from connection reports. All SRAM write-data holds
retain the earlier comparison floor.

The coordinated area is **359,950.4640 µm²**, **0.461326%** above the original
358,297.5456 µm² reference and **578.025763 µm²** above the historical allowance.
The reference repair occupies **359,903.2896 µm²**, with a **530.851363 µm²**
overage. These totals include the inherited overage; neither is a claim that
the historical size budget passes.

## Separating initialization from repair

The coordinated source starts at **+0.181782 / −0.082617 ns** setup/hold.
Legalization and its first complete route produce **+0.460087 / −0.027616 ns**,
with three capacitance violations. Repair and the final complete route then
produce **+0.571241 / −0.018681 ns** and zero electrical violations. Most of
this experiment's setup gain already appears before repair. Conversely, the
reference's setup falls from +0.321638 to **+0.148800 ns** during initialization,
then recovers only to +0.178522 ns after repair.

The previous worst hold witness `_10937_/Q → _10884_/D` improves from
**−0.027615577 ns** at the prepared coordinated checkpoint to **+0.462380916 ns**
after repair and rerouting. Its data delay after launch grows by **505.125 ps**;
changed launch/capture clocks offset that by **15.001 ps**, with another
**0.127 ps** in required-time terms. Fixing that path does not establish the
hold condition elsewhere. The native optimizer reports its +0.10 ns hold
target satisfied, but the final complete route introduces the two failures
listed above.

Final readback preserves all original placement statuses and row definitions.
Only 13 original cell coordinates move on the reference repair and two on
the coordinated repair; thousands of orientation changes remain explicit.
All protected cells and 342 clock nets retain their identity and geometry.
Runtime routing still relaxes clock nondefault rules: the logs retain the
exact nets by phase. Fixed clock topology therefore does not imply fixed
clock wiring or delay.

Minimum pin access passes for both final layouts: **33,688 / 33,694** standard
cell pins, zero standard-cell or macro no-access counts and no off-grid warnings.
It does not establish simultaneous routability. The reference repair's 27
router/grid/native overflow units reconcile strictly. The coordinated layout's
13 router/native units disagree with its 12 stored-grid units; strict
reconciliation rejects a duplicate or stale native marker. Both have nonzero
congestion, and the latter discrepancy remains unresolved.

## Bounded continuation and tool failure

The coordinated first pass clears global electrical violations and the setup
comparison floor, but complete routing produces two different hold violations.
One continuation therefore targets +0.20 ns hold: the previous +0.10 ns native
target lost about 0.119 ns after full routing, and the retained hold floor is
+0.079 ns. This is a measured margin choice, not a guarantee that the same
loss will recur.

That attempt fails in pinned OpenROAD while inserting a hold buffer on
`ui_in[6]`. Its sole load is an already protected hold cell. The pinned
[hold-repair implementation](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/rsz/src/RepairHold.cc)
filters protected loads after choosing a buffer location, then calls insertion
with an empty load set; the
[resizer implementation](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/rsz/src/Resizer.cc)
rejects that insertion. Both exact source files and the failed log are retained.
The failed attempt leaves no final candidate.

One recorded recovery starts from the same first-pass checkpoint and skips
nets whose loads are all protected. It retains the cell protections and all
timing checks. It passes the original failure but later encounters the same
empty-load error on `_12274_/Q`: net-wide filtering does not cover the
optimizer's timing-selected subsets of loads. It also produces no final
candidate. Neither partially repaired state contributes a timing or area
success claim. The original 2,400-second CAD cap remains; the failure and
recovery both consume it. Full-route reservations increase from four to six
for the continuation, then eight for its recovery. The failed attempt consumes
two reservations conservatively despite completing only its initial route;
the failed recovery does the same. No further repair attempt is made here.

The next gate is to correct and test that empty-load behavior in the pinned
tool, then measure one bounded hold/clock-aware continuation from the stronger
coordinated checkpoint through another complete route. Preserve the original
comparison reference and all timing/reserve gates. This study supports the
coupled-flow direction but does not promote its candidate.

## Evidence limits

These are estimates from global routes under the existing 20 ns constraint.
The historical fast standard-cell −40°C / SRAM −55°C mismatch remains explicit.
Clock topology is fixed, but routed clock delay can change. No new Lean
theorem, emitted RTL change, extra pipeline cycle, full compiler/package
refinement, detailed routing, extracted timing, antenna or power-grid
qualification follows from this experiment.

## Verification and reproduction

The report binds **2,229 artifacts / 2,122 retained source versions**, including
the failed continuations and superseded verification support. Four fresh
three-corner collections supply **130,671** pin/net/corner reconciliations,
**432** selected-path checks, **1,536** SRAM write-interface checks and **72**
targeted branch witnesses. The **1,536** unrestricted regional witness records
include repeated data paths and are not independent coverage.

Twelve CAD attempts consume **1,427.573 seconds** of the original 2,400-second
cap: ten pass and two fail in native hold repair. Four edit attempts yield two
completed first-pass candidates and no completed continuation. Six complete
routes finish; eight route reservations conservatively count both failed
attempts. All twelve containers are absent and no timeout occurs. Including
the preceding regional/SRAM/control/placement work, retained CAD time is
**3,374.535 seconds**.

The reusable [repair validator](../../scripts/physical_routed_repair.py) checks
the actual native output. Its [seven tests](../../test/test_physical_routed_repair.py)
reject changed logic, bypasses, cycles, unsupported sizing, a wrong function in
one Liberty corner, changed parameters, protected-cell motion, clock/power
changes and illegal geometry. The complete portable suite passes **485 tests /
2 skips**; four additional run-local tests cover constant-net report handling.

```sh
python3 -B -m unittest discover -s test -p test_physical_routed_repair.py
```

The [tracked manifest](../../physical/experiments/routed-repair-results.json)
binds the ignored `build/validation/routed-repair-01/` directory. Reproduction
requires its retained source versions, two source checkpoints, pinned local
container image, PDK and resolved configuration. Use a new output lineage;
completed stage directories must remain immutable. The run-local `run.py`
requires a declared stage, source hash and verified candidate for measurement,
enforces serial execution and records every failed attempt against the budget.
Seven negative launch checks reject absent stages/verification, a missing route
gate, exhausted attempts/routes and reused output, before new CAD or candidate
changes. The saved report SHA-256 is
`56b5475fa26511822828d745e5b6486ad2db18e3df0fd2c1fb1453be427cc5b5`.
The container has two CPUs, 2 GiB, no network and read-only source design/PDK
mounts. The manifest alone is insufficient to replay the experiment.

An initial independent checker rejected the baseline's three native drive
changes. Its replacement accepts only same-family gates with identical pinned
pin functions at every corner. A duplicate verification-log attempt was also
rejected before replacing its outputs. Old helpers, failures, successful fresh
checks and test-source hashes remain in the evidence lineage. The constant-net
parser extension distinguishes absent STA limits from a pass. A whole-chip
report comparison uses the precise scalar slack to avoid false disagreement
with metrics rounded to fewer digits.
