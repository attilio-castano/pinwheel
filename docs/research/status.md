# Research status

Updated 2026-09-23. This page owns the active decision and remaining gates.
[Results](results.md) indexes conclusions; [journal](journal.md) retains dated
receipts; the [submission plan](../submission-plan.md) owns acceptance criteria.
The [branch integration guide](../branch-integration.md) separates retained
interfaces, experimental candidates and remaining proof/physical obligations.
The local consolidation records the implementation and evidence in separate
reviewable milestones. Portable integration checks are recorded in that guide;
the physical candidate disposition and next research gates below are unchanged.

## Objective and current decision

Build a reloadable protocol engine that preserves specified pin timing, capture,
branching and atomic replacement, then establish physical feasibility under the
[competition constraints](../competition.md). Lean/model proof, emitted RTL,
physical implementation and board behavior are separate evidence layers.

**Retain the shared physical-edit abstraction; reject its first whole-chip
candidate qualification. Independent intake and 121 tests pass. One bounded
coarse route preserves all six original target gains, but other connections
fail: 1,142 of 1,146 retain 20% reserve, three fail and one misses reserve; a
fourth capacitance failure is outside the inventory. Slow setup is −0.055813 ns;
fast hold is positive at +0.064551 ns but below its retained floor. Overflow
rises 22 → 33; all 33 new markers reconcile with the saved grid. Area remains
+0.299786%, within the unchanged 0.3% cap. The read-only comparison now separates
the causes: mode/status loses 2.318 ns mainly in data, SRAM/status loses 0.307 ns
mainly in launch-clock delivery, and input hold loses 39.835 ps through its
capture clock. The [organization study](../physical-organization-study.md) now
checks the 1,152-connection watchlist and compares existing trees, bounded
regrouping and local decoding in 4.112 seconds without CAD. Twelve swaps across
fourteen branches preserve virtual identity but have no complete conditional
wire-budget pass. Restoring the earlier clock environment still leaves mode
and SRAM setup below the retained floors. Two decoder copies total 21.7728 µm²,
exceeding the remaining 0.767837 µm²; their broader physical potential remains
open. Next obtain the two missing parent-net measurements and opposite timing
checks, then compare regional tree replacement/reuse and decoding under an
explicit structural budget. Keep original budgets, the local evidence,
43-buffer control and opt-in pipeline. Detailed routing remains unadmitted.**

The [full-capacity paired model](../compact-execution-study.md#full-capacity-follow-up)
retains canonical E64 operations and the 256-position/32-record capacity using
one 512×64 SRAM, banked parameter tables and a one-read successor schedule.
The [complete controller](../compact-execution-study.md#complete-controller-and-macro-timing)
passes core/package traces and both mapped-corner arbitrary-state SAT checks.
It has 1,572 physical FFs. Its conditional Lean schedule lemmas and these
artifact checks leave complete compiler/admission/package refinement open.

The [shared physical target](../physical-targets.md) binds the exact mapping,
macro views, typed state and four semantic path roles. The clock/status repair
cleared 113 clock fanout failures and raised placement setup to +1.089 ns,
retaining 25.24% less area than the old control at the post-CTS stage.

The saved [bounded coarse route](../physical-targets.md#bounded-coarse-route)
completed its single GlobalRouting step in **36.283 seconds** under a 600-second,
four-CPU, 6 GiB cap. Overflow fell from the retained routed control's **1,310
to 41**, a **96.87% reduction**. Area stayed **354,010.1184 µm²**, 26.92% below
the routed control. The separate 2.348-second
minimum-pin-access probe passed for standard cells and the macro. Individual
access does not establish simultaneous detailed routability.

That baseline exposed −2.493735 ns slow setup, −0.659543 ns fast-screen hold
and signal electrical failures. The [local repair](../physical-targets.md#local-repair-with-coarse-wire-estimates)
raises slow setup to **+0.071044 ns** and fast hold to **+0.072689 ns** in its
incremental coarse estimates. All three local measurements pass setup, hold,
fanout, slew and capacitance with complete consumed-net annotation and verified
nominal RC. The full reroute below supersedes these local estimates for the
current decision; the fast screen still uses mismatched cell/SRAM temperatures.

Four clock repeaters, 111 signal-driver buffers, 126 endpoint delay buffers and
one SRAM receiver buffer retain all original cells and locations. Area is
**357,660.6912 µm²**, 1.03% above the baseline and 26.17% below the routed control.
No state or pipeline cycle is added. Independent buffer contraction transfers
the 331,401-edge functional trace, and an input-corruption control is rejected.
State/path, macro geometry, power-binding and corridor checks pass. **25 focused
tests** pass, all **36 exact containers** are absent, and 514 prior identities
are preserved. The [local-repair manifest](../../physical/experiments/paired-local-repair-results.json)
binds the selected database and staged evidence. Physical closure remains false.

The [whole-chip reroute](../physical-targets.md#whole-chip-reroute-of-local-repair)
completes in **58.116 seconds** under the same 600-second/four-CPU/6 GiB bound.
Fresh timing gives **+0.430335 ns slow setup** and **+0.081790 ns fast-screen hold**,
with zero setup/hold/fanout failures in all corners. Overflow falls **41 → 22**,
all on Metal3; the independent pin-access screen passes. The router disables a
special routing rule on `clk` to reduce congestion, so wire policy is not
identical even though clock connections and cells are unchanged.

Electrical failures reappear on **27 signal nets**: 21 eight-load distribution
nets and six SRAM write-input nets. Slow slew/capacitance counts are **80/16**;
fast counts are **4/19**. No clock net violates an electrical limit. Netlist,
placement, state and area remain unchanged from the local candidate. The distinct
added-buffer intake passes **49 focused tests**; all six exact containers are
absent. The [reroute manifest](../../physical/experiments/paired-reroute-results.json)
binds these current measurements, including complete coarse wire estimates.

The [connection diagnosis](../physical-targets.md#connection-diagnosis-and-checked-repair-plan)
reproduces both local and full-route measurements in **20.684 seconds** of
read-only collection. Unchanged consumers and pin capacitances accompany
**1.03–3.52× larger wire capacitance** on the 27 failing nets. Typed ownership
separates one mode-control branch, nine serial-data branches, eleven
parameter-word control branches and six SRAM write inputs. A shared validator
and generator prepare **21 driver buffers and six SRAM receiver buffers** while
retaining every original cell and hold delay. Their predicted cell-footprint
cost is **636.8544 µm² (0.178%)**; the following probe tests that candidate.

The saved grid accounts for all **22 Metal3 overflow units**: 17 lie above SRAM,
one overlaps its body and one the reserved corridor. Only seven hot cells
overlap guides of the failing nets; electrical repair cannot be assumed to
resolve congestion. Stored clock-rule bindings match between checkpoints even
though the router log records the `clk` override, so both forms of evidence
must be retained. **35 focused tests** pass; all six diagnostic containers are
absent. The [preparation manifest](../../physical/experiments/paired-repair-plan-results.json)
binds the diagnosis and unexecuted plan. No new repair or route ran.

The [bounded signal repair](../physical-targets.md#bounded-probe-of-the-checked-signal-plan)
then executes that exact plan in **6.005 seconds**. Independent whole-chip STA
and geometry collection takes **12.448 seconds**; detailed connection reports
and a separate saved-placement check take **12.752 seconds**. All three corners
have zero setup/hold/fanout/slew/capacitance violations. Slow setup rises from
**+0.430335 to +0.527857 ns**; fast-screen hold stays **+0.081790 ns**.
All 54 changed/new nets pass electrical limits and both min/max path checks.

Independent readback verifies the exact 27-buffer edit and unchanged logic,
including the shared SRAM-bit-21 serial consumer. Every original cell/location,
all **342 clock-net connections**, macro/corridor geometry and hold cells remain
unchanged. Added cells pass placement and power-terminal binding checks. Area
is **358,297.5456 µm²**, exactly the predicted 0.178% increase. All eight exact
containers are absent. The [signal-repair manifest](../../physical/experiments/paired-signal-repair-results.json)
binds the locally qualified candidate. At that stage, the source's 22 overflow
units were not replaced by the incremental grid's zero count.

The [whole-chip qualification](../physical-targets.md#whole-chip-qualification-of-the-signal-repair)
now completes one **100.452-second** route with all automatic repair disabled.
Fresh slow setup is **+0.408159 ns**, fast-screen hold **+0.088087 ns**; all corners
have zero setup/hold/fanout violations. All 27 targeted nets and all 54 edited
connections pass electrical checks, but **15 different nets** fail: 14 eight-load
distribution branches and SRAM `A_DIN[51]`'s hold-buffer output. Slow slew failures
fall **80 → 16**; fast/slow/typical capacitance counts are **13/12/12**. Saved
local/full-route comparisons find unchanged pin loads and **1.025–2.682×** wire
capacitance on these residual nets. This is measured variation, not a universal
margin bound.

Minimum pin access passes. Metal3 overflow changes **22 → 21**, with only two
locations retained; one remains at the macro edge and none overlaps the corridor.
The router relaxes nondefault rules on three clock nets, versus one previously,
despite unchanged stored bindings and topology. The exported netlist, placements,
state and **358,297.5456 µm²** area remain identical to the local candidate.
Fresh intake distinguishes the immediate edit from full functional ancestry;
**41 focused tests** pass and all **nine exact containers** are absent. The
[signal-route manifest](../../physical/experiments/paired-signal-route-results.json)
keeps successful collection separate from failed electrical/congestion qualification.

The [measured distribution contract](../physical-targets.md#measured-distribution-contract)
then inventories **1,067 connections in 211 trees**, including all 64 SRAM write
inputs and their buffer/hold neighborhoods. Two saved-checkpoint measurements
take **57.258 s** and reproduce the global metrics. A 20% experimental electrical
reserve selects the 15 failures plus **18 passing neighbors**, including SRAM
bit 50. The **unexecuted** plan adds 31 driver buffers and two receivers, costing
**778.3776 µm² (0.217243%)** against a 0.3% cap. It requires 20% cap/slew reserve
on the rebuilt inventory plus new branches and at least 90% of every corner's
current setup/hold slack. Minimum slow setup/fast-screen hold floors are
**+0.367343/+0.079278 ns**. Shared membership and routing evidence remain explicit;
the measured wire ratio is not a universal bound. **54 focused tests** and recipe
syntax pass, and three containers are absent. The
[distribution manifest](../../physical/experiments/paired-distribution-results.json)
records zero executed repairs and zero new routes.

The [local execution](../physical-targets.md#local-qualification-of-the-distribution-contract)
then applies that exact plan once in **5.658 s**, with **41.223 s** of independent
physical checks. All **1,100 connections** retain at least **26.12% capacitance
and 21.87% slew reserve** across the three corners. Whole-chip electrical
violations become zero; worst setup/hold slack remains **+0.408159 ns slow setup /
+0.088087 ns fast-screen hold**. Area becomes **359,075.9232 µm² (+0.217243%)**.
All original cells/placements, 342 clock connections, hold cells and execution
boundaries remain. Added placement and power bindings pass, as do **61 focused
tests**; eight containers are absent. The
[distribution-repair manifest](../../physical/experiments/paired-distribution-repair-results.json)
records the local contract pass separately from unresolved whole-chip routing.
The closest reserve is only 1.87 percentage points above the target, so fresh
routing must remeasure passing neighbors too. No extra route ran in this study.

The [whole-chip distribution requalification](../physical-targets.md#whole-chip-requalification-of-the-distribution-contract)
then completes exactly one route with fixed cells and disabled automatic repair.
Identity, placement and minimum pin access pass; area stays **359,075.9232 µm²**.
All 33 repaired nets and 33 added branches keep the 20% reserve. Across all
1,100 connections, **1,091** meet reserve, six fall below it and three violate
capacitance. `A_REN` adds one slow slew failure outside this write/distribution
scope. Slow setup becomes **−0.074067 ns** and all three hold-retention floors
fail, although hold remains positive (**+0.041429 ns** in the fast screen).

Saved-path comparison identifies **+0.615247 ns** of gate-delay growth on the
one-receiver status connection `_02486_`, outside the branching inventory. The
worst output path changes SRAM bit 51→53; a matching bit-53 prefix supplies the
comparison without pretending those complete worst paths are identical.
Input-hold data arrival is unchanged, while fast capture-clock arrival grows
**46.659 ps**. These observations support separate status-load and clock-arrival
budgets; they do not isolate a routing-policy cause.

Native router markers now reconcile actual capacity/demand with every saved
overflow cell. The old zero-capacity macro-edge overflow disappears, but a new
edge has capacity/demand **3/4**; the other nineteen are **10/11 or 11/12**.
Only three hotspot locations persist. Total **21 → 20** congestion is essentially
unchanged. A negative control rejects inherited local marker records as stale.
Nine stored clock rules are retained, but the router relaxes only `clk` this
time instead of three nets. **73 focused tests** pass; all fourteen exact
containers are absent. The
[distribution-route manifest](../../physical/experiments/paired-distribution-route-results.json)
records successful collection and failed qualification separately. The local
follow-ups below test a concrete repair and its whole-chip route. Extraction
has not run.

The [path/control follow-up](../physical-targets.md#local-qualification-of-path-and-control-guards)
adds nineteen timed connections before selecting a repair. These cover the
single-receiver status link, seven input-hold endpoints and all eleven dynamic
SRAM control/address inputs. Write-enable joins read-enable after measuring
only **3.66%** slow slew reserve. Nine distribution-driver buffers, one status
buffer, two SRAM-enable receivers and two small buffers at each input endpoint
make **26 buffers** total. No original cell, clock connection or hold cell changes.

The local probe and independent checks total **61.204 s**, including source
diagnosis. All **1,145 connections** meet the 20% reserve; the lowest capacitance
and slew reserves are **20.88% / 22.12%**. Whole-chip setup/hold and electrical
counts pass, with **+0.436742 ns** slow setup and **+0.093797 ns** fast hold.
Exact paths show lower status load, much faster SRAM enable transitions and
**82.4–88.6 ps** additional fast input data delay with unchanged capture-clock
arrival. Thus the hold repair does not depend on changing the clock tree.

Area becomes **359,360.7840 µm²**: **284.8608 µm²** for this repair and
**0.296747%** cumulatively above the original distribution-budget reference.
Only **11.6542 µm²** remains under its fixed cap. Fresh readbacks transfer the
331,401-edge trace through 328 added buffers and 168 prior resizes; corruption,
placement and power checks pass. **74 tests** pass and ten containers are absent.
The [path-repair manifest](../../physical/experiments/paired-path-repair-results.json)
binds the local result. Its incremental zero-overflow grid does not supersede
the source's twenty native congestion edges; the independent follow-up below
owns the new whole-chip evidence.

The [whole-chip path/control follow-up](../physical-targets.md#whole-chip-requalification-of-path-and-control-guards)
adds shared admission that rebuilds the complete declared scope and every stage,
reparses raw measurements and retains the original cumulative budgets. **90
focused tests** pass. One **92.059 s** route preserves the exact netlist,
placements, clock connections and power bindings. Fresh setup/hold is positive
in all corners and above the original floors: slow setup **+0.420384 ns**, fast
hold **+0.101286 ns**. All nineteen repaired connections and twenty-six new
branches retain reserve; **1,139/1,145** total connections qualify.

Two existing eight-load `buf_1` nets, `_03253_` and `_04701_`, fail capacitance;
the first accounts for all nine slow slew violations. Four more connections
miss the fixed 20% reserve: `_02981_`, `_03380_`, `_04527_` and SRAM DIN14 branch
`net31`. Pin loads are unchanged, while wire capacitance on the two failing nets
grows **2.57× / 2.13×** relative to local estimates. These ratios are measured
evidence, not a new safety factor. Cumulative area remains **+0.296747%**.

The final flow reports **22 overflow units** (21 Metal3, one Metal4); native
markers number 22 but the saved grid exposes only 21. The strict reconciler
rejects complete attribution and retains a matching 21-marker subset. The extra
horizontal marker at **(511.2, 352.8) µm** remains unresolved. Stored clock rules
are unchanged, but runtime relaxation now includes `clknet_0_clk_regs` as well
as `clk`. Minimum pin access passes and all eleven containers are absent. The
[path-route manifest](../../physical/experiments/paired-path-route-results.json)
records successful timing retention separately from failed full qualification.

The [physical organization policy](../physical-targets.md#physical-organization-policy-and-saved-chip-screen)
now separates measured tree ownership, permitted transformations, exact edits
and eventual qualification. The saved-chip reconstruction counts **211 trees,
1,109 family branches, 774 buffers, 124 delay cells and 4,613 leaves**, preserving
the broader 1,145-connection contract. Pin loads across all 64 branches in the
four affected trees match **192 independent library/corner checks**. The policy
protects clock/hold/state boundaries and retains every original budget.

Of **18 costed choices**, no complete portfolio passes the present geometry
rules. Stronger drivers for all six residual connections cost at least
**18.1440 µm²**. Eight zero-area bit-53 consumer exchanges reduce geometric span
on three targets, but only about 2% on failing `_03253_`; electrical benefit
is unmeasured. Virtual copies of the saved independent netlist preserve complete
buffer-contracted identity for both nonempty exchange candidates. **107 focused
tests** pass. The final screen takes **7.330 s**, and no CAD or physical edit runs.
The [organization manifest](../../physical/experiments/paired-organization-results.json)
retains the complete comparison and its evidence limits.

The [locality follow-up](../physical-targets.md#local-qualification-of-the-organization-policy)
implements that bounded extension. The same-row move preserves orientation and
checks both incident pins against the pinned LEF; weak-branch grouping uses
individual wire budgets. Of 104 screened combinations, thirteen pass footprint,
area and the explicitly conditional wire-span scenario. The selected plan moves
`_09463_` **0.48 µm left** and redistributes bit-53 leaves without adding buffers
to that family. Two driver upgrades and one DIN14 receiver bring the increment
to **10.8864 µm²**.

One **18.720 s** local probe passes the complete original numerical budgets
over **1,146 connections**. Minimum reserves are **24.56% capacitance / 21.53%
slew**; every global electrical violation is zero. Worst setup/hold and all
original timing floors are retained. `_03253_`'s pin capacitance stays fixed
while wire capacitance falls **0.322079 → 0.042548 pF**, with its original driver.
Fresh readbacks confirm the exact edit, original clock/power connectivity and
all 2,202 protected instances. Minimum pin access and **110 tests** pass; all
nine exact containers are absent. The
[locality manifest](../../physical/experiments/paired-locality-results.json)
binds the candidate and original-budget qualification. Its incremental zero
overflow is not new whole-chip congestion evidence.

The [whole-chip follow-up](../physical-targets.md#shared-physical-edits-and-whole-chip-requalification)
now extracts four reusable checked edit operations and extends shared intake to
recompute the candidate and original budgets. One coarse route completes under
**600 s / four CPUs / 6 GiB**, with automatic repair disabled. All six original
weak connections retain their gains, but new capacitance failures appear in
serial-shift bits **49–51** and the shared control net `_01924_`. The latter is
outside the family inventory and lies on the new worst mode-to-status setup
path. Independent whole-chip checking therefore remains essential.

There are four capacitance failures per corner and twelve slow slew violations.
The 1,146 scoped connections comprise 1,142 within reserve, three failing and
one with only **19.9146%** slew reserve. Slow setup **−0.055813 ns** and fast hold
**+0.064551 ns** miss their original retained floors. Exact netlist/placement,
power bindings, area and minimum pin access pass. Ten exact containers are
absent; the [manifest](../../physical/experiments/paired-locality-route-results.json)
records completed collection and failed physical qualification separately.

Saved matched input-hold reports already show identical data arcs and **39.834 ps**
later capture-clock arrival. The worst setup source changes from SRAM to
`r_mode[0]`; its matching prior path is absent from the saved top-1,000 report.
All nine stored clock-rule bindings remain, while the new log has no runtime
relaxations versus two previously. Do not attribute the regression solely to
grouping. New **33-marker / 33-grid / 33-flow** Metal3 congestion fully reconciles;
the older 22-marker / 21-grid discrepancy remains open for its source artifact.

The [matched comparison](../physical-targets.md#matched-clock-control-and-capacity-diagnosis)
uses the exact same pin/transition/cell sequence on four paths, in all three
corners on both saved chips. The formerly unreported mode-to-status path changes
**+2.262653 → −0.055813 ns**. Its **2.318466 ns** arrival increase comprises
**2.299226 ns data / 0.019240 ns launch clock**. The `_01924_` driver, following
wire and first receiver gate account for **1.534994 ns** of that data increase.
Its wire capacitance grows **0.115121 → 0.309965 pF** with unchanged pin geometry
and loads. SRAM/status separately loses **0.205627 ns** in launch clock and
**0.101463 ns** in data. The input-hold match confirms later capture-clock
delivery, while the prior worst parameter self-hold path keeps its margin.

All **118 connections** in five complete affected transport trees pass reserve
in the old full route; **113 pass / four fail / one misses reserve** in the new
one. Six control branches are outside the old scope, so the measured watchlist
proposes **1,152** connections for the next candidate. It records four exact
paths and thirteen clock nets without changing production admission or budgets.
Five successful read-only commands total **50.489 s**; four diagnostic rejection
controls pass, and six collector plus two source containers are absent.
The [manifest](../../physical/experiments/paired-coupling-results.json) preserves
the initial syntax failure and all completed receipts. No physical edit occurs.

The selected families cross 21 of 33 reconciled congested edges; ordinary clocks
cross nine, all have other signal traffic, and none directly contains a stored
NDR-bound net. The pinned router source confirms runtime softening changes
in-memory cost without clearing the database rule. This explains the evidence
distinction, but does not justify relaxing clock rules as a capacity repair.

The [received-frame study](../chip-physical-study.md#received-frame-ownership-and-bounded-site-exchanges--september-22)
binds all 2,895 physical FFs to typed state and identifies an 871-cell receiver,
decode and distribution region. Most word FFs are already near SRAM: 53 below
SRAM0, three below SRAM1 and two beside the macros. Bits 0–4 account for 72.3%
of word-family span, but none of its 44 Metal4 interior-overlap nets.

Three bounded site-exchange screens preserve occupied footprints and all 670
clock-net geometries. Their best complete region/displacement span saving is
only 0.2085%, every pin of all ten diagnosed electrical nets stays unchanged,
and 16 arcs on hold-adjacent nets shorten. Reject these local rearrangements;
no physical run is admitted. Fourteen focused tests and an independent full-chip
accounting check pass; the complete analysis takes 1.587 s.

**Next: screen data organization and clock-delivery control as separate choices.**
Use the measured watchlist to retain the six new control branches, complete
affected trees, four exact paths and thirteen clock nets. Compare area-neutral
regrouping across the shared-control and serial families. Separately inspect
whether the pinned routing interface can preserve or constrain the observed
clock branches; prove that support before proposing an execution recipe.
Only **0.7678 µm²** remains in the original allowance. A subsequent physical
candidate must address both timing mechanisms without losing global capacity
or passing neighbors. No new repair or route is selected by this diagnostic
result. Detailed routing, antenna closure, extraction and physical power
qualification remain open.
The experimental 290-word upload format is still opt-in.

Keep the drive/buffering change on `net3533`, the SRAM-only bit-41 write branch,
as a fallback experiment on the control, including both replicas and the
existing hold chain. It is no longer the active next step merely because the
first compact encoding failed.

The preceding upload-stage
[locality screen](../chip-physical-study.md#upload-stage-locality-and-available-placement-space--september-22)
finds that 41 of the earlier 44 Metal4 interior crossings also feed other logic;
only three are SRAM-only. Both pin-face bands together fit at most 37 adjacent
FF/mux pairs even after optimistic branch removal, short of 62 actual mapped
payload pairs. Allowing separated muxes and overlapping FF centers within each
free interval still increases the best span estimate on 96 affected data nets
by 50.52%. No placement or routing run is admitted by these configurations.

The shared received-word/decoder/distribution boundary is now accounted for
above, including external consumers and displaced cells.
The [earlier interface screen](../chip-physical-study.md#sram-interface-geometry-and-upload-staging--september-22)
also retains south-facing pins, almost complete Metal2/3 obstructions and rejected
isolated macro-mirror projections.

The 71-bit upload stage drains writes on eligible idle edges and preserves
running/start reads. Queue/memory-view and emitted-priority proofs pass;
14,200 core edges and 508,252 complete-chip pin edges pass, and a write-priority
mutant fails behaviorally. Matched synthesis adds 7,580.4876 µm² (1.926141%)
against the shared reference hybrid assembly. This is not yet a comparison
against the retained optimized physical chip. The stage still distributes a
64-bit word to two replicas. Its complete execution refinement, placement,
clock/hold cost and wire benefit remain open; no new routing was launched.

The preceding
[bounded electrical-cost diagnosis](../chip-physical-study.md#electrical-cost-and-sram-interface-geometry--september-22)
finds that all ten remaining electrical groups have only two or four sinks,
with 82–97% of their slow load due to wires. Its one local probe fails after
17.801 s with OpenROAD `GRT-0183` during an incremental route update, before
saving a candidate. The source is unchanged; the failure is neither a timeout
nor evidence that the microarchitecture cannot fit.

Read-only saved-grid analysis places every recorded overflowing cell in the
lower SRAM strip and about 90% of its overflow inside the macro footprints.
Only about 2% is in the reserved corridor. Capacity maps are identical across
the two retained routes, but the pinned exporter includes reductions in both
stored capacity and usage: equal capacity alone does not establish equal
obstruction effects. Saved-grid totals are 1,298→1,309, while flow totals are
1,302→1,310; the differences remain explicit. The interface study binds pin
shapes, obstructions, power geometry and structurally classified traffic.
Require a measurable improvement across every affected connection before
another physical run. The current storage/fetch and exact-edge contracts remain fixed.

The retained
[local data-buffer study](../chip-physical-study.md#local-data-buffering-and-complete-wire-estimates--september-22)
targets 29 driver nets while preserving all original cells, their placement,
existing hold-delay cells and all 670 clock nets. One fresh coarse route takes
42.652 s within its 600 s/four-CPU/6 GiB cap; independent diagnostics take
14.466 s. Nominal layer RC and complete annotations are checked in every screen.

Against `local-route-01`, slow setup improves **+2.021800→+5.339320 ns** and slow
slew falls **58→22**. The change clears 57 previous pins and exposes 21 other
violators. Eleven of twelve SRAM address inputs and all four enable inputs now
pass. `_09593_/X` falls 0.308889→0.117662 pF in the slow screen, below its
0.300000 pF limit; all seven previously repaired SRAM outputs also still pass.
Setup, hold and fanout violations remain zero in all three screens, but minimum
hold margin decreases +0.093542→+0.060261 ns. Capacitance violations become two
typical, one slow and two fast. Overflow changes **1,302→1,310**, so congestion
has not improved.

The electrical diagnosis covers **ten driver groups**: eight nets account
for the 22 slow slew pins (one SRAM address, eight upload-data and 13 standard-cell
pins); `storage0/A_DOUT[36]` and `[50]` add two output-load groups. They remain
unresolved after the failed probe. Preserve clock topology and hold delay, and
check all nets for new violations after any future rerouting. No new candidate,
standalone routing run or functional simulation was produced by this diagnosis.

This study also rejects incomplete placement timing. A fresh placement-only
initialization has 513 partially unannotated drivers on the unchanged control
and 524 on the candidate. The apparent local timing pass is unqualified.
Functionality and geometry justified one diagnostic route to obtain complete
wire estimates; they did not substitute for timing admission. The finished
coarse route has zero partial or consumed unannotated nets.

The buffers add **769.3056 µm² (0.16%)**, bringing instance area to
**484,422.6752 µm²**. The candidate passes 508,252 independent pin edges and one
rejected output corruption. Exact post-route export identity reuses that result
without repeating simulation. Fifty-five focused tests pass; closeout checks
531 artifacts, all 267 unchanged Lean sources, 53 prior experiment files and
22 prior receipts. Every run container is absent. Detailed routing, antenna
closure, extracted timing and backend promotion remain gated; the fast screen
uses −40 °C cells and −55 °C SRAM.

The earlier [exact-mapping comparison](../chip-physical-study.md#exact-mapping-placement-and-hold-repair--september-22)
remains the area control: 473,519.9456 versus 485,738.1152 µm² after placement
and repair, under identical constraints. Its candidate finished coarse routing
in about 93 s with 1,312 overflow; the baseline timed out at 600 s, leaving no
matched baseline final routing result. The latest clock policy spends most
of that 2.52% area margin. Both retained policies preserve the same mapping
and execution contract.

The [fetch contract study](../fetch-contract-study.md) connects actual edge
obligations to these measurements. Same-edge capture forwarding is proved for
arbitrary states, and a valid-word premise permits a narrower entered-word
metadata calculation. Neither changes production RTL or creates a timing
exception. The load-budget candidate adds only 209 mapping buffers over the
earlier combined chip, versus 1,369 for flat repair. Its earlier −0.86 ns
cell-only hold result is now followed by measured repair cost and a fresh
coarse-wire screen. Exact intake prevents resynthesis from erasing the mapping
choice. The physical follow-up shows why clock loads, wire capacitance and
minimum delays must join the aggregate load contract; fewer gate levels or
positive placement slack alone cannot justify detailed routing.
The completed
[architecture comparison](../chip-architecture-study.md) accounts for every
mapped FF in the existing hybrid and direct chips. Hybrid's macro-address cone
contains 6,037 combinational cells and reaches all 2,560 map bits; direct's
contains 607 cells and no scratch state. Direct moves lookup work into upload,
but saves 113,189 µm² of standard cells at a cost of 199,227 µm² more SRAM.
Both responses feed both address ports: execution/fetch is one coupled locality
problem. These structural measurements do not establish routed superiority.

`SramAssembly` now provides one typed source for package composition, state
owners, emitted names, seven SRAM crossings and eight named computations.
`SramSchedule` connects thirteen
edge obligations to the existing controller/array model. The analyzer checks
all named state and ten macro address/data/enable terminals per variant against
the saved mapping and Verilog read-back. All four regenerated MLIR and RTL
artifacts are byte-identical to the earlier comparison. The complete cached
gate takes 11.456 s; graph analysis/read-back takes 2.320 s. Thirty focused
architecture tests and six new tile-checker tests pass. Keep hybrid as the mapped-area baseline and direct as the
organization comparison; neither backend is promoted.

The [computational map](../chip-architecture-study.md#computational-map-and-phase-cuts)
accounts for every mapped cell once, with explicit shared consumers. Hybrid's
fetch region contains 12,094 of 12,593 combinational cells, too broad for a useful
placement constraint. Its read-address envelope excludes the 64-bit upload
payload but retains all 2,560 map bits; it includes idle/commit, not only running.

The [first locality screen](../chip-architecture-study.md#a-cheap-test-rejects-the-first-locality-projection)
selects 70 final address gates from saved physical connectivity. Projecting them
toward the SRAM pins raises the estimated span of all 170 incident signal nets
by 84.6%; none of the individual projections improves it with neighbors fixed.
Defer that projection. This is an unlegalized center-based geometric proxy,
not measured routed length or a proof that every placement would be worse.
The [map-slice study](../map-slice-study.md) now costs that wider dependency
boundary. One bit plane owns 512 FFs and 1,986 private gates (48,576.5532 µm²)
but imports 1,073 nets, mostly shared with other planes. Consecutive 16-word
groups fragment the actual read trees. Groups with a fixed low address nibble
retain more of both readers: the first tile has 80 FFs, 294 private gates,
280 incoming nets and 13 outgoing nets, versus 90 outgoing nets for consecutive
words. Whole-map boundary nets are 1,265 for five planes, 4,099 for consecutive
tiles and 1,615 for strided tiles; these are graph cuts, not routed costs.

The [completed tile experiment](../map-tile-study.md) reuses the proved
`Memory.Flops.circuit 4 5 2`. Its 18 functional inputs and ten outputs survive
mapping. Both reads and every update match the actual controller projection.
A matched map-only comparison, including all 32 tiles and glue, reduces area
253,254.9348→250,189.4304 µm² (1.21%) and read depth 14/13→9/9 gate levels.
Nine independent arbitrary-state RTL/mapped SAT checks pass in a 77.772 s run.
The [distribution follow-up](../map-tile-study.md#bounded-distribution-result)
adds 346 buffers without changing tile/glue internals. It reduces maximum signal
fanout 224→10, raises read depth 9→10 and leaves next-state depth at eight.
Area becomes 252,700.5600 µm², only 554.3748 µm² (0.2189%) below the flat map.
Both mapped corners pass independent next-state/output SAT, and an inverted
buffer is rejected, in 37.020 s. Fourteen focused checker tests pass; all 239
inputs to the existing production identity gate remain unchanged. Keep the
candidate experimental. Sink count and gate depth do not establish electrical timing.

The [complete-chip follow-up](../map-tile-study.md#complete-chip-integration--september-22)
now connects the actual PCs, selected bank and admitted writes to the tiles.
The shared map emitter and retained hybrid chip/core emissions stay byte-identical.
Lean proves netlist substitution, retained transitions, core observations, both
map reads and every admitted update. Four RTL/mapped SAT checks, a rejected
address mutation, 508,252 pin edges on RTL and each mapped corner, and 11,840
core stress edges pass in 254.643 s. Twenty-four focused tests pass; the audit
covers 14,831 declarations / 7,529 theorems with standard axioms only.

Typical standard-cell area changes 292,580.0514→288,888.2010 µm²; the two SRAM
footprints remain 100,978.2656 µm². Address depth changes 29/29→30/30 and next-state
depth 27→24. Slow mapping has the same disposition. Cursor bits zero/one each
drive eight engine and seven map pins; some upload bits also serve both macros.
One deepest candidate address path has twenty engine gates and ten map gates.
Preserving a storage boundary does not settle the appropriate combinational
optimization boundary. No backend is promoted and no timing/physical run is
allocated to this candidate.

The [combined boundary study](../map-tile-study.md#combined-controller-and-selection--september-22)
then optimizes controller and selection together, retaining storage tiles and
budgeting all controller/tile/SRAM consumers. It inserts 354 buffers and reaches
fanout ten. Both corners map to 289,427.1156 µm² of standard cells, address depths
30/29, next-state depth 25 and package output depth 15. The last is a regression
from baseline 14/13. Four equivalence checks, two rejected wiring/buffer mutations,
1,536,596 simulated edges and 27 focused tests pass in 274.167 s. The longest
address paths contain eighteen gates before a candidate PC, one distribution
buffer, four tile gates and seven/six final selection gates. These conservative
paths require semantic diagnosis before another implementation experiment.
All Lean sources and 45 preceding experiment manifests remain unchanged.

Retain the half-height placement corridor: it reserves 24.82 µm and improves
global overflow 1,255→870 and Metal4 body-overlapping guides 129→45. The latest
[diagnostic cycle](../routing-diagnostics.md) rejects `hybrid-chip-15`: early
Metal4 obstruction objects leave global guides and saved capacities unchanged.
Explicit regional capacity control remains a possible flow diagnostic, deferred
while the organization is made explicit. It is not the current work allocation.

The three-hour `hybrid-chip-14` retry completed all four detailed-routing passes
and RC extraction, but timed out before completing extracted timing. Its final
antenna check still reports three violating nets and four pins. Retained routing
reports accumulate old and duplicate markers: their 73/174/283/384 pass-end
counts become 75/103/112/103 under fresh static DRC. The completed routing ODB
independently has **103 fresh markers**, including 101 on Metal4 inside SRAMs
and two on Metal2 outside them. This is an unclean layout, not routing closure.

These checks take seconds: the combined report takes 6.7 s, pin access about
3.6 s and fresh static DRC about 9 s. Both candidate access probes pass under
the resolved Metal2–Metal4 limits. Timing figures inherited from different flow
stages are kept separate. The earlier `hybrid-chip-13` endpoint is corrected to
pass 1 iteration 38 with 198 markers; 35/230 was its shorter log's snapshot.
All diagnostic containers are confirmed absent; the old retry heartbeat is
paused. No second global screen or new detailed route is allocated in this cycle.
Extracted timing, antenna closure and final layout qualification remain open.

Hybrid still has the best complete mapped-area screen: 393,558 µm² versus
479,596 for direct SRAM and 622,897 for matched flip-flop storage. Physical
repair raises its cost to about 484,000 µm². The small pre-layout allowance
was optimistic. Supply connectivity is checked, while power-grid qualification
and the mixed-temperature fast corner remain open.

Keep the current capacity rule and UART schedule. Two logical reads preserve
consecutive branches and require no duration restriction. The unrestricted
flip-flop chip remains the proved reference. No experimental backend is promoted.
The historical one-port command-split core's routed result does not transfer to
the result-enabled chip or its concentrated package pins.

## Integrated concepts

The shared cleanup separates upload encoding (`Loader.ProgramImage`), storage
admission, compiler certificates and netlist composition. Input maps change
interpretation; feeders own transport/input state; observers own retained output
state without changing the core transition. The result mailbox exposes all
16 capture bits, outcome, consumption, overflow and sticky rejection.

The hybrid proof now composes these existing owners. `Memory.Sram` describes
replicated arrays and held Q; `SramController` owns the expressions used by the
emitter; `SramCoverage` establishes initialized dictionary words; `SramContents`
identifies those words with the uploaded loader image. `SramExecution` connects
actual array responses, lookup addresses and commit/start bypass to the existing
two-port execution invariant. Every controller register follows the shared
netlist, and one initializing edge establishes equality of all subsequent
observations with the capacity-adapted atomic reference. Initial arrays and Q
may be arbitrary; SRAM is not cleared on reset. The backend image retained in
the proof is specification bookkeeping, not execution's source of successor
words.

The [closed-loop model proof](../storage-primitives.md#closed-loop-hybrid-execution-2026-09-21)
therefore closes the initialized-words-to-execution gap. External Verilog macro
binding, package-wrapper composition and actual emitted-chip read-back remain
separate obligations. Direct SRAM does not inherit the hybrid proof. The four
experimental MLIR and RTL emissions remain byte-identical.

The [host workflow](../host-workflow.md) uploads and runs UART TX/RX, SPI mode 0,
a stretched I²C read and a custom captured-input trigger on one unchanged RTL
chip. The client and peers use package pins only. It tests nondestructive result
reads, consumption and malformed-upload recovery. The September 19 demonstrations
passed nine cases, 855,975 edges and 2,925 serial frames on both hybrid and FF
reference implementations. That phase's RTL/generic-gate regressions passed
508,252 two-port edges and 436,800 admitted one-port edges, with 6,580/6,575
proven equivalence points and corrupted-result rejection. Later checks are
recorded below with their separate scopes.

A full upload takes 94,629 chip edges (1.89258 ms at the assumed 20 ns period),
while the TX example executes for 40 edges. This supports evaluating a resident
program with variable payload data before adding protocols or a general FIFO.
It does not measure host software wall time, board throughput or a supported
physical clock rate. The bounded [resident-payload proposal](../host-workflow.md#bounded-resident-payload-proposal-2026-09-19)
uses the data word already carried by START and one shift on instruction entry.
It remains unimplemented in the default chip; the experimental paired controller
now implements and checks resident payload behavior. Continuous RX supervision
remains a separate Lean model.

## Evidence and boundaries

| Layer | Established | Remaining |
| --- | --- | --- |
| Protocols/compilers | UART, SPI, I²C correspondence, storage certificates and digital input-latency contracts | Selected physical rates, electrical and board assumptions |
| Memory/fetch | Generic policies and admission; initialized hybrid array/controller trace refinement with uploaded-word correspondence, actual lookup/Q and commit/start ownership; every controller register matches the shared netlist; typed assembly, thirteen edge obligations and artifact-bound computational map | External macro behavior binding, full package-wrapper/emitted-chip composition; direct request/expansion proof |
| Chip artifact | Independent serial/core/mailbox oracle and corruption controls; exact paired macro/state intake, both mapped-corner output/next-state SAT checks, and typical mapped package replay | Full Lean binding of emitted behavior, external macro assumptions and package traces; final physical netlist regression |
| Host | Public transport/client interface, reusable E64 JSON, interactive protocol and custom-program demonstration; experimental paired resident payload checked at RTL/mapped pins | Board transport, paired 290-word upload integration and continuous supervisor composition |
| Physical | Chip-specific SDC, official 6×4 DEF, pinned macro views, power connections, frozen inputs and bounded routing attempts; repaired netlist passes the full pin oracle | Routing, extracted multi-corner setup/hold/electrical closure, required layout checks, power-grid qualification and final layout-netlist regression |
| Packaging | Reproduction paths and documented evidence boundaries | Root license remains pending by user decision; final template package and publication |

The earlier foundation gate passed all 31 suites in 1,476.691 s. Its build and
audit covered 197 modules, 14,217 declarations and 7,313 theorems using standard
axioms only; counts include generated declarations. The audit rejected an early
native bit-vector proof dependency; the corrected proof uses ordinary bank
separation and arithmetic, with no change to the allowed axioms. The Python
suite then passed 105 tests with two platform skips.

The earlier SRAM comparison passed all three chips at RTL and both mapped
corners: 508,252 external-pin edges per simulation, plus 11,840 core edges for
each SRAM including 1,000 consecutive branches and both negative controls.
All 220 captured comparison sources and 266 foundation sources matched that
validated checkout. The half-corridor post-CTS netlist, inherited by its
global-routing state, also passed 508,252 pin edges and compiled
output-corruption rejection. That explicitly identified netlist is not an
export of the later routing database. Exact receipts and boundaries are in
the journal and physical manifest.

The earlier map-tile increment builds the library and emitters, audits 14,526
declarations / 7,421 theorems with standard axioms only, and passes `Interfaces`
and 36 focused Python tests. Exact regenerated MLIR/RTL equality binds typed
bank/word coordinates and computational probes to the earlier mapped/simulated comparison. The full
31-suite regression and RTL simulations were not rerun for unchanged hardware.
Slice membership, boundary signatures, counts and retained Liberty areas match
independent Verilog read-back; areas sum to the original complete standard-cell
cost. The [slice receipt](../../physical/experiments/map-slice-results.json)
records the earlier census. The new [tile receipt](../../physical/experiments/map-tile-results.json)
records nine arbitrary-state output/next-state SAT checks, mapped-Verilog
read-back and a rejected joined-reader control. The complete-chip receipt adds
actual package/macro terminal checks and equivalence of outputs and surviving
state with arbitrary reference inputs; both mapped versions discard the same
six unused cached-word bits. This remains distinct from a full Lean theorem
for the external macro model and package trace. The earlier organization receipt
and 2.810 s read-only OpenDB export remain preserved; no physical tools ran.

## Next discriminators

1. **Screen area-neutral data organization under the measured environment.**
   The [diagnosis](../../physical/experiments/paired-coupling-results.json) identifies
   shared-control wire/load growth as the dominant mode/status regression. Extend
   the next candidate's declared scope by its six control branches (**1,152**
   total before further edits), retaining four exact timing paths and thirteen
   clock nets. Compare complete control and serial-bit-49/50/51 grouping choices,
   including passing siblings and both incident sides. Keep original timing
   floors, 20% reserve and cumulative area reference; only **0.7678 µm²** remains.
2. **Establish a supported clock-delivery constraint before physical execution.**
   SRAM launch delay and input capture delay are distinct measured losses.
   Inspect the pinned interface's ability to preserve or constrain their routes;
   identical stored rule names are insufficient. A proposed recipe must identify
   which measured paths it protects and then verify its actual effect. All 33
   current markers reconcile, with other signal traffic on every edge. No current
   hotspot directly contains a stored NDR-bound net, so clock-rule relaxation is
   not established as a capacity repair. Keep independent native capacity and
   global electrical gates. The older 22-marker / 21-grid discrepancy remains
   artifact-specific; detailed routing stays unadmitted.
3. **Bind the selected model to the complete emitted chip.** Existing hybrid
   uploaded-word/response/execution theorems do not automatically apply to the
   paired controller. Its conditional dispatch lemmas, finite model/RTL traces
   and mapped SAT checks leave compiler, admission and complete package trace
   refinement open. Make the external macro assumptions explicit and compose
   actual reads, captures, immediate starts, branches and atomic replacement.
   The upload pipeline has its own memory-view obligation. Keep host integration
   of the new image format separate from backend promotion; physical evidence
   determines which organization merits that investment.
4. **Close the final artifact and submission gates.** Validate the implemented
   chip netlist, complete translation/equivalence boundaries and required physical
   checks, then prepare the pinned Tiny Tapeout package. Licensing stays pending;
   publication/submission remain separate actions.

This sequence follows the [organizers' guidance](https://blog.janestreet.com/protocol-emulator-asic-competition/),
rechecked September 19: general programmability, verification and early routed
evidence. The physical experiments guide further adapter investment while its
implementation cost remains uncertain. Routing searches remain bounded.

## Stable constraints and deferred work

<a id="the-official-outline-2026-09-18"></a>

The current allocation is 6×4. Its official rectangle is 1,289.28 × 710.64 µm,
with 43 Metal4 pins near the top-left corner. Historical core runs used that die
area but spread their stand-in ports around the edge; the new chip flow uses the
actual template. The previous two-port core timeout is not an impossibility
proof or a universal utilization cutoff.

Both-synchronous indexed storage requires another latency contract and remains
deferred. One-port UART changes, alternative gating and broad ISA expansion are
not the next experiment. The specified resident-payload workload also awaits an
instruction/hardware budget against measured headroom. Keep digital sampling
limits explicit: SPI requires
`d + tco ≤ halfCycles`; I²C requires `d ≤ phaseCycles` and `d < waitCycles` under
the tested contracts. A digital two-edge delay is not an analog detection bound.
