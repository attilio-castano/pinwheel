# Physical targets and the paired implementation comparison

Study dated **2026-09-22**, with follow-ups **2026-09-23**. The latest
[whole-chip comparison](#shared-physical-edits-and-whole-chip-requalification)
completes the shared edit abstraction and independent admission, but **rejects
physical qualification**. All six targets of the preceding local repair retain
20% reserve. Elsewhere, three covered nets fail and one misses the reserve;
another shared control net fails outside the 1,146-connection inventory.
Slow setup becomes **−0.055813 ns**; fast hold is positive at **+0.064551 ns**
but below its retained floor. Global capacitance counts are four per corner,
with twelve slow-corner slew violations. Reported overflow rises **22 → 33**.

The new **33 native markers, flow units and saved-grid overflow agree**, all
on Metal3. The previous 22-marker / 21-grid discrepancy remains unresolved for
that older artifact. Exact netlist, cell placement, power bindings, area and
minimum pin access survive; **121 tests**, six actual admission mutations and
ten absent-container checks pass. Area remains **359,371.6704 µm²**, cumulatively
**+0.299786%**. The subsequent [read-only diagnosis](#matched-clock-control-and-capacity-diagnosis)
now separates the mechanisms: mode/status loses **2.318 ns**, almost entirely
in data; SRAM/status loses **0.307 ns**, mostly in its launch clock; input hold
loses **39.835 ps** through capture-clock delay. The subsequent
[organization study](physical/physical-organization-study.md) completes a 4.112-second
saved-chip screen: twelve consumer swaps have no complete conditional pass, and
two proposed decoder copies exceed the remaining incremental area allowance.
Clock-environment replay still leaves both setup paths below their retained
floors. Next compare regional tree replacement and decoding with explicit
upstream, clock and area budgets; the original contract remains intact.
Detailed routing remains unadmitted.
[Research status](research/status.md) owns allocation.
The [initial](../physical/experiments/physical-target-results.json),
[repair](../physical/experiments/paired-closure-results.json) and
[coarse-route](../physical/experiments/paired-route-results.json) manifests bind
the preceding stages; the [reroute manifest](../physical/experiments/paired-reroute-results.json)
binds the source full route. The
[preparation manifest](../physical/experiments/paired-repair-plan-results.json)
binds the subsequent read-only diagnosis and unexecuted candidate.
The [signal-repair manifest](../physical/experiments/paired-signal-repair-results.json)
binds its execution and local qualification; the
[signal-route manifest](../physical/experiments/paired-signal-route-results.json)
binds the new whole-chip result. The
[distribution manifest](../physical/experiments/paired-distribution-results.json)
binds the subsequent measurements, contract and unexecuted plan.
The [distribution-repair manifest](../physical/experiments/paired-distribution-repair-results.json)
binds its local execution and independent qualification.
The [distribution-route manifest](../physical/experiments/paired-distribution-route-results.json)
binds the subsequent full-route failure and saved-path diagnosis.
The [path-repair manifest](../physical/experiments/paired-path-repair-results.json)
binds the expanded scope and locally qualified candidate.
The [path-route manifest](../physical/experiments/paired-path-route-results.json)
binds its admitted whole-chip route, surviving timing margins and remaining failures.
The [organization manifest](../physical/experiments/paired-organization-results.json)
binds the subsequent policy, saved-chip comparison and rejected combinations.
The [locality manifest](../physical/experiments/paired-locality-results.json)
binds the policy refinement, selected mixed plan and its local qualification.
The [locality-route manifest](../physical/experiments/paired-locality-route-results.json)
binds shared edit admission, the rejected whole-chip result and saved-path diagnosis.
The [coupling manifest](../physical/experiments/paired-coupling-results.json)
binds the subsequent matched paths, complete affected families and capacity diagnosis.

## One handoff with explicit ownership

The target is the connection between the validated abstract machine and its
physical implementation. It identifies the exact saved mapping, each SRAM
instance and view, power rails, placement exclusions, typed state owners and
four semantic timing roles. It does not introduce another hardware generator.

| Owner | Responsibility |
| --- | --- |
| `physical/targets/control.json`, `paired.json` | Bind an accepted mapping receipt, macro organization, placement and logical state roles. |
| `scripts/physical_target.py` | Adapt each existing validation format; resolve every physical FF and role to actual mapped pins; generate the platform configuration. |
| `physical/chip.json`, `chip.sdc` | Own the common package, clock, I/O and implementation assumptions. |
| `physical/targets/comparison-overrides.json` | Retain the control's eight-load implementation constraint. This file must accompany the comparison run. |
| Existing preparation, runner and collectors | Freeze artifacts, admit checkpoints, measure actual OpenDB geometry and perform independent timing and pin checks. |
| `physical/experiments/` and `build/` | Record decisions and immutable experimental receipts, respectively. |

This applies the earlier interface/platform separation lesson: the controller's
logical identities survive mapping as checked physical endpoints. The local
source adapters understand the old load-budget report and the new paired
controller report; the subsequent physical checks are shared. A future target
must provide its validation contract and ownership, not copy an entire flow.

All **2,895 control FFs** and **1,572 paired FFs** have exactly one typed state
owner. Timing roles are SRAM response → next SRAM address, SRAM response →
entry state, SRAM response → rejection status, and serial shift state → SRAM
upload data. Combinational reachability in the saved mapping predicts whether
each role has a path, and fresh STA must agree. The control has no SRAM →
rejection-status path; its result is explicitly absent. Missing a required path
still fails the gate. These are structural checks, not a new Lean theorem.

## Admission before cell placement

Preparation verifies the mapped Verilog/JSON and assembly against the accepted
report. It stages LEF, GDS, CDL, blackbox and timing views against the pinned PDK
inventory, and checks signal terminal widths/directions and all power pins.
The complete macro footprint must fit without overlapping another macro or
the reserved corridor.

Both new floorplan imports pass independent connection identity in a fresh
OpenDB export and the saved netlist. The paired macro then passes a separate
placement/PDN gate before standard-cell placement. Its 784.48 × 191.34 µm
footprint occupies **[252, 144, 1036.48, 335.34] µm**, keeping the former upper
SRAM's south-facing pin line. The **[252, 119.18, 1036.48, 144] µm** band below
it has neither placement rows nor cells. This is one explicit placement
hypothesis, not a floorplan optimum.

Actual OpenDB terminals bind `VDD!` and `VDDARRAY!` to `VPWR`, and `VSS!` to
`VGND`; package rails have the correct power/ground classification. Signal pin
geometry exists. These facts do not establish routed pin access, metal power
continuity, IR drop or shuttle power-grid qualification.

The first PDN readback stopped because its saved netlist included two explicit
power ports. The final checker projects only declared, isolated scalar power
ports after checking actual power nets separately. Logic loads, shorted rails,
unexpected bidirectional ports and changed signal connections still fail. The
earlier receipt remains intact; `--check-tag` permits fresh collection without
rerunning the physical step.

## Matched placement and repair

Both measurements use `OpenROAD.STAMidPNR-2`, immediately after clock
construction and post-CTS timing repair. The control reuses its saved
`mapped-local-place-01` checkpoint; a matching prepared target supplies its
roles only after checking identical mapping, libraries, package and SDC.

The paired pass takes about **26 seconds**, capped at 600 seconds with four
CPUs and 6 GiB. An earlier pass used the platform's fanout limit of ten; it is
preserved and excluded from the matched comparison. The comparison pass uses
eight, matching the control. Resolved configurations differ only in target
netlists/defines, macro organization/power bindings and the reserved band after
normalizing snapshot paths. Clock/I/O, placement and repair policy match.

| Measurement at the same stage | Control | Paired |
| --- | ---: | ---: |
| Total instance area, including macros and physical repair | 473,519.9456 µm² | 348,205.8528 µm² |
| Physical FFs | 2,895 | 1,572 |
| SRAM instances | 2 | 1 |
| Hold buffers | 2,986 | 1,678 |
| Clock buffers and dummy clock loads | 427 | 242 |
| Slow overall setup | +6.096080 ns | +0.304933 ns |
| Slow SRAM → next address | +6.096080 ns | +3.790690 ns |
| Slow SRAM → entry state | +9.042105 ns | +6.185663 ns |
| Slow SRAM → rejection status | No path | +0.304933 ns |
| Slow overall hold | +0.458213 ns | +0.405227 ns |
| Fast-screen overall hold | +0.099694 ns | +0.095552 ns |
| Clock fanout violations | 203 | 113 |
| Slow slew violations | 5 | 0 |
| Capacitance violations, every measured corner | 0 | 0 |

The saving is **125,314.0928 µm² / 26.464375%**. These are instance areas under
the same package allocation, not different die areas. All paired signal
fanout, slew and capacitance checks pass in the three measured corners; its
remaining fanout failures are clock nets. The 43-buffer control's later routed
measurements remain a separate reference, not the stage used in this table.

The limiting paired path starts at SRAM `A_DOUT[51]`, crosses shared parameter
and admission logic, and reaches `uo_out[4]`. Its reported arrival is
15.495067 ns against 15.800000 ns required. The path includes 0.738652 ns of
clock arrival and a 6.453160 ns SRAM clock-to-output arc. This directs the next
diagnosis toward clock distribution and the status/admission cone. A pipeline
change would need an explicit interface timing contract; a spare execution
cycle cannot be assumed.

These measurements use propagated clocks and **placement wire estimates**.
The control's 182 and candidate's 94 unannotated drivers have no consumers,
verified against actual connected terminals and disconnected output pins.
Both have zero partially unannotated drivers and zero consumed unannotated
nets. This qualifies the placement estimate, not a claim about routed RC.
The fast screen combines −40 °C cells and −55 °C SRAM; it is not a signoff corner.

## Initial comparison validation

The paired layout's fresh export passes **331,401 independent pin edges** and
rejects a compiled public-output corruption. Final export identity reuses that
trace without simulating again. The control's fresh export is also byte-identical
to its previously tested **508,252-edge** netlist, with unchanged vectors, bench
and models. This establishes the observed functional traces, not universal
equivalence or timing simulation.

**69 focused tests** pass. Five additional controls against the actual paired
OpenDB reject missing state ownership, a missing timing endpoint, wrong power
binding, changed macro location and an occupied corridor. All 27 exact run and
diagnostic containers are independently confirmed absent. The preceding paired
controller's 262 source/78 artifact hashes and paired model's 239 source/70
artifact hashes still match. No Lean or RTL source changed in this study.

This comparison admitted the clock and status investigation below. Its receipts
and the older control remain intact.

## Clock and status repair

The clock failures were leaf drivers with 10–17 sinks against the eight-load
limit. Setting `CTS_SINK_CLUSTERING_SIZE=7` in the
[clock overrides](../physical/experiments/paired-clock-overrides.json) clears
all 113 violations. The run resumes the verified macro/PDN state and stops at
the same post-CTS/hold-repair stage, capped at 600 seconds, four CPUs and 6 GiB.
After normalizing paths, clustering is the only change to the preceding paired
flow. The status setup margin barely changes, separating the clock and data
problems.

The data investigation first strengthens three consecutive buffers on the
worst SRAM-to-status path. With complete wire estimates this buys only
**0.008933 ns**: another branch becomes critical. The useful boundary is the
complete combinational distribution cone from SRAM outputs to `uo_out[4]`,
stopping at sequential and macro boundaries. The
[frozen selection](../physical/experiments/paired-status-cone.json) identifies
128 `buf_1` and 40 `buf_2` cells. The
[repair](../physical/experiments/paired-status-cone-repair.tcl) replaces those
168 cells with `buf_4`, legalizes them with all other instances fixed, then
restores placement statuses. Each repair probe is capped at 120 seconds,
two CPUs and 2 GiB; the selected probe takes about three seconds.

| Placement measurement | Initial paired | Clock repair | Clock and complete status-cone repair |
| --- | ---: | ---: | ---: |
| Total instance area | 348,205.8528 µm² | 352,863.4176 µm² | 354,010.1184 µm² |
| Slow overall setup | +0.304933 ns | +0.303624 ns | +1.089368 ns |
| Slow overall hold | +0.405227 ns | +0.418639 ns | +0.418639 ns |
| Fast-screen overall hold | +0.095552 ns | +0.099842 ns | +0.099842 ns |
| Clock fanout violations | 113 | 0 | 0 |

The final candidate has zero fanout, slew and capacitance violations in every
measured corner. Slow SRAM-to-address and SRAM-to-entry slacks are
**+4.680503 / +7.196474 ns**. SRAM `A_DOUT[20]` to rejection status is now the
limiting path, arriving at 14.710632 ns against 15.800000 ns required. The data
repair costs **0.325%** over the clock-repaired chip; both repairs cost
**1.667%** over the initial paired placement. The final instance area is
**25.238605% below** the old control's 473,519.9456 µm² at the same stage.
No pipeline cycle or package timing requirement changed.

Measurement policy is part of the evidence. The local optimizer initializes
explicit nominal layer RC from the pinned technology LEF. An initial attempt
to use that initialization for independent placement STA produced **308 partially
unannotated drivers** on both the unchanged control and three-cell repair.
Those margins are unqualified and preserved as diagnostics. Fresh independent
measurement of the final candidate uses the retained flow configuration and
has zero partially unannotated drivers and zero consumed unannotated nets in
all three corners. The collector records optimizer and measurement RC policies
separately. This diagnoses this pinned initialization path; it does not establish
that nominal RC is generally unsuitable. Propagated clocks and complete
placement estimates still do not establish routed or extracted timing.

The clock-repaired export passes **331,401 independent package pin edges** and
rejects a compiled output corruption. Independent Verilog readbacks then show
that contracting recognized noninverting buffers produces identical connectivity
before and after the 168-cell repair. This transfers the same zero-delay trace
evidence without another simulation. Actual-netlist inverter and rewired-input
controls are rejected. All other instance placements, every net terminal and
macro pin geometry match; the shared checker resolves all 1,572 FF owners,
four semantic timing roles, power bindings and the clear corridor.

**71 focused tests** pass and all **26 exact containers** are absent. The
preceding paired controller's 262 source/78 artifact hashes and paired model's
239 source/70 artifact hashes remain unchanged. The repair receipt freezes the
new collector interfaces, recipes and selected database; earlier receipts are
preserved. No Lean or RTL changes were needed for this physical repair.

The selected placed database is
`build/physical/repair-probes/paired-status-cone-01/repaired.odb`; its fresh
measurement is `build/physical/mapped-diagnostics/paired-status-cone-01/report.json`.
That database, with its parent state and repair receipt, supplies the bounded
coarse-routing diagnostic below. Detailed routing, antenna closure, extracted
timing, final power qualification and promotion of the experimental upload
format remain separate gates.

## Bounded coarse route

`paired-route-01` runs only `OpenROAD.GlobalRouting`, with a 600-second cap,
four CPUs and 6 GiB. The stage completes in **36.283 seconds**. Its intake
rechecks the passed placement measurements, exact parent/probe/database chain,
independent readback buffer identity and original pin-oracle inputs. The
continuation carries only the repaired ODB and empty metrics. CTS, placement,
signal/hold repair and antenna repair are disabled.

The comparison reuses the 43-buffer control's `local-slew-route-01` result.
Normalized configurations differ only in netlist/defines, macro organization,
power bindings and placement obstructions. Both use the same 20 ns clock,
eight-load policy, seven-sink clock clusters, Metal2–4 routing limits, 30%
capacity adjustment and explicit nominal layer RC. This compares complete
organizations and placements; it does not isolate the effect of buffer sizing.

| Coarse-route measurement | Retained 43-buffer control | Paired |
| --- | ---: | ---: |
| Total overflow | 1,310 | **41** |
| Routing resource | 452,959 | 425,596 |
| Routing demand | 147,062 | 191,854 |
| Overall reported usage | 32.47% | 45.08% |
| Instance area | 484,422.6752 µm² | **354,010.1184 µm²** |
| Slow overall setup | +5.339320 ns | **−2.493735 ns** |
| Slow overall hold | +0.336383 ns | **−0.491156 ns** |
| Fast-screen overall hold | +0.060261 ns | **−0.659543 ns** |
| Slow slew violations | 22 | 316 |
| Slow capacitance violations | 1 | 68 |
| Fanout violations in measured corners | 0 | 0 |

Overflow falls **96.870229%**, leaving 40 units on Metal3 and one on Metal4.
These are excess routing demand counts, not detailed-routing DRC markers.
Higher total demand and lower local overflow coexist: total wire use alone
does not describe the localized congestion. Paired area stays exactly equal to
its placed source and is **26.92% below this routed control**; the earlier
25.24% saving uses the control's post-CTS placement stage instead.

Fresh independent collection takes **12.109 seconds**, verifies actual nominal
layer RC in all three corners, and finds zero partially unannotated drivers and
zero consumed unannotated nets. The earlier placed measurement used the retained
flow configuration, so the timing difference also crosses an RC-policy boundary;
it cannot be attributed solely to longer wires. These remain coarse estimates,
not extraction or matched-temperature signoff.

The separate **2.348-second** minimum-one-access-point probe reports zero
standard-cell pins without access across 32,942 checked pins and zero macro pins
without access; 348 macro planar access points are valid. It uses the exact
settled route database and resolved routing layers, capped at 180 seconds with
four CPUs and 6 GiB. Individual pin access does not prove simultaneous legal
routing. The saved guide/body screen also records 67 Metal4 rectangles on 32
nets overlapping the macro footprint; guide overlap is not a short or DRC.

The new failure boundaries are concrete:

- **Status setup:** `memory.storage/A_DOUT[53]` → `uo_out[4]` arrives at
  18.293736 ns against 15.800000 ns required. Two loaded logic drivers are
  `_05608_/Y` (`nand3_1`, two sinks, 0.226882 pF, 2.200929 ns cell delay) and
  `_06399_/X` (`a21o_1`, three sinks, 0.283454 pF, 1.218126 ns). The SRAM-to-address
  and SRAM-to-entry roles retain +0.913580 and +4.982161 ns slow slack.
- **Hold:** the worst fast path is `uio_in[1]` → `_12267_/D`, owned by
  `r_pin_first_incoming[1]`. Its data arrives at 0.737588 ns against 1.397131 ns
  required. The register-clock trunk to `clkbuf_3_2_0_clk_regs/A` contributes
  0.632916 ns wire delay despite passing fanout/electrical limits. There are
  36 input-to-register and 55 register-to-register fast hold failures, including
  serial-shift paths. SRAM upload hold remains +0.200687 ns in that screen.
- **Signal distribution:** all electrical violations are on signal nets. Slow
  slew failures cover 58 distinct nets; capacitance failures cover 68, with
  **96 distinct nets in their union**. Fast and typical capacitance counts are
  70 and 69. Repair should account for these physical loads even when fanout
  is below eight.

The fresh netlist is byte-identical to the validated repair. Every context
field except database path/hash is identical, including cells, placement,
clock connections, macro pins, power shapes and the clear corridor. The 331,401
pin-edge trace and corruption rejection therefore transfer without another
simulation. All 1,572 FFs and four timing roles still resolve. **79 focused
tests** pass, all **six exact containers** are independently absent, and 321
prior source/result identities remain unchanged. The route-intake helper is the
one intentionally extended source from the previous closure receipt; that
receipt and its executed artifacts remain intact.

Retain this routed checkpoint for bounded clock/data-distribution and hold
repair. Investigate the register-clock trunk and input/serial hold paths, then
the loaded logic in the status cone and remaining signal electrical groups.
Any repair must use complete wire estimates, retain functional identity and
remeasure setup/hold/electrical limits before another routing experiment. The
41 remaining overflow units also need reconciliation before detailed routing.

## Local repair with coarse wire estimates

The September 23 follow-up retains **`paired-local-status-01`** as the local
repair candidate. Incremental coarse routing refreshes wires after each edit;
independent export and three-corner STA then check the saved database with the
same explicit nominal layer RC. Every original cell, placement, macro shape,
power shape and reserved corridor is retained. Only noninverting buffers and
their connections are added; the 1,572 FFs and execution schedule are unchanged.

| Measurement | Saved coarse-route baseline | Selected local repair |
| --- | ---: | ---: |
| Slow setup | −2.493735 ns | **+0.071044 ns** |
| Fast-screen hold | −0.659543 ns | **+0.072689 ns** |
| Slow hold | −0.491156 ns | **+0.360733 ns** |
| Fast hold failures | 91 | **0** |
| Slow slew / capacitance failures | 316 / 68 | **0 / 0** |
| Instance area | 354,010.1184 µm² | **357,660.6912 µm²** |

All three measured corners pass setup, hold, fanout, slew and capacitance checks
with complete consumed-net wire annotation. Typical setup/hold are
+5.873979/+0.176697 ns. Slow SRAM-to-address and SRAM-to-entry margins are
+3.312355/+6.229340 ns. The fast SRAM-upload hold role is +0.072689 ns.
Added area is **1.03120%**; the candidate remains **26.17% smaller** than the
retained routed control. Setup and fast hold margins are narrow, not signoff.

The experiments separate three mechanisms:

1. Four clock repeaters divide the long eight-load register trunk into four
   spatial pairs. This alone reduces fast hold failures from 91 to 12 and the
   worst deficit from −0.659543 to −0.077746 ns. Slow and typical hold pass,
   while status setup is unchanged. Earlier register clocks also expose SRAM
   upload hold failures: clock latency must be checked at both ends of a path.
2. Strong local buffers isolate small signal drivers from long wires. The
   first 99 address the 98-net union of all-corner electrical failures and one
   additional critical status net. Further measured status branches bring the
   total to **111 signal-driver buffers**. A 100-path near-critical status
   audit identifies the final two shared drivers; it is a bounded sample, not
   exhaustive path enumeration.
3. **126 small buffers** add delay at short-path endpoints, and **one strong
   receiver-side buffer** repairs SRAM input slew. These change physical delay,
   not pipeline cycles. Faster signal distribution can create hold failures,
   so both minimum and maximum delay are rechecked after each repair.

The final **242 added buffers** comprise those three groups plus the four clock
repeaters. Independent Yosys readback and buffer contraction establish unchanged
logical connectivity; a deliberately corrupted buffer input is rejected. All
original cell locations and types are identical, macro-pin geometry is unchanged,
and every added cell has both power terminals bound. This transfers the earlier
331,401-edge functional trace through the buffer identity check; no new pin
simulation is claimed. **25 focused tests** pass and **514 prior source/evidence
identities** are preserved. All **36 exact containers** are independently absent.

Each repair probe is capped at 120 seconds, two CPUs and 2 GiB; successful
candidate recipes take about four seconds, followed by roughly twelve seconds
for independent collection. The first resizer insertion attempt hits an OpenROAD
DPL assertion and produces no selected candidate. Direct database insertion
followed by normal legalization succeeds; the failed receipt remains intact.
An initially overstrict guide-byte check is also retained: a nearby replacement
driver can correctly reuse the same coarse guide block. The corrected check
requires guide coverage, complete fresh RC and independent connection identity.

The [local-repair manifest](../physical/experiments/paired-local-repair-results.json)
binds every candidate, measurement, readback, recipe and the selected ODB.
This closes the measured local timing/electrical investigation. It does **not**
transfer the baseline's 41 overflow units or pin-access pass to the edited chip.
The whole-chip follow-up below completes that gate with a distinct intake for
added buffers and changed clock topology. Its fresh measurements replace the
local estimates for the current decision. Detailed routing remains unadmitted.
Extracted timing, antenna/DRC closure, physical power qualification and matched
cell/SRAM temperature corners remain open.

## Whole-chip reroute of local repair

`paired-reroute-01` completes one full GlobalRouting step in **58.116 seconds**,
under a 600-second, four-CPU, 6 GiB cap. It consumes the exact selected local
repair with empty inherited metrics. All automatic repair is disabled; the
netlist, cells, placement and clock connectivity remain unchanged. Independent
three-corner collection takes **12.353 seconds** and verifies complete consumed-net
wire estimates and actual nominal layer RC.

| Measurement | Local incremental estimate | Full coarse reroute |
| --- | ---: | ---: |
| Slow setup | +0.071044 ns | **+0.430335 ns** |
| Fast-screen hold | +0.072689 ns | **+0.081790 ns** |
| Slow hold | +0.360733 ns | **+0.347819 ns** |
| Slow slew / capacitance failures | 0 / 0 | **80 / 16** |
| Instance area | 357,660.6912 µm² | **357,660.6912 µm²** |

Setup, hold and fanout pass in all three measured corners. Typical setup/hold
are +6.205010/+0.169243 ns. Slow SRAM-to-address and SRAM-to-entry margins are
+3.504518/+6.586933 ns; fast SRAM-upload hold is +0.164731 ns. These are coarse
wire estimates, not extraction. The fast screen still mixes −40 C standard
cells with −55 C SRAM.

The full reroute exposes electrical failures that the local estimate did not.
Fast/typical slew counts are 4/5 and capacitance counts are 19/19. Across all
corners, the failing pins belong to **27 distinct signal nets**; no clock net
fails an electrical limit. Fresh reports and actual connectivity identify:

- **21 distribution nets with eight loads each.** The worst fast capacitance
  is 0.386423 pF against a 0.300000 pF limit at `_08772_/X`. Slow slew includes
  80 failing pins on 14 nets, so pin counts must not be treated as independent
  repair groups.
- **Six SRAM write-input nets**, feeding `A_DIN[10,15,17,19,21,52]`. Four already
  have strong `buf_8` drivers; two retain delay cells needed for hold. The worst
  fast input slew is 0.734179 ns against a 0.380000 ns limit at `A_DIN[15]`.
  Repair must consider the receiver and wire geometry as well as driver strength,
  and must preserve minimum-delay timing.

Relative to the pre-repair full route, overflow falls **41 → 22 (46.34%)**.
All 22 units are on Metal3; Metal4 falls from one to zero. Total coarse demand
falls 191,854 → 186,936 with the same 425,596 resource count. The router reports
that it **disabled the nondefault routing rule on `clk` to reduce congestion**;
the baseline has no such warning. Clock connectivity is unchanged, but wire
policy is not identical, and this experiment does not isolate that rule's
contribution to the gains. Overflow is excess coarse demand, not detailed DRC.

The independent **2.360-second** pin-access screen passes: none of 33,426
standard-cell pins lacks access, no macro pin lacks access, and 348 macro planar
access points are valid. This does not prove simultaneous legal routing.
The guide/body screen finds 68 Metal4 rectangles on 33 nets overlapping the
macro footprint; these overlaps are not DRC violations.

The new schema-4 intake checks the 242 added buffers, original placement and
power bindings, complete positive local measurements and fresh independent
Verilog readback. It recomputes identity through the prior 168 buffer resizes
to the original 331,401-edge pin oracle. The routed export is byte-identical
to the local candidate, so that functional evidence transfers without another
simulation. **49 focused tests** pass, **528 prior source/evidence identities**
remain intact, and all **six exact containers** are independently absent.
The [reroute manifest](../physical/experiments/paired-reroute-results.json)
binds the selection, admission, source/export identities, diagnostics and analysis.

**Decision:** retain the timing and area gains. The preparation below resolves
connection ownership and locates the 22 Metal3 overflow units before a bounded
local repair. Require fresh whole-chip qualification after any repair. Detailed
routing, antenna closure, extracted timing and physical power qualification
remain open.

## Connection diagnosis and checked repair plan

The next September 23 study reads the settled local and whole-route databases;
it executes no repair, placement or routing. Fresh three-corner measurements
reproduce both earlier global reports exactly, with complete consumed-net
annotation, propagated clocks and verified nominal layer RC. Successful geometry
and STA collection takes **20.684 seconds**, with each command capped at
120 seconds, two CPUs and 2 GiB.

`physical_connections.py` follows the actual connections back to typed state
and forward to every state, SRAM or package boundary. It preserves shared
consumers instead of assigning shared combinational logic to one inferred block.
The resulting records include all physical terminals, pin geometry, library
limits, load ranges, minimum/maximum path summaries and retained delay cells.
The four existing semantic path roles remain intact; the 21 distribution nets
need these more specific owner records because they fall outside those roles.

| Family | Nets | Full/local estimated wire-capacitance ratio | Prepared operation |
| --- | ---: | ---: | --- |
| Mode control from `r_mode` | 1 | 1.057× | Isolate the existing driver with a strong buffer |
| Serial data from `r_serial_shift` | 9 | 1.034–3.037× | Isolate each existing driver; retain all shared consumers |
| Parameter-word control | 11 | 1.114–3.522× | Buffer each measured control branch |
| SRAM write inputs, bits 10/15/17/19/21/52 | 6 | 1.196–3.024× | Add a buffer near each SRAM receiver, retaining hold cells |

Pin capacitance, consumer sets, netlist, placement and terminal geometry are
unchanged. Estimated wire capacitance rises on every selected net. For example,
`_04700_` rises from 0.079309 to 0.279310 pF in the fast screen. SRAM `A_DIN[15]`
has 0.075497 → 0.228279 pF wire capacitance, and its input slew worsens from
0.067867 to 0.734179 ns against a 0.380000 ns limit despite an existing `buf_8`
driver. The six SRAM nets pass driver capacitance limits; their remaining
problem is receiver slew. On `net1897`, the serial-register consumer must also
be retained: only the SRAM receiver moves onto the added buffer's output.

These observations support different driver and receiver repairs, but do not
isolate the cause of each wire change. Both saved databases retain the same
nine nondefault-rule bindings, including `clk → CTS_NDR_0`. The whole-route log
nevertheless reports disabling that rule during routing. A stored binding is
therefore insufficient evidence of the effective router policy. Future
comparisons retain the binding map and runtime warnings separately.

The saved capacity/usage grid independently matches the reported **22 overflow
units**, one in each of 22 Metal3 grid cells. **Seventeen lie north of SRAM**;
the other five form a column at x=259.2 µm. One cell overlaps the macro and one
the reserved corridor. Only **seven** overlap coarse guides of the 27 failing
nets; the other **15** require separate traffic diagnosis. The coordinate and
guide-candidate lists are in the ignored local artifact
`build/validation/paired-repair-plan-01/congestion.json`, identified by the
tracked [preparation manifest](../physical/experiments/paired-repair-plan-results.json).
Guide overlap does not assign blame to a net or establish detailed DRC. Saved
grid totals include capacity reductions in usage and are not free-track counts.

The durable [repair plan](../physical/experiments/paired-signal-repair-plan.json)
describes **21 driver and six receiver buffers** using `sg13cmos5l_buf_8`.
`physical_repair_plan.py` validates its exact checkpoint, drivers, complete
consumer sets, routing policy, new names and unoccupied row rectangles before
generating Tcl. This replaces recipe duplication for this repair family while
leaving historical recipes unchanged. The generated candidate also checks
consumer sets before editing and fixes original cells during legalization.
All existing cells, hold chains, clocks, state and cycle boundaries are retained.
Added cell-footprint area is **636.8544 µm² (0.178061%)**. The rectangles are
placement hints; site alignment, legalization, power binding, pin access and
timing have not been established for the candidate.

This applies the [interface and timing-contract lessons](engine/timed-components.md#sources-and-next-application)
and the [separation of hardware allocation from scheduling](physical/chip-architecture-study.md#the-structural-next-step):
one checked description connects semantic owners to concrete pins and defines
the obligations a physical implementation must retain. These Python checks are
not Lean proofs of placement, routing or timing.

**35 focused tests** pass, including malformed ownership, shared consumers,
stale checkpoints, missing measurements, invalid repairs and relaxed acceptance
gates. The recipe regenerates byte-for-byte and passes a Tcl completeness check;
it was not executed. All six diagnostic containers are independently absent.
The first two read-only collectors encountered pinned OpenDB binding mismatches;
their failed receipts and source versions remain preserved. **595 prior source
and evidence identities** remain unchanged, with five documentation pages
updated separately. The
[preparation manifest](../physical/experiments/paired-repair-plan-results.json)
binds all evidence and records physical closure as false.

The bounded probe below completes this planned local gate: independent netlist
readback, placement/power checks and all three timing/electrical corners, covering
new branches and adjacent paths with complete estimates. The recorded congestion
locations still require separate traffic accounting and a fresh whole-chip route
before detailed routing. Coarse timing and the fast cell/SRAM temperature mismatch
remain explicit limitations.

## Bounded probe of the checked signal plan

The next September 23 follow-up executes that exact plan once as
**`paired-signal-repair-01`**, starting from the settled full-route checkpoint.
The source design and PDK are mounted read-only. The candidate uses the shared
generator's 21 driver buffers and six SRAM receiver buffers, followed by
legalization of only the added cells and incremental coarse-wire updates.
Execution completes in **6.005 seconds**, within the 120-second/two-CPU/2 GiB cap.

Independent saved-ODB export, geometry and three-corner STA take **12.448 seconds**.
Separate reports for all **54 changed/new nets**, their pin geometry, and a
fresh OpenROAD placement check take **12.752 seconds**. Complete consumed-net
annotation, explicit nominal RC and propagated clocks pass throughout. The
per-connection collector exactly reproduces the independent global metrics.

| Measurement | Source full route | Local signal repair |
| --- | ---: | ---: |
| Slow setup | +0.430335 ns | **+0.527857 ns** |
| Fast-screen hold | +0.081790 ns | **+0.081790 ns** |
| Slow hold | +0.347819 ns | **+0.347819 ns** |
| Fast slew / capacitance failures | 4 / 19 | **0 / 0** |
| Slow slew / capacitance failures | 80 / 16 | **0 / 0** |
| Typical slew / capacitance failures | 5 / 19 | **0 / 0** |
| Instance area | 357,660.6912 µm² | **358,297.5456 µm²** |

All corners have zero setup, hold and fanout violations as well. Typical
setup/hold are +6.258440/+0.169243 ns. All 54 affected nets pass electrical limits
and both minimum/maximum path summaries in all three corners, giving 324
positive path summaries; global STA also checks adjacent paths. The fast
cell/SRAM temperature mismatch and narrow hold margin remain limitations.

The measured mechanisms match the plan. In the fast screen, the largest load
seen by an original distribution driver falls from **0.386423 to 0.012289 pF**:
the new strong buffer drives the long branch. At SRAM `A_DIN[15]`, receiver slew
falls **0.734179 → 0.019937 ns**, against a 0.38 ns limit. All six receiver slews
are 0.019449–0.026150 ns in that screen. Existing hold cells remain, and the six
new SRAM branches retain positive fast hold slack, at least **+0.273833 ns**.
The chip-wide minimum stays +0.081790 ns on another path.

Fresh Yosys readback checks the exact declared edit and buffer-contracted
connectivity; tying one new buffer input to zero is rejected. The full ancestry
is recomputed through the previous 168 buffer resizes and now 269 additions to
the original 331,401-edge pin oracle. No new pin simulation is required for
that logical identity argument. All original cells/types/locations, all **342
clock-net connections**, macro pins and the clear corridor remain unchanged.
Every new footprint fits a row without overlap; the independent OpenROAD
placement check passes and both power terminals of every new cell are bound.
Physical power continuity is a later qualification.

Guide comparison records **46 changed rectangle sets**, all on the 54 declared
connections. A further 2,297 raw guide blocks differ only by repeated rectangles;
they are not additional geometric changes. This comparison keeps every edited
net covered and relies on fresh complete RC, rather than guide bytes alone.
Stored nondefault-rule bindings are unchanged. The saved incremental grid has
zero overflow, but it does **not** replace the preceding full-route count of
22 Metal3 units or qualify the 15 source hotspots outside the failing-net guides.

The physical probe and diagnostic stages take **31.205 seconds** in total;
native readback takes another 0.865 seconds. All **eight exact containers** are
independently absent, **616 prior source/evidence identities** remain unchanged,
and five documentation pages are updated separately. The
[signal-repair manifest](../physical/experiments/paired-signal-repair-results.json)
binds the candidate, measurement and complete functional ancestry. The local
connection reports reside at
`build/validation/paired-signal-repair-01/connections.json`; this generated
artifact requires the matching local run or reproduction.

**Decision:** retain this locally qualified candidate. Bind its exact source and
complete ancestry through routing intake, account for the saved congestion
locations, then run one bounded whole-chip coarse route and fresh timing,
electrical, congestion and pin-access checks. The earlier local pass lost
electrical qualification after full routing, so that comparison remains
necessary. No new whole-chip route, detailed route, extracted timing or
backend promotion occurred in this probe.

## Whole-chip qualification of the signal repair

The September 23 follow-up **`paired-signal-route-01`** runs exactly one
`OpenROAD.GlobalRouting` step, with automatic design, timing and antenna repair
disabled. It finishes in **100.452 seconds**, within the 600-second/four-CPU/6 GiB
cap. Independent export/geometry/STA, pin access, saved-grid collection and
residual-net comparisons take another **35.555 seconds**. No second route or
further repair runs.

The shared intake now distinguishes the **27 new buffers** from **242 prior
additions** and **168 prior resizes**. Fresh native readback checks the original
oracle, repaired parent and candidate in 1.284 seconds, recomputing both full
ancestry and the immediate edit. Placement and power checks use the immediate
source. **41 focused tests** pass, including corrupted ancestors, mismatched
source exports, changed prior buffers and missing power bindings. The legacy
intake remains supported; the previous helper bytes and receipts are preserved.

| Measurement | Source full route | Local candidate | New full route |
| --- | ---: | ---: | ---: |
| Slow setup | +0.430335 ns | +0.527857 ns | **+0.408159 ns** |
| Fast-screen hold | +0.081790 ns | +0.081790 ns | **+0.088087 ns** |
| Slow hold | +0.347819 ns | +0.347819 ns | **+0.350921 ns** |
| Fast slew / capacitance failures | 4 / 19 | 0 / 0 | **0 / 13** |
| Slow slew / capacitance failures | 80 / 16 | 0 / 0 | **16 / 12** |
| Typical slew / capacitance failures | 5 / 19 | 0 / 0 | **0 / 12** |
| Full-route Metal3 overflow | 22 | Not requalified | **21** |

All corners retain zero setup, hold and fanout violations, complete consumed-net
annotation, explicit nominal RC and propagated clocks. Typical setup/hold are
+6.183450/+0.174788 ns. All **27 originally failing nets and all 54 changed/new
connections pass electrical limits** after routing. The exported netlist is
byte-identical to the local candidate; every context field except database
identity is unchanged. All placements, 342 clock nets, 1,572 FFs, macro/corridor
geometry and area are retained. The 331,401-edge oracle transfers through checked
identity; no pin simulation repeats. Minimum pin access finds zero inaccessible
standard-cell or macro pins. All **nine exact containers** are independently absent.

The **15 residual nets** comprise 14 eight-load branches driven by twelve `buf_1`
and two `nand2_1` cells, plus `net1889`, a hold-buffer output feeding SRAM
`A_DIN[51]`. None is one of the 54 edited connections. Saved local/full-route
comparisons find unchanged pin capacitance while wire capacitance rises
**1.025–2.682×**; wires make up **83.5–94.9%** of the new load. For example,
`_04363_` wire capacitance rises 0.097066 → 0.260303 pF, taking capacitance margin
from +0.158239 to −0.004998 pF. SRAM bit 51's slow slew becomes 0.605968 ns against
a 0.595200 ns limit. These measurements justify examining margins across the
serial/parameter distribution families; their ratio is not a universal bound.

Saved-grid and flow totals agree on **21 Metal3 overflow units**, each one unit.
Capacity arrays are unchanged. Only two locations persist: twenty old hotspots
clear and nineteen new ones appear. One remains at the macro edge at
(259.2, 144.0) µm, where the sole overlapping guide changes `_02961_` → `_01660_`.
None overlaps the corridor. Eleven hotspots include clock guides, and only five
include a currently failing net's guide. Guide association is not track-demand
attribution. The source accounting preserves all 258 associated nets, including
15 clock nets, with shared typed owners retained.

The router disables nondefault rules on **`clknet_0_clk_regs`, `delaynet_4_clk`,
and `clk`**, compared with only `clk` previously. All nine stored rule bindings
nevertheless remain unchanged. Fixed clock topology therefore does not imply
fixed effective routing policy. No isolated experiment attributes gains or
regressions to a particular rule relaxation.

The [signal-route manifest](../physical/experiments/paired-signal-route-results.json)
binds the run and separate timing/electrical/congestion verdicts. Collection
succeeds; electrical and congestion qualification do not. Coarse estimates, the
fast cell/SRAM temperature mismatch, detailed DRC, antenna checks, extracted
timing and physical power qualification remain separate limitations.

**Decision:** retain the demonstrated repairs. Inventory wire load and driver
margin across the serial/parameter distribution and SRAM-input families,
including currently passing neighbors. Use saved routes to select one bounded
local strengthening or segmentation plan with setup/hold, area and neighborhood
margin gates. Separate the persistent macro edge from migrating signal/clock
competition. Another full route requires a concrete qualified candidate;
detailed routing remains unadmitted. No RTL, pipeline, protocol, backend-default
or licensing change occurred.

## Measured distribution contract

The next September 23 study makes physical distribution a checked description
over an exact saved chip. `physical_distribution.py` discovers branching nets
from typed source/sink ownership, includes all 64 declared SRAM write inputs,
and closes the inventory over existing buffer and hold chains. The scope covers
serial data, serial control and parameter distribution. It retains shared family
memberships and all consumers; it does not claim exclusive physical partitions
or cover every signal family in the chip.

The result contains **1,067 connections in 211 trees**, including **124 existing
hold cells**. Read-only reports for both the local and full-route checkpoints
take **57.258 seconds** in total, under 120 seconds/two CPUs/2 GiB per command.
They produce 6,402 connection/corner records and 12,804 min/max path summaries.
Global metrics reproduce the prior independent measurements. Terminal geometry
and pin loads match; complete consumed-net annotation and nominal RC pass.
All **three exact diagnostic containers** are independently absent.

The contract records actual consumers and cell locations, buffer-tree roots,
per-corner capacitance and slew limits, remaining budgets, setup/hold summaries,
and the source checkpoints. The available trial wire-capacitance budget is the
chosen fraction of the driver's total limit minus its measured pin load. That
separates what the receiving pins consume from what the wires may consume.
Routing must revalidate the measurements. The observed 2.682× ratio is never
used as a universal load multiplier.

The headroom sensitivity is explicit:

| Proposed capacitance/slew reserve | Failing connections | Passing below reserve | Selected total |
| --- | ---: | ---: | ---: |
| 5% | 15 | 5 | 20 |
| 10% | 15 | 12 | 27 |
| 15% | 15 | 14 | 29 |
| **20% trial** | **15** | **18** | **33** |
| 25% | 15 | 19 | 34 |

The chosen 20% reserve is an experimental gate, not a library requirement or
a proven guard against another route. It selects **31 driver buffers and two
SRAM receiver buffers**, all `buf_8`. The receivers serve bits **50 and 51**.
Bit 50 currently passes, but its slow slew is 0.556960 ns against a 0.595200 ns
limit: only **6.42% headroom**. Two selected driver branches have six consumers,
so the inventory also avoids limiting diagnosis to the previously failing
eight-load pattern.

The shared checked generator produces this plan with a fresh namespace and
rejects collisions with earlier repairs. Unoccupied row hints account for all
33 proposed cells together. Predicted added instance area is **778.3776 µm²
(0.217243%)**, below the **1,074.8926 µm² (0.3%)** cap. This is a geometric cost,
not evidence of legal placement, power continuity or improved electrical behavior.

The [contract](../physical/experiments/paired-distribution-contract.json) requires
independent identity and original-cell/clock/hold retention, actual legal added
cells and power bindings, zero chip-wide electrical violations, and 20% cap/slew
reserve across the rebuilt inventory and every added branch. The expected check
set is **1,100 connections**, including 66 changed/new ones. Every corner must
retain at least 90% of its current setup and hold slack: slow setup at least
**+0.367343 ns**, fast-screen hold at least **+0.079278 ns**. These are proposed
acceptance floors, not measured candidate results. Whole-chip routing must later
requalify the result, including congestion and effective clock rules.

The separate congestion accounting finds inventory guides at **20 of 21** saved
hotspots and selected-target guides at only **five**. The persistent macro-edge
hotspot has neither. Its guide `_01660_` belongs to shared cached/mode/capture
logic outside this distribution scope. Guide association is not a cause or a
prediction that the buffer plan clears congestion.

**54 focused tests** cover family/chain coverage, passing siblings, missing
corners or consumers, reserve/budget gates, source identity, namespace collisions
and existing repair/intake checks. Recipe syntax passes without executing CAD.
The [distribution manifest](../physical/experiments/paired-distribution-results.json)
binds all evidence and the [33-buffer plan](../physical/experiments/paired-distribution-repair-plan.json).
No repair, route, RTL or pipeline change occurs in this preparation. The next
gate is one bounded local probe of this exact plan followed by the contract's
independent checks; detailed routing remains unadmitted.

## Local qualification of the distribution contract

The next September 23 experiment executes the saved **33-buffer plan once**
against `paired-signal-route-01`. The local probe completes in **5.658 s**;
independent export, geometry, whole-chip STA, complete inventory measurements
and placement checks add **41.223 s**, for **46.881 s** of physical commands.
Each command has a 120-second/two-CPU/2 GiB cap. All eight exact containers are
independently confirmed absent before final collection.

Fresh netlist readback confirms exactly **31 driver buffers and two SRAM input
buffers**, with no original cell resized or moved. All **342 clock-net
connections**, **1,682 chip-wide hold cells** (124 in the inventory), state and
macro/corridor geometry remain. The added cells pass independent placement and
power-terminal binding checks; legalization moves thirteen from the planning
hints, which were not placement guarantees. Instance area becomes
**359,075.9232 µm²**, adding **778.3776 µm² (0.217243%)** within the 0.3% cap.

The rebuilt inventory contains all **1,067 original plus 33 added connections**,
still in 211 logical trees and covering all 64 SRAM write inputs. It measures
**3,300 connection/corner records and 6,600 min/max path summaries**, including
all 66 changed/new connections. Every connection exceeds the saved 20% reserve:

| Corner | Minimum capacitance reserve | Minimum slew reserve | Whole-chip setup slack | Whole-chip hold slack |
| --- | ---: | ---: | ---: | ---: |
| Fast screen | 26.12% | 21.87% | +9.478370 ns | +0.088087 ns |
| Slow | 26.73% | 25.51% | +0.408159 ns | +0.350921 ns |
| Typical | 26.45% | 28.20% | +6.183450 ns | +0.174788 ns |

Whole-chip capacitance/slew/fanout and setup/hold violation counts are **zero**
in every corner. Worst setup and hold slack are identical to the source, so all
90%-retention floors pass. Complete consumed-net annotation, propagated clocks
and explicit nominal RC are independently reproduced. Every selected original
driver sees lower fast-corner load. SRAM inputs 50 and 51 improve from
**0.556960 / 0.605968 ns** to **0.062730 / 0.062341 ns** slow slew, against the
same 0.595200 ns limit. The tightest remaining margin is the unedited bit-14
input's **21.87% fast slew reserve**, only 1.87 percentage points above the
experimental target; another route must measure it again.

The quantitative checker in `physical_distribution_acceptance.py` requires
exact old-plus-new coverage, all declared corners, matching drivers/consumer
counts, electrical reserve, whole-chip timing floors and the area cap. It rejects
missing evidence and reports budget failure separately from collection success.
**61 focused tests** pass, including low-margin new branches, invalid values,
missing corners and independent area/timing/electrical failures. Independent
buffer contraction rejects a grounded new-buffer input and reconnects the
candidate to the original **331,401-edge** pin trace: 302 cumulative buffer
additions and 168 earlier resizes, with no new execution edge or state bit.

Guide rectangle sets change only within the declared edit (57 of 66 connections).
The local incremental grid reports zero overflow, but this does **not** replace
the source whole-chip result of **21 Metal3 units**. Nine stored clock-rule
bindings remain; absence of a new incremental warning does not demonstrate that
the source's three effective clock-rule relaxations have been reversed.

**Decision:** retain this locally qualified candidate. Diagnose persistent
macro-edge and migrating congestion from the saved full-route evidence, then
bind this exact candidate, its ancestry and distribution budgets through intake
before a bounded whole-chip route. That route must recheck the complete
inventory, timing/electrical budgets, congestion, effective clock rules and pin
access. No full route or detailed route was run here. Coarse estimates, fast
cell/SRAM temperature mismatch, extracted timing, physical power continuity and
complete compiler/package refinement retain their existing boundaries.

The [distribution-repair manifest](../physical/experiments/paired-distribution-repair-results.json)
binds all execution and validation receipts. All **1,183 initial identities**
remain unchanged before the five documentation updates; the planning receipt
and its historical `checked-plan-only` status remain immutable.

## Whole-chip requalification of the distribution contract

The September 23 follow-up **`paired-distribution-route-01`** completes one
GlobalRouting step in **62.633 s**, capped at 600 s, four CPUs and 6 GiB. It
uses the exact locally qualified 33-buffer candidate, with automatic repair
disabled and no new placement, sizing, clock topology or execution boundary.
Independent whole-chip checks take **12.711 s**, full inventory and saved-placement
checks **28.869 s**, and minimum pin access **2.393 s**. All fourteen exact
containers are independently absent. No second route or repair follows.

Before routing, `physical_distribution_route.py` recomputes the source inventory,
the selected plan and its local numerical acceptance. It checks the exact driver
and receiver edits against independent buffer contraction, and validates added
footprints. The existing intake retains all functional, geometry, power and
clock checks. **73 focused tests** pass, including attempts to skip the new
contract gate and stale congestion-marker controls. Three fresh native netlist
readbacks reconnect the candidate to the original **331,401-edge** oracle;
the routed export is byte-identical to the candidate. All 1,572 FFs, 342 clock
connections, cells, locations and **359,075.9232 µm²** area remain unchanged.

### Actual edge demand and marker freshness

Read-only diagnosis of the two earlier routes uses native OpenROAD congestion
markers alongside the saved grid and guides. The installed version stores
capacity reductions in **both** grid capacity and usage; the
[pinned exporter implementation](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/grt/src/fastroute/src/FastRoute.cpp#L1203-L1272)
explains why displayed capacity/usage of **17/18** can mean actual available
capacity/demand of **0/1**. That was the source route's blocked Metal3 edge at
**[259.2, 144, 266.4, 151.2] µm**. The earlier and source routes used different
nets there (`_02961_`, then `_01660_`), so persistence of the location did not
identify one faulty logical net.

The source has **213 actual crossing nets**, versus 235 guide-overlap
associations. `physical_congestion.py` reconciles every native marker with its
matching grid cell and flow total, retaining actual capacity, demand and named
crossings separately from guide overlap. A useful negative control finds that
the local candidate inherited the source's **21 marker records byte for byte**
despite its incremental grid reporting zero overflow. The checker rejects them
as stale; being inside the selected ODB does not establish freshness.

The fresh whole-chip result has **20 Metal3 overflow units**: twelve edges at
capacity/demand **10/11**, seven at **11/12**, and one at **3/4**. No overflowing
edge has zero capacity. The former blocked edge clears, but the new 3/4 edge
overlaps the macro's upper boundary at **[777.6, 331.2, 784.8, 338.4] µm**.
Only three hotspot locations persist; seventeen are new. Six hotspots have
actual clock crossings, six have repaired-family crossings, and the native
markers name **209 crossing nets**, versus 239 guide associations. These are
shared routing demands, not proof that a particular net caused congestion.
Aggregate **21 → 20** overflow is essentially unchanged.

Nine stored clock-rule bindings remain unchanged. At runtime the router relaxes
only `clk`, versus `clknet_0_clk_regs`, `delaynet_4_clk` and `clk` in the source.
That effective-policy difference is recorded; its contribution is not isolated.

### Which margins survive

All **66 changed/new connections** retain the fixed 20% cap/slew reserve.
Across all 1,100 connections, **1,091** meet it, **six** pass electrical limits
but miss reserve, and **three** violate capacitance in every measured corner:
`_03012_`, `_03116_` and `_03160_`. These three have unchanged consumers and pin
loads; full-route wire capacitance is about **2.11×, 1.99× and 2.73×** their
local estimates. The nine below-reserve connections are retained in the report,
including passing neighbors. These observed ratios are not reusable bounds.

Whole-chip STA also finds one slow slew failure on **SRAM `A_REN` / `net11`**:
**0.596672 ns** against **0.595200 ns**. The write-input distribution inventory
does not cover this read-enable control. Global checks therefore remain necessary.

| Corner | Setup slack | Hold slack | Saved hold floor | Cap / slew violations |
| --- | ---: | ---: | ---: | ---: |
| Fast screen | +9.347420 ns | +0.041429 ns | +0.079278 ns | 3 / 0 |
| Slow | −0.074067 ns | +0.290273 ns | +0.315829 ns | 3 / 1 |
| Typical | +5.890660 ns | +0.121309 ns | +0.157309 ns | 3 / 0 |

Slow setup misses zero and its **+0.367343 ns** floor. Hold remains positive,
but every retention floor fails. All 6,600 inventory min/max path summaries are
positive; the failing whole-chip output path is outside that inventory.
Consumed-net annotation is complete, with propagated clocks and verified nominal
RC. These remain coarse wire estimates; the fast cell/SRAM temperature mismatch
and absence of extracted timing remain explicit.

Saved paths make the next diagnosis concrete:

- **Status setup:** the worst output path changes from SRAM bit 51 to bit 53,
  both ending at `uo_out[4]`. An exact matching bit-53 path prefix in the old
  reports shows net `_02486_` (`_06301_/Y → _06302_/B1`) growing
  **0.068197 → 0.113368 pF**.
  Its gate delay grows **1.117685 → 1.732932 ns**, adding **0.615247 ns**.
  This one-receiver link is outside the branching-family inventory. The prefix
  comparison is valid; the differing worst output paths are not a same-path
  slack comparison.
- **Input hold:** `uio_in[1] → _12267_/D` retains identical path pins/edges and
  **0.737588 ns** fast data arrival. Capture-clock arrival grows
  **0.472345 → 0.519004 ns**, consuming almost exactly the lost hold margin.
  The same mechanism appears in the slow and typical reports. This localizes
  the timing budget; it does not establish which routing-policy change caused it.

**Decision:** preserve the local repair and reject full-route qualification.
Extend the watchlist to the status link, input capture-clock arrival, SRAM
control inputs and the nine distribution connections below reserve. Select a
bounded local repair only with explicit path, whole-family electrical, hold and
area gates. Analyze the twenty native congestion edges separately. Another
whole-chip route requires a newly qualified candidate; detailed routing,
antenna closure, extraction and physical power qualification remain open.

The [distribution-route manifest](../physical/experiments/paired-distribution-route-results.json)
binds the complete result. Of 1,316 initial source/evidence identities, 1,315
remain unchanged before documentation; the extended intake helper's original
bytes are archived. Two read-only API-inspection failures are preserved and
resolved using the installed OpenROAD bindings and native JSON export. They
are not routing failures or timeouts.

## Local qualification of path and control guards

The next September 23 experiment expands coverage before executing one repair.
The original distribution families remain complete. Nineteen explicit timed
connections add the status link, seven deficient input-hold endpoints, and all
eleven dynamic SRAM control/address inputs. Read-only classification also
accounts for 208 static non-data inputs and one clock input; all 64 write-data
inputs remain in the original family scope. The expanded source inventory has
**1,119 connections**. Besides read-enable's known slew failure, write-enable
has only **3.66%** slow slew reserve; it joins the candidate even though it passes
the library limit.

The shared plan compiler now accepts explicit buffer sizes and serial stages.
It validates exact source consumers, unused names, cell footprints, row space,
clock exclusion and the intended FF data endpoint for a hold guard. Its earlier
single-buffer schema and rendered recipes remain byte-identical. The checked
[plan](../physical/experiments/paired-path-repair-plan.json) declares:

- Nine `buf_4` driver buffers for the remaining distribution connections below
  reserve, plus one `buf_8` for the one-receiver status link.
- Two `buf_4` receiver buffers for SRAM `A_REN` and `A_WEN`.
- Two `buf_1` stages at each of seven input FF data endpoints, adding hold delay
  while retaining the clock tree and every existing hold cell.

These **19 operations / 26 buffers** add **284.8608 µm²**. Larger buffers at
every site would exceed the existing cumulative area cap. The
[path contract](../physical/experiments/paired-path-contract.json) retains the
original **358,297.5456 µm²** reference, **0.3%** area allowance, **20%** reserve
and every setup/hold floor. It does not reset the budget at each repair.

The exact recipe runs once in **5.739 s**. Independent whole-chip geometry/STA
takes **12.434 s**, and complete connection reports plus a separate placement
check take **30.897 s**. Including **12.134 s** of source diagnosis, physical
commands total **61.204 s**. Each command has a 120 s/two-CPU/2 GiB bound, uses
the pinned offline image, and terminates before settled artifacts are consumed.
All ten exact containers are independently absent.

| Coarse estimate | Source full route | Local path repair |
| --- | ---: | ---: |
| Slow setup | −0.074067 ns | +0.436742 ns |
| Fast-screen hold | +0.041429 ns | +0.093797 ns |
| Slow hold | +0.290273 ns | +0.439880 ns |
| Typical hold | +0.121309 ns | +0.208469 ns |
| Chip-wide capacitance failures, fast/slow/typical | 3 / 3 / 3 | 0 / 0 / 0 |
| Chip-wide slew failures, fast/slow/typical | 0 / 1 / 0 | 0 / 0 / 0 |
| Instance area | 359,075.9232 µm² | 359,360.7840 µm² |

All **1,145 connections**, including every intermediate chain branch, meet
reserve across **3,435 corner records / 6,870 min/max paths**. Minimum reserve
is **20.88% capacitance / 22.12% slew**; the closest capacitance margin is just
0.88 percentage points above the trial target. All saved timing floors pass.
Cumulative added area is **0.296747%**, leaving only **11.6542 µm²** under the
fixed cap. These narrow budgets must remain visible at whole-chip intake.

Matched saved paths show the intended mechanisms rather than just better global
numbers. Status-driver load drops **0.113368 → 0.009168 pF**; an identical bit-53
prefix through its predecessor accompanies a driver-hop delay reduction
**1.733107 → 0.317004 ns**. This hop includes the predecessor's wire delay.
The same status path reaches **+1.452227 ns** setup, so another path now sets the
whole-chip **+0.436742 ns** minimum. Slow read/write-enable slew falls
**0.596672 / 0.573418 → 0.073174 / 0.080670 ns**. Each guarded input gains
**82.4–88.6 ps** of fast data arrival delay; capture-clock arrival is identical
at every endpoint in every measured corner. The former worst endpoint's fast
hold rises **+0.041429 → +0.123537 ns**; a different input now sets the minimum.

Fresh native netlist readbacks verify exactly the planned edit, original
placements, all **342 clock connections** and **1,682 existing hold cells**.
Only 36 guide-rectangle sets change, all within the 45 declared changed/new
nets; clock guides remain unchanged. Added cells pass independent placement
and power-terminal checks. Buffer contraction transfers the retained
**331,401-edge** oracle through **328 cumulative added buffers** and 168 prior
resizes. Grounding a second hold stage is rejected. **74 focused tests** pass.
Declared input-hold roles are carried through the new buffers: an independent
metadata check preserves their source roles without changing measurement
selectors or rewriting the initial collected inventory.

**Decision:** retain the locally qualified candidate. Extend shared intake to
reconstruct this expanded path/control scope and every serial stage, preserving
complete ancestry and the original area/timing budgets. Only then allocate one
bounded whole-chip coarse route and remeasure all connections, global timing,
native congestion capacity/demand, effective clock rules and minimum pin access.
The local grid's zero count does not replace the source's **20 Metal3 overflow
units**. Nine stored clock rules remain; no new incremental warning establishes
a fresh whole-chip clock policy. Detailed routing, extracted timing and physical
power continuity remain separate gates. No RTL, state, pipeline, execution-edge,
default-backend or licensing change occurs here.

## Whole-chip requalification of path and control guards

The next September 23 study first extends shared intake in
`scripts/physical_path_contract.py`. It reconstructs the declared status link,
seven input-hold anchors, all eleven timed macro controls and complete
distribution families from the exact source. It independently checks the other
208 static macro inputs and one clock input. Declared roles propagate through
every new buffer stage, including branches already belonging to another family.
Raw measurements and the exact edit are rechecked against the original area
reference, 20% reserve and setup/hold floors. A later checkpoint cannot reset
the cumulative budget. **90 focused tests** pass, including omitted controls,
incorrect static classification, lost hold stages and weakened-budget rejections.

After that admission, **`paired-path-route-01`** executes exactly one full
GlobalRouting step in **92.059 s**, capped at 600 s/four CPUs/6 GiB. Cells and
placements remain fixed; automatic repair is disabled. Independent whole-chip
geometry/STA takes **13.371 s**, full connection/placement collection **31.520 s**,
and minimum pin access **2.515 s**. Fresh export is byte-identical to the local
candidate; all **342 clock connections**, **1,572 FFs**, power bindings and
placement geometry remain. The **331,401-edge** oracle transfers through the
same 328 cumulative buffers and 168 prior resizes. All eleven exact containers
are independently absent.

| Measure | Previous full route | Local 26-buffer repair | New full route |
| --- | ---: | ---: | ---: |
| Slow setup | −0.074067 ns | +0.436742 ns | **+0.420384 ns** |
| Fast-screen hold | +0.041429 ns | +0.093797 ns | **+0.101286 ns** |
| Slow hold | +0.290273 ns | +0.439880 ns | **+0.457194 ns** |
| Typical hold | +0.121309 ns | +0.208469 ns | **+0.221184 ns** |
| Global capacitance failures, fast/slow/typical | 3 / 3 / 3 | 0 / 0 / 0 | **2 / 2 / 2** |
| Global slew failures, fast/slow/typical | 0 / 1 / 0 | 0 / 0 / 0 | **0 / 9 / 0** |

Every original timing floor passes, and all **19 repaired source connections
plus 26 new branches** retain the required reserve. Whole-chip qualification
still fails: **1,139 of 1,145** connections meet reserve, four are below 20%,
and two violate a library limit. Every global electrical failure is now covered
by the inventory. Nine slow slew pin failures share `_03253_`; they are not nine
independent failing nets.

| Remaining connection | Physical role | Lowest routed reserve | Verdict |
| --- | --- | ---: | --- |
| `_02981_` | Serial bit-53 distribution | 19.12% capacitance | Below 20% |
| `_03253_` | Serial bit-53 distribution | −38.84% capacitance | Capacitance and slow slew fail |
| `_03380_` | Serial bit-53 distribution | 10.65% capacitance | Below 20% |
| `_04527_` | Parameter distribution | 2.53% capacitance | Below 20% |
| `_04701_` | Parameter distribution | −4.51% capacitance | Capacitance fails |
| `net31` | SRAM `A_DIN[14]` branch | 7.11% fast slew | Below 20% |

The five capacitance-sensitive drivers are existing `buf_1` cells with eight
consumers each. All 1,145 pin-load sets remain identical. On the two failing
nets, fast-corner wire capacitance grows **0.125184 → 0.322079 pF (2.57×)** and
**0.123089 → 0.262146 pF (2.13×)** from local to full routing. These measured
ratios diagnose this route; they do not establish a universal safety factor.
Local reserve alone has again failed to bound full-route wire redistribution.
The family-wide inventory is what exposes the newly vulnerable neighbors.

Area remains **359,360.7840 µm²**, leaving **11.6542 µm²** under the original
0.3% cumulative allowance. Even two additional `buf_1` cells cost **14.5152 µm²**.
The next decision therefore needs a costed redistribution or selective-sizing
comparison across the affected families, including upstream load and hold
effects; it cannot assume another additive repair fits the current budget.

Congestion has not improved: the final flow table reports **21 Metal3 + one
Metal4 overflow unit**, versus twenty Metal3 units before. The saved grid
contains only **21 Metal3** units. Native JSON contains **22 markers**; the
strict reconciler rejects complete coverage. Twenty-one markers match the grid,
while the horizontal marker at **(511.2, 352.8) µm**, with capacity/demand
**11/12**, does not. Its layer/location attribution remains unqualified; the
flow's Metal4 total alone does not resolve that mismatch. Only two of the 21
matched hotspot locations persist from the previous route. The matching subset
has no zero-capacity edge, but it is explicitly partial evidence.

Nine stored clock-rule bindings remain unchanged. The router now relaxes
`clk` **and `clknet_0_clk_regs`**, whereas the parent full route relaxed only
`clk`. The timing gains survive this effective policy, but this experiment does
not isolate its contribution from signal-wire redistribution. Minimum access
passes for 33,598 standard-cell pins and the macro, without proving simultaneous
detailed routability.

**Decision:** retain the timing and local-repair gains; reject whole-chip
electrical/reserve and congestion qualification. First use saved geometry,
loads and library costs to compare remedies for the complete residual families
under unchanged budgets. Independently reconcile the extra congestion marker
before assigning a location-specific congestion repair. A subsequent local
candidate must pass the complete contract before another separately admitted
whole-chip route. No further repair, detailed route, extraction, RTL/pipeline
change, backend promotion or licensing decision is part of this study.
The [path-route manifest](../physical/experiments/paired-path-route-results.json)
binds the raw evidence, independent intake and explicit failed gates.

## Physical organization policy and saved-chip screen

The [policy](../physical/experiments/paired-organization-policy.json) separates
physical intent from the exact repair and its eventual measurements. It binds
the settled `paired-path-route-01` database and original path contract, then
permits three bounded transformations: stronger existing buffers with free
space at their current origins; equal-count exchanges of ordinary leaf inputs
between same-size buffers carrying the same source; and a separate SRAM data
receiver in an unoccupied row rectangle. It explicitly protects 2,202 clock,
hold and endpoint instances. State, macro, delay and other transport inputs
stay attached to their existing branches during exchanges. Changed branch
pin-capacitance upper bounds must remain unchanged in every corner.

`scripts/check-physical-organization.py` reconstructs **211 trees / 1,109 family
branches**, with **774 buffers + 124 delay cells** and **4,613 true leaf
consumers**. Shared trunks and their **10,303.9776 µm²** of transport-cell area
are counted once. The broader **1,145-connection path contract** remains the
qualification scope. The six residual connections occupy four trees with 64
branches; **192 independent pin/corner comparisons** reproduce the saved STA
loads from the pinned Liberty files. Mixed receiver loads are summed at a
common rise/fall edge before selecting extrema; summing unrelated per-pin
maxima was caught and rejected in the first screen.

The completed saved-chip screen takes **7.330 s** and compares **18 choices**:

| Residual group | Cheapest relevant choice | What the screen establishes |
| --- | --- | --- |
| `_04527_` | Existing `buf_1` → `buf_2`, **+1.8144 µm²** | Growth fits its current row footprint; upstream pin-load cost is included. Leaf exchange improves a neighbor but leaves this target's span unchanged. |
| `_04701_` | Existing `buf_1` → `buf_2`, **+1.8144 µm²** | Driver `_09463_` would overlap `_11880__1348`. No permitted leaf exchange shortens the target. A placement-rule extension is needed for this choice. |
| SRAM DIN14, `net31` | Add a `buf_1` receiver, **+7.2576 µm²** | An empty row rectangle exists. Both the source's changed pin load and the new branch's available wire-capacitance budget are costed. Legal placement, pin access and timing remain unmeasured. |
| Bit 53: `_02981_`, `_03253_`, `_03380_` | Eight pairwise consumer exchanges, **zero added area** | All three geometric spans decrease, with unchanged per-branch counts, driver locations and edge-specific pin-load upper bounds. Some fixed transport consumers remain on these branches. |

For bit 53, pin-envelope HPWL changes **602.275 → 598.0025 µm**,
**947.010 → 928.255 µm** and **860.970 → 284.315 µm**, respectively.
The largest saving is on the third branch; the failing `_03253_` improves only
about 2% geometrically. This greedy eight-exchange search is neither an optimum
nor an electrical repair prediction. Two nonempty exchange candidates preserve
complete buffer-contracted circuit connectivity in virtual copies of the
independently saved Yosys netlist, including a 13-input reassignment for bit 53.
No physical netlist or database is edited by this check.

Strengthening every residual driver costs at least **18.1440 µm²**, exceeding
the **11.6542 µm²** left in the unchanged cumulative allowance; several current
footprints also collide. No complete portfolio passes the current geometry
rules. This rejects the enumerated choices, not the execution engine or all
possible physical organizations. A hypothetical mixed portfolio—bit-53
regrouping, the two `buf_2` upgrades and a DIN14 `buf_1` receiver—costs
**10.8864 µm²**, but still needs a permitted location for `_09463_` and has no
new timing, slew or wire-capacitance evidence.

**Next gate:** extend the policy narrowly to screen relocation of that one
buffer while accounting for every changed incident connection, protected
boundary and original area budget. Compare bit-53 groupings against the weak
branch's required wire budget rather than treating aggregate span savings as
qualification. Any selected regroup/resize/move combination needs independent
exact-edit checking, legal placement/power/pin geometry and fresh complete-family
and upstream STA in a bounded local probe. A new whole-chip route still requires
the complete original path contract and separate admission.
The **22-marker / 21-grid** congestion discrepancy remains untouched and is not
used to rank these candidates.

**107 focused tests** pass, including 17 organization checks covering shared
ownership, forged source membership, edge-specific capacitance, protected
loads, virtual readback corruption, placement collisions and cumulative area.
The [manifest](../physical/experiments/paired-organization-results.json) binds
`build/validation/paired-organization-01/report.json` and the exact final screen.
All earlier receipts are preserved. No CAD, new physical measurement, repair,
route, pipeline change or backend promotion occurs in this study.

Reproduce using a fresh output tag and the already staged source artifacts:

```sh
python3 -B -W error scripts/check-physical-organization.py \
  --source-manifest physical/experiments/paired-path-route-results.json \
  --policy physical/experiments/paired-organization-policy.json \
  --check-tag FRESH_ORGANIZATION_SCREEN
python3 -B -W error -m unittest discover -s test -p test_physical_organization.py
```

## Local qualification of the organization policy

The [refinement](../physical/experiments/paired-locality-policy.json) extends the
original policy in two bounded ways. `_09463_` may grow to `buf_2` and move by
at most ten **0.48 µm** sites, on its current row and orientation. Grouping may
perform up to sixteen equal-count leaf exchanges, ranking the worst residual
wire-load/budget ratio before aggregate span. Pin-capacitance bounds stay fixed
and passing neighbors' spans cannot increase. A branch-specific proportional
span scenario is used for screening; it is not a parasitic estimate or guarantee.

The **8.842 s** screen compares 35 choices and 104 complete combinations.
Twenty-six meet footprint and area screens; thirteen also meet the conditional
wire-budget screen. The selected combination uses the smallest displacement:
**0.48 µm left**, retaining both incident nets' geometric spans. The pinned LEF
reproduces the old A/X pin locations before projecting the resized cell.
Bit-53 target spans change **602.275 → 575.020**, **947.010 → 332.4225** and
**860.970 → 534.445 µm**. Sixteen swaps result in 23 distinct scalar-input
reassignments over ten branches, with no new state or buffer in that family.

The [exact plan](../physical/experiments/paired-locality-repair-plan.json) also
upgrades `_08797_` in place and adds one DIN14 `buf_1` receiver. Added area is
**10.8864 µm²**, leaving **0.7678 µm²** below the original cumulative cap.
`physical_organization_repair.py` checks source connectivity, protected cells,
same-row/grid movement, every changed footprint, consumer bijections and area
before compiling the recipe. Six preflight mutations are rejected; the combined
virtual plan preserves whole-circuit buffer-contracted connectivity.

One **18.720 s** local probe runs under **120 s / two CPUs / 2 GiB**, with the
source design and PDK mounted read-only. Fresh diagnostic collection takes
**24.822 s**, full connection/geometry/placement checks **81.585 s**, and minimum
pin access **5.314 s**. Only the local probe edits a candidate database; the
other checks read settled artifacts. The initial sandbox-only launch failed
before any container or probe directory existed; its receipt is retained, and
the authorized Docker launch is the sole physical edit attempt.

| Local evidence | Result |
| --- | --- |
| Complete original scope plus new receiver | **1,146 connections / 3,438 corner records / 6,876 min/max paths**, all at or above 20% reserve |
| Minimum electrical reserves | **24.5592% capacitance / 21.5316% slew** |
| Whole-chip electrical violations in local estimates | **Zero** capacitance, slew and fanout violations in all three corners |
| Retained timing | Slow setup **+0.420384 ns**, fast hold **+0.101286 ns**; every original setup/hold floor passes |
| Area | **359,371.6704 µm²**, cumulatively **+0.299786%** against the unchanged 0.3% budget |
| Exact identity and geometry | One added buffer, two resized buffers, exactly one original cell translated; all 2,202 protected instances, 342 clock connections and original power bindings retained |
| Minimum pin access | All **33,600 standard-cell pins** and the macro pass; no off-grid warnings |

The bit-53 load sets retain the same measured pin capacitances. Their fast-corner
wire capacitances change **0.157347 → 0.073543 pF**, **0.322079 → 0.042548 pF**
and **0.173625 → 0.067571 pF**. Thus the formerly failing `_03253_` gains
**54.34% capacitance reserve** with its original `buf_1` driver. This is direct
local routing evidence for improved distribution. The proportional-span screen
did not predict these capacitances, and they remain subject to full rerouting.

Independent fresh Yosys readbacks preserve the complete circuit after contracting
known buffers and transfer the retained **331,401-edge** oracle. A grounded new
receiver and a wrongly moved original cell are rejected. Fifteen guide sets
change within the sixteen declared incident nets; all clock guides and nine
stored clock-rule bindings remain. **110 focused tests** pass and all nine exact
containers are independently absent. The
[manifest](../physical/experiments/paired-locality-results.json) binds every gate.

**Local-study decision:** retain the candidate for independent whole-chip intake
under the original area reference, 20% reserve, timing floors and complete
1,146-connection coverage. That gate and its adverse result are now recorded
below. This local study's incremental zero overflow does not replace whole-chip
congestion evidence or establish detailed routing, extraction, physical
power-grid qualification or backend promotion.

Reproduce the saved-chip selection with fresh output names:

```sh
python3 -B -W error scripts/check-physical-organization.py \
  --source-manifest physical/experiments/paired-path-route-results.json \
  --policy physical/experiments/paired-organization-policy.json \
  --refinement physical/experiments/paired-locality-policy.json \
  --check-tag FRESH_LOCALITY_SCREEN
```

The sealed preflight, exact recipe, command receipts and independent verification
scripts live under `build/validation/paired-locality-01`; reproducing the physical
probe requires a fresh tag and the same bound source, recipe and pinned views.

## Shared physical edits and whole-chip requalification

`physical_organization_edits.py` separates four operations from candidate search:
resize a buffer, move-and-resize within a declared row/site bound, regroup equal
numbers of consumers under the same source, and insert a receiver. The
[edit plan](../physical/experiments/paired-locality-edits.json) and
[policy](../physical/experiments/paired-locality-edit-policy.json) preserve the
qualified local candidate. Both incident nets of changed buffers enter coverage.
The common checker admits different operation counts and rejects undeclared
geometry/connectivity, protected boundaries, wrong receiver rails, collisions
and false area. The previous experiment builder remains a compatibility adapter;
its exact recipe and independent proof reproduce unchanged.

Shared route intake schema 5 independently reconstructs full functional ancestry,
the exact edit, original role declarations, all **1,146 connections**, raw measured
records, complete timing, minimum pin access and the original area reference.
It transfers the existing **331,401-edge** oracle through fresh complete-netlist
readback. **121 focused tests** pass. Six real-artifact mutations with updated
hashes are rejected: weaker reserve, missing connection, fabricated measurement,
moved neighbor, reset area reference and a grounded receiver. The older add-only
intake retains its original guard.

**`paired-locality-route-01`** runs exactly one GlobalRouting step with automatic
design, timing and antenna repair disabled, under **600 s / four CPUs / 6 GiB**.
The flow reports **36 seconds** and exits successfully with congestion. No bound
is reached. Fresh diagnostics take **12.696 s**, connection/geometry/placement
collection **71.632 s**, and minimum pin access **4.888 s**. All ten exact
containers are independently absent before measurement analysis. A successful
tool exit establishes completion, not the following physical gates:

| Whole-chip coarse-route check | Result |
| --- | --- |
| Original six weak connections | All retain 20% reserve; `_03253_` has **53.66%** minimum capacitance reserve and **0.044594 pF** fast wire capacitance, versus **0.322079 pF** before the local edit |
| Complete scoped inventory | **1,142 / 1,146** meet reserve; `_02988_`, `_03097_`, `_03552_` fail; `_04718_` has **19.9146%** slow slew reserve |
| Independent whole-chip electrical checks | Four capacitance failures in every corner, including uncovered `_01924_`; twelve slow slew pins on `_02988_` and `_03552_`; no fanout failures |
| Slow setup | **+0.420384 → −0.055813 ns**; required retained floor **+0.367343 ns** |
| Fast hold | **+0.101286 → +0.064551 ns**; still positive, below retained floor **+0.079278 ns** |
| Area | **359,371.6704 µm²**, unchanged; original cumulative **+0.299786%** and **0.7678 µm²** remaining allowance |
| Identity and access | Byte-identical netlist, unchanged physical context and all 342 clock connections; all **33,600 standard-cell pins** and macro pass minimum access, no off-grid warnings |
| Congestion | **33** flow units / native markers / saved-grid units, all Metal3; two locations persist, no zero-capacity edges |

The three new covered capacitance failures descend from serial-shift bits
**50, 49 and 51**, respectively. Their pin loads and drivers are unchanged, but
fast wire capacitance rises **2.76×, 3.26× and 2.84×** against the local estimate.
Those ratios describe this run, not reusable safety factors. The six targeted
connections remain repaired while a full route redistributes wires elsewhere.

The uncovered `_01924_` is a shared control connection with eight immediate
consumers. It lies on the new worst setup path, from `r_mode[0]` to package status
`uo_out[4]`. The previous worst path starts at SRAM; its saved top-1,000 report
does not include the matching mode-to-status path. Comparing those two worst
slacks therefore cannot isolate the clock and data contributions.

A matched hold path **can** be compared without another CAD command. For
`ui_in[6] → _12281_/D`, data arrival remains **0.785377 ns** with every reported
data arc unchanged; capture-clock arrival changes **0.509116 → 0.548950 ns**.
That **39.834 ps** clock shift explains the **39.835 ps** slack loss at report
precision. All nine stored nondefault-rule bindings remain, but the old route
logged relaxations for `clk` and `clknet_0_clk_regs`, while the new log has none.
Logged decisions are distinct from both stored policy and proof of final wire
spacing; these coupled changes prevent attributing the regression to grouping
alone.

**Route-study decision:** retain the reusable edit/intake abstraction and the local
candidate as evidence; reject route qualification. The matched-path/family
diagnosis requested by this gate is now completed below. Keep the original budgets. The older
22-marker / 21-grid discrepancy is still an artifact-specific open question;
it does not invalidate this new reconciliation. No further route or repair,
detailed routing, extraction, pipeline change or backend promotion is admitted
by this result. The [manifest](../physical/experiments/paired-locality-route-results.json)
binds the complete evidence; the study scripts are in
`build/validation/paired-locality-route-01`.

## Matched clock, control and capacity diagnosis

**`paired-coupling-01`** reads the settled `paired-path-route-01` and
`paired-locality-route-01` chips without routing, placement or repair. Normalized
configurations are identical; source databases and tool image are hash-bound.
Every timing query fixes the source and destination transitions and all
intermediate data pins. Independent parsing requires the same pin/transition/cell
sequence, rather than comparing whichever path happens to be worst.

Five successful bounded commands total **50.489 s**: two complete three-corner
family/path collections, two additional path queries with input-pin detail, and
one geometry read. Each command is capped at **120 s / two CPUs / 2 GiB**, with
source artifacts mounted read-only and networking disabled. The first collector
attempt stopped on a Python syntax error before OpenROAD ran; its script, log and
receipt remain. Six exact collector containers and both source-route containers
are independently absent. No timeout occurs.

| Matched path | Before → after slack | What accounts for the change |
| --- | --- | --- |
| Slow `r_mode[0] → uo_out[4]` | **+2.262653 → −0.055813 ns** | Arrival grows **2.318466 ns**: **2.299226 ns data / 0.019240 ns launch clock**. Required time is unchanged. |
| Slow SRAM bit 53 → `uo_out[4]` | **+0.420384 → +0.113294 ns** | Arrival grows **0.307090 ns**: **0.101463 ns data / 0.205627 ns launch clock**. It remains positive but below the original retained setup floor. |
| Fast `ui_in[6] → _12281_/D` | **+0.104386 → +0.064551 ns** | Data arrival and all data arcs are identical; capture clock arrives **39.833486 ps** later. Hold-requirement change accounts for the **39.835244 ps** slack loss. |
| Fast `_11166_/Q → _11166_/D` | **+0.101286 → +0.101286 ns** | Launch and capture shift together; clock reconvergence correction preserves the self-hold margin. |

The control net `_01924_` has unchanged driver, consumers, pin loads and pin
geometry, yet fast wire capacitance grows **0.115121 → 0.309965 pF**. Its driver,
wire into `_06218_/B1` and following gate together add **1.534994 ns**, about
**66.76%** of the matched mode path's data-delay increase. Other arcs also
contribute; this is not a counterfactual prediction that repairing one net will
remove the whole regression.

The SRAM launch-clock delay increase is concentrated around the retained delay
chain: wire capacitance on `delaynet_3_clk` grows **0.085832 → 0.162166 pF**.
Its wire into `delaybuf_4_clk/A` and that buffer's cell delay together add
**0.173777 ns**. On the register side, input hold is affected by root clock
delivery and branch 1; the latter's wire capacitance grows
**0.025340 → 0.034717 pF**. Both sides are unchanged logical clock trees with
different routed-wire behavior. The recorded thirteen clock nets distinguish
root, SRAM delay chain and register branches.

Complete transport closure yields **118 connections**: six shared-control
branches, serial-bit-50/49/51 trees with **13 / 8 / 88** branches, and three
parameter-control branches. Every connection passes 20% reserve in the earlier
full route; afterwards **113 pass, four fail and one misses reserve**. All selected
pin loads and geometry remain unchanged. All six shared-control branches were
absent from the prior 1,146-connection inventory. The measured watchlist therefore
proposes **1,152 connections** for the next candidate, with original numerical
budgets; the production admission contract is not changed by this study.

Fresh geometry reproduces all **33 native Metal3 markers**. Thirty-four distinct
nets from these families cross **21 of 33** congested edges. Ordinary clock nets
cross nine edges, and every congested edge also has other signal traffic.
**No rule-bound NDR net directly crosses a current congested edge.** Removing
traffic from the selected families alone does not account for the twelve other
edges; this observation does not predict how a new route would redistribute them.

The pinned OpenROAD source explains the stored/runtime distinction. At commit
`dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`, `computeTrackConsumption` derives
routing cost from the stored width/spacing rule; `applySoftNDR` logs the relaxation
and changes the in-memory routing cost without clearing the OpenDB binding.
Both chips retain the same nine bindings and rule dimensions. The older route
logs softening `clk` and `clknet_0_clk_regs`; the newer route logs none. This
explains why stored-rule equality is insufficient, but does not establish that
relaxing those rules now would improve capacity or timing.

Four negative controls reject a changed path transition, missing arc, ambiguous
path and wrong grid identity. Fresh three-corner metrics reproduce the saved
whole-chip measurements, with complete consumed-net annotation. No production
source, RTL, physical database or prior receipt changes; the preceding 121-test
suite is retained and not rerun for these diagnostic/documentation artifacts.

**Decision:** retain the diagnosis and measured watchlist. The next bounded
screen should compare area-neutral regrouping across complete control/serial
trees and separately identify a routing constraint that can protect measured
clock delivery. Test the constraint's actual support before selecting a physical
candidate; stored rule names alone are not sufficient. Any candidate must retain
the inherited inventory plus six control branches, the original 20% reserve,
timing floors and area reference, all four matched paths, and independent global
capacity checks. Only **0.7678 µm²** remains in the existing allowance. No physical
repair or route is selected here. The
[manifest](../physical/experiments/paired-coupling-results.json) binds the full
analysis and `build/validation/paired-coupling-01/watchlist.json`.

## Reproduce the intake

Use fresh design/run/check names. Preparation is offline when the pinned views
are already staged; add `--fetch` only for missing pinned inputs.

```sh
python3 -B scripts/prepare-chip-physical.py --target physical/targets/paired.json --design paired-example
python3 -B scripts/run-physical.py --design paired-example --tag paired-example-import \
  --pdk-root /path/to/verified/pdk --from-step OpenROAD.CheckSDCFiles \
  --state build/physical/paired-example/initial-state.json \
  --checkpoint-manifest build/physical/paired-example/initial-manifest.json \
  --to OpenROAD.Floorplan --timeout-seconds 120
python3 -B scripts/check-mapped-import.py --tag paired-example-import
```

Continue the verified state and continuation manifest from that receipt through
`OpenROAD.DumpRCValues` → `OpenROAD.GeneratePDN`, again capped at 120 seconds.
Run `check-mapped-import.py --tag MACRO_RUN --placed-macros`. Its verified state
admits `Odb.RemovePDNObstructions` → `OpenROAD.STAMidPNR-2`, with
`--overrides physical/targets/comparison-overrides.json` and a 600-second cap.

```sh
python3 -B scripts/check-mapped-physical.py --physical-tag PLACEMENT_RUN --tag FRESH_MEASUREMENT
python3 -B scripts/check-mapped-physical.py --physical-tag mapped-local-place-01 \
  --step 25-openroad-stamidpnr-2 --target-bundle build/physical/target-control-01 \
  --tag FRESH_CONTROL_MEASUREMENT
python3 -B -m unittest discover -s test -p test_physical_target.py
```

Collectors use bounded read-only, network-disabled containers. Their successful
status means collection completed; violations remain visible in the report.
The final physical pin oracle accepts either target's selected receipt through
the existing `check-chip-physical.py --comparison ... --mapped-export ...` path.

To remeasure the selected local repair without rerunning placement or routing:

```sh
python3 -B scripts/check-mapped-physical.py --physical-tag paired-clock-01 \
  --repair-probe build/physical/repair-probes/paired-status-cone-01/report.json \
  --tag FRESH_REPAIR_MEASUREMENT
```

`--repair-probe` verifies the exact parent database, passed producer receipt,
input hashes, stopped containers and candidate database hash. It retains the
target's original configuration and checks actual repaired geometry and timing.
See [validation](validation.md#foundation-review-order) for explicit RC policy
and functional-evidence reuse rules.

The completed coarse route's
[selection](../physical/experiments/paired-route-selection.json) and
[overrides](../physical/experiments/paired-route-overrides.json) bind its source
repair. The actual state, snapshot, command and resource cap are retained in
`build/physical/paired-route-01-invocation.json`; the receipt is indexed by the
[coarse-route manifest](../physical/experiments/paired-route-results.json).
The shared intake's schema 3 accepts target-based buffer resizing and a linked
pin oracle without hard-coding one chip's trace length. It rejects changed
sources, stale artifacts, unrelated geometry, incomplete/violating placement
measurements, expanded flow stages, increased caps or enabled automatic repair.

For added buffers and clock branches, the completed reroute uses schema 4 in
[its selection](../physical/experiments/paired-reroute-selection.json).
`physical_added_route.py` independently checks logical identity, original-cell
placement, macro geometry and every added power binding. Inputs may use the
pinned shared PDK and recorded tool/library aliases, with exact byte checks;
candidate artifacts remain inside this checkout. The actual command, source
state, resource limits and admission are preserved in
`build/physical/paired-reroute-01-invocation.json`. It admits one GlobalRouting
step with automatic repair disabled, never detailed routing. Remeasure saved
output using `check-mapped-physical.py --physical-tag paired-reroute-01
--tag FRESH_MEASUREMENT --verify-nominal-layer-rc`.

The distribution candidate additionally uses
[its schema-4 selection](../physical/experiments/paired-distribution-route-selection.json)
and `physical_distribution_route.py` to recompute the immutable experimental
budgets before admission. Its saved invocation records the one completed route;
admission of that run does not imply the routed output qualifies. Remeasure it
with `check-mapped-physical.py --physical-tag paired-distribution-route-01
--tag FRESH_MEASUREMENT --verify-nominal-layer-rc`. Native congestion markers
must match that output's saved grid and flow total before interpreting crossings.
