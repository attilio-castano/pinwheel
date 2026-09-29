# Coordinated status/decode placement — September 26

**Retain the preceding 34-buffer SRAM design; reject both placement candidates
for physical qualification.** Coordinated placement improves local setup from
+0.322 ns to +1.196 ns without adding area, but complete routing leaves only
+0.182 ns setup, introduces four hold violations (worst −0.083 ns), creates
four capacitance failures and raises router overflow from 16 to 20.

The [manifest](../../physical/experiments/status-region-placement-results.json)
binds the saved results, actual readbacks and failed attempts. This experiment
measures a bounded region, not the complete 2,722-cell status cone. The
[preceding control-distribution study](control-distribution-experiment.md)
retains its original results; [research status](../research/status.md) owns the
active decision and next gate.

## Scope and controls

The status output has 2,722 combinational ancestors. A reproducible backward
traversal selects the last fourteen connection levels, then excludes package
port drivers, clock-connected cells, registers, the SRAM, explicit hold buffers,
delay cells and cells on the retained minimum-delay witnesses. **1,226 cells**
remain movable; all **10,076 other instances** are fixed during placement.

This boundary contains all three previously competing drivers (`_06692_`,
`_06420_`, `_06603_`) and their immediate upstream decode logic. It is a bounded
portion of the complete status cone, not a re-placement of the entire chip.
All instances, cell types, net connections, dimensions, package pins, macro
geometry, clock and hold cells, power connections and reserved geometry must
survive independently checked ODB and Verilog readback.

The measurement inventory contains **4,199 connections**: the prior 1,298,
every incident signal net and complete affected transport trees. It includes the
status package wire with its separately checked **0.010 pF** SDC load. All
64 SRAM write-data inputs retain minimum/maximum path checks at three corners.
Repeated near-critical reports are deduplicated by their data paths when
assessing coverage; explicit witnesses through each of the three competing
drivers supplement the unrestricted and exact historical path checks.

OpenROAD selects the coordinates. The first pass skips its initial solver and
uses its wire-length objective. The coordinated candidate enables the initial
solver and uses a 0.03 placement-overflow stopping threshold. An attempted
timing-guided version fails inside the pinned tool before producing a candidate;
the completed variant uses wire length only. Readback independently establishes
that no cell was added, removed or resized. The region and physical identity
policy are identical for both completed variants.

The original bound permits two placement variants, three complete-route
attempts and **1,800 CAD seconds**. Two recorded tool-failure recoveries extend
the edit-attempt count to four while retaining at most two completed candidates
and the original time/route bounds. Each local container has two CPUs, 2 GiB, no network
and read-only source design/PDK mounts. Complete-route comparison requires
verified placement identity, nonnegative local setup/hold and the retained
SRAM write-hold floor. It is a diagnostic comparison; physical qualification
still requires the original **+0.367343 / +0.079278 ns** comparison floors,
electrical reserve, routing and pin-access checks.

## Baseline

The unchanged complete reroute reproduces every baseline connection measurement
and exact selected/write path. The expanded baseline retains **+0.321638 ns
setup / +0.089025 ns hold**, one capacitance failure and three reserve misses.
No additional electrical failure appears in the wider inventory.

The cell/macro area remains **359,776.2816 µm²**, **0.412712%** above the original
358,297.5456 µm² reference and **403.843363 µm²** above the historical allowance.
Placement introduces no additional cell area. The recorded inherited overage
remains permitted under the [exploration policy](../research/README.md#exploration-with-temporary-size-overages).

## Execution notes

The first pass terminates its main placement iteration at zero because its
initial overflow, 0.0451, is already below the 0.10 stopping threshold. It
changes 928 coordinates and 543 orientations (1,012 distinct cells), with a
maximum Manhattan displacement of **15.24 µm**. The three troublesome drivers
move by at most 0.48 µm. This limited result does not establish that the intended
regional reorganization has occurred. The next recipe therefore enables up to
20 initial-solver iterations and uses a tighter stopping threshold. The completed
solve takes five initial-solver
iterations and ends its main iteration at 487 with a 0.03 threshold. It changes
1,183 cells with at most 354 µm Manhattan displacement.

One first-candidate timing collection is rejected by its input hash guard: the
unused second recipe was revised while that collection ran. The actual worker,
selected recipe and candidate database did not change. The attempt and its time
are retained; the launcher now freezes the selected stage's recipe, policy and
route gate rather than unrelated future recipes. A fresh collection is required
before analysis or admission. Missing candidate stages and missing route gates
fail before output creation or Docker launch.

The attempted timing-guided solve aborts in `dpl::Opendp::legalPt` during
virtual resizer buffer insertion (`std::clamp` assertion, signal 6). The first
untimed recovery runs past a stable 0.03 overflow crossing but cannot reach
0.01; its penalty grows until numerical divergence (`GPL-0305`). Neither
attempt produces a candidate database. A second recorded recovery uses 0.03
and completes. All failures consume the unchanged CAD time budget.

The first independent coordinated-placement check fails because one cell
lands on a previously empty row, where its original neighboring cells cannot
supply a rail orientation. A separately hash-bound OpenDB extraction confirms
the row's actual `MX` orientation and 480 × 3,780 DBU site. The checker now
accepts authoritative row definitions, cross-checks populated rows and rejects
missing, incompatible or inconsistent definitions. The failed check, old
helper/tests and original request are retained; the new measurement-support
freeze changes no circuit, policy or timing gate. All 11,302 placement statuses
and all row definitions are independently unchanged.

## Local results

| Measurement | Baseline / unchanged control | Limited first pass | Coordinated placement |
| --- | ---: | ---: | ---: |
| Worst slow setup, ns | +0.321638 | +0.580231 | **+1.195870** |
| Worst fast hold, ns | +0.089025 | +0.089025 | +0.089025 |
| Capacitance violations at every corner | 1 | 1 | 1 |
| Slew / fanout violations at every corner | 0 / 0 | 0 / 0 | 0 / 0 |
| Connections meeting 20% electrical reserve | 4,195 / 4,199 | 4,196 / 4,199 | **4,197 / 4,199** |
| Exact original bit-53 path setup, ns | +0.321638 | +0.580231 | **+1.681067** |
| Added cell area, µm² | 0 | 0 | 0 |

The coordinated local result clears the `_02877_` and `_02966_` reserve
shortfalls. `_04754_` remains a capacitance failure and `_05207_` remains below
reserve. The worst read shifts from SRAM bit 53 to bit 51. All three targeted
branches improve locally: their unrestricted slow setup margins become
**+1.681067 / +1.471247 / +1.814118 ns**. SRAM write inputs retain their hold
floor. These are local estimates; the complete-route comparison is separate.

## Complete routing changes the decision

| Measurement | Baseline / unchanged control | Limited first pass, full route | Coordinated placement, full route |
| --- | ---: | ---: | ---: |
| Worst slow setup, ns | +0.321638 | +0.299410 | **+0.181782** |
| Worst fast hold, ns | +0.089025 | +0.105010 | **−0.082617** |
| Fast hold violations | 0 | 0 | **4** |
| Whole-chip capacitance violations, every corner | 1 | 1 | **4** |
| Scoped connections meeting 20% reserve | 4,195 / 4,199 | 4,196 / 4,199 | **4,193 / 4,199** |
| Minimum SRAM write-data hold, ns | +0.161179 | +0.230123 | +0.192793 |
| Router / stored-grid overflow | 16 / 15 | 17 / 16 | **20 / 19** |
| Added cell area, µm² | 0 | 0 | 0 |

The coordinated route has **three** failing connections in the scoped inventory
(`_02292_`, `_04508_`, `_04567_`) and a **fourth** outside it:
`memory.storage/A_DOUT[11]`, on `memory.mem_q0[11]`. The latter's slow-corner
reported load is 0.070019 pF against a 0.064000 pF limit. Whole-chip reports are
reconciled separately from the independently measured inventory; the wider
inventory is not whole-chip electrical coverage.

The three previously troublesome branches still improve relative to baseline
when measured through those drivers, but other competing paths become worse.
The exact original bit-53 path retains +0.622734 ns after full routing, while
the new worst bit-53 path is +0.181782 ns. On that original exact path, full
routing loses 1.058333 ns relative to the local result: **21.545 ps** from later
launch-clock arrival and **1,036.788 ps** from the data portion after launch.
Local timing gains therefore do not establish complete-chip improvement.

Minimum pin access passes on both complete candidates: 33,678 standard-cell
pins, zero standard-cell or macro no-access counts, and no off-grid warnings.
All row definitions and placement statuses remain unchanged. The router/native
2-D marker totals are 16, 17 and 20, while saved-grid totals are 15, 16 and 19.
Each discrepancy remains a failed strict reconciliation, not a congestion-free
result. Partial incremental grids are excluded from this comparison.

## Why an unmoved path now violates hold

The new worst hold path runs from `_10937_/Q` through `_05578_`, `_05579_` and
`_05580_` to `_10884_/D`. None of these cells was selected or moved. A separate,
exact fast-corner probe reproduces **+0.149842 ns** in both the baseline and
local coordinated layout, then **−0.082616 ns** after complete routing.

The 232.458 ps margin loss decomposes as follows:

| Change after complete routing | Effect on hold margin |
| --- | ---: |
| Launch clock arrives 70.976 ps earlier | −70.976 ps |
| Capture clock arrives 109.029 ps later | −109.029 ps |
| Data delay becomes 41.231 ps shorter | −41.231 ps |
| Other required-time terms increase | −11.221 ps |

Changed clock delivery accounts for **180.005 ps** of the loss. Preserving clock
cells and connectivity did not preserve their routed delays. Across the two
local candidates, all **96 matched launch/capture clock-pair comparisons** on
the historical paths remain unchanged; complete routing changes that environment.

The next hypothesis should couple placement, global routing and timing/electrical
repair, with explicit clock and hold treatment after routing. More isolated
placement tweaks against the old wire estimates would not address this measured
failure. The subsequent [coupled-flow comparison](routed-repair-experiment.md)
tests that hypothesis while retaining this experiment's original evidence.

## Evidence limits

These are global-route estimates under the existing 20 ns constraint, retaining
the historical fast standard-cell −40°C / SRAM −55°C mismatch. Local incremental
routing grids are partial. Placement identity does not establish wire timing,
congestion or pin access. No new Lean theorem, RTL change, extra pipeline cycle,
complete paired compiler/package refinement, detailed routing, extracted timing,
antenna or power-grid qualification follows from this experiment.

## Evidence and reproduction

The [placement helper](../../scripts/physical_region_placement.py) and its
[seven tests](../../test/test_physical_region_placement.py) implement the bounded
selection and independent readback checks. The complete portable suite passes
**478 tests / 2 skips**. Re-run just the helper's tests from the repository root:

```sh
python3 -B -m unittest discover -s test -p test_physical_region_placement.py
```

The final report binds **3,473 artifacts / 2,904 retained source versions**.
Six accepted timing collections supply **75,582** pin/net/corner reconciliations,
**576** selected-path checks and **2,304** SRAM write-interface checks. There are
also **90** targeted branch witnesses, **six** exact new hold witnesses and
**2,304** unrestricted regional witness records; repeated data paths in the
latter are not independent coverage. All **2,190** affected transport families
are checked. The manifest records the exact scopes and source digests.

Eighteen CAD attempts consume **927.689 seconds** of the original 1,800-second
bound: fifteen pass, one measurement is rejected for an input-hash change and
two native placements fail. Four edit attempts produce two completed candidates;
three complete routes finish. All eighteen containers are absent and no timeout
occurs. Including preceding regional/SRAM/control work, retained CAD time is
**1,946.962 seconds**.

The tracked manifest points to the ignored run directory
`build/validation/status-region-placement-01/` and report SHA-256
`b841063f537ad665c35165d8f1b9f46be54e871f00953212e5469ba28ae881dd`.
Review or reproduction requires those retained files, the original SRAM
checkpoint, pinned local container image and PDK inputs named in `request.json`.
The manifest alone is insufficient. Use fresh output tags and a new source
freeze for any replay; the completed stage directories must remain immutable.

The retained pinned OpenROAD sources explain the placement controls:
[Tcl command arguments](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/gpl/src/replace.tcl)
and [solver defaults](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/gpl/include/gpl/Replace.h).
Their source snapshots are included in the run artifacts; the logs establish
which iterations and stopping conditions actually occurred.
