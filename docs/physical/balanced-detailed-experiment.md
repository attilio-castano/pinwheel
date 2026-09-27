# Balanced design: detailed layout and extraction

**The redesigned chip completes detailed layout with positive extracted timing,
but A is not accepted.** At the unchanged 20 ns clock, slow setup is
**+1.451337 ns**, versus −3.190857 ns in the first allocated layout. Full-rule
Magic DRC, routing DRC, LVS, antenna and power-connectivity checks pass. One
capacitance violation, 14 fanout violations, fast-corner qualification and
complete paired refinement remain open.

This is the second and final A full-flow attempt under the
[complete-iteration allocation](../research/complete-design-iteration.md).
The [manifest](../../physical/experiments/balanced-detailed-results.json)
binds the actual layout, fresh extracted measurements, independent circuit
checks, remaining failures and resource ledger. [Research status](../research/status.md)
owns the next decision.

## From the screened circuit to actual wires

The input is the independently checked [seven-buffer candidate](balanced-electrical-experiment.md),
following isolated validation and balanced signal distribution. Its global-route
screen has no electrical violations or conservative overflow. Minimum pin access
also passes: no standard-cell or macro pins lack an access point.

The pinned flow starts at detailed routing with empty metrics, four CPUs, 6 GiB
and a 5,400-second limit. It retains the 6×4 outline, package and I/O constraints,
SRAM placement, 1,572 flip-flops and exact execution behavior. Full-rule Magic
uses flat GDS import, following the earlier matched control; no rule, macro,
timing path or electrical limit is waived.

Routing adds **118 input-only antenna cells**; filler insertion adds **45,931
power-only filler/decap cells**. Independent readback proves every original
cell, placement, signal connection, clock connection, macro/power/package shape
and reserved corridor unchanged. The ordinary detailed router chooses actual
wires; coarse-route clock segments are not claimed to equal detailed wires.

| Measure | Input coarse screen | Actual extracted layout |
| --- | ---: | ---: |
| Slow setup, ns | +0.845816 | **+1.451337** |
| Slow hold, ns | +0.326675 | +0.301876 |
| Typical setup / hold, ns | +6.809810 / +0.135776 | +7.308272 / +0.117794 |
| Fast-screen setup / hold, ns | +9.968000 / +0.040186 | +10.220580 / +0.020742 |
| Cap / slew / fanout violations, each corner | 0 / 0 / 0 | **1 / 0 / 14** |
| Signal-cell, SRAM and antenna area, µm² | 374,652.5472 | 375,294.8448 |

The input and final columns are different physical stages. The earlier detailed
layout is a stage-matched historical comparison, but its architecture, buffering
and placement also differ; the timing gain cannot be attributed to seven buffers
alone. The combined architectural and physical changes survive extraction.

A fresh STA run reads the final netlist and the exact extracted SPEF with empty
metrics. It reproduces all flow timing/electrical metrics. Every consumed net
has parasitics; 128 unused drivers explain all unannotated outputs. Every SRAM
write-input hold path passes: the minimum fast-screen write hold is
**+0.118523 ns**, and write bit 54 is **+0.763871 ns**. The SRAM-to-rejection
dependency remains absent.

## The remaining electrical mechanism

All **14 fanout failures are explained exactly by inserted antenna loads**.
Before routing, each affected net had at most eight input loads. The 1–6 added
antenna inputs raise those totals to 9–13. The pinned Liberty default assigns
each input one fanout unit and limits fanout to eight. For example,
`paired_balanced_142_4_out` changes from eight receivers to eight receivers plus
five antenna cells. The independent readback reconciles every reported count.

The capacitance failure is a separate net, `paired_balanced_5_4_out`, with
**no added antenna cells**. Its eight receivers and extracted wire load total
0.304679 pF typical, 0.302660 pF slow and 0.307562 pF in the fast screen, against
the 0.300000 pF limit. The worst overage is 0.007562 pF / 2.521%. All seven nets
repaired in the preceding experiment remain electrically clear.

The next physical hypothesis is therefore specific: account for antenna
protection in the distribution load budget, and split or shorten the one
remaining capacitive branch. Removing needed antenna protection or increasing
the limits is not an established repair. Any changed circuit needs equivalence,
hold checks, rerouting, extraction and the same layout checks. Both allocated A
attempts are consumed; a new experiment requires an explicit allocation rather
than a new tag under the exhausted limit.

## Completion checks and the flow-status trap

Routing DRC, full-rule Magic DRC, antenna violations and all seven reported LVS
difference/error counts are zero. The two power grids have connected shapes;
all 116,477 actual power terminals bind to the expected rails. Eight unused
package inputs are reported disconnected (`ena`, `ui_in[7]`, `uio_in[2..7]`),
with zero critical disconnected pins. This is not a claim that every declared
package input is consumed.

The exact final signal circuit preserves the checked source after accounting
for input-only antenna cells and cells with no signal terminals. The final
netlist independently passes **331,401 package-pin edges / 1,517 frames**;
hidden-state and changed-clock controls are rejected. Pinned cell/SRAM models
remain trusted; this is not an SDF simulation or completed universal package
refinement.

The flow exits successfully despite its electrical failures. Its resolved
`MAX_CAP_VIOLATION_CORNERS` and `MAX_SLEW_VIOLATION_CORNERS` are both `[""]`,
which select no enforcement corners. The capacitance checker logs the measured
failures and then reports no enforced failure. There is no corresponding
fanout checker in this flow sequence.

The new small shared [timing acceptance check](../../scripts/physical_timing_acceptance.py)
requires setup/hold slacks, setup/hold violation counts, and capacitance/slew/
fanout counts for **every explicitly requested corner**. Missing or invalid
metrics fail; passing aggregate metrics cannot hide a failed corner. Five tests,
including 21 individual corner/metric failure cases, pass. On actual receipts it
accepts the coarse screen and rejects the final layout. Physical acceptance also
requires separately qualified libraries, parasitics, layout checks and behavior.

KLayout DRC, KLayout XOR and flow EQY remain disabled and are not counted as
passes. The independent circuit check supplies the stated signal-preservation
evidence. Fast cells at −40°C and SRAM at −55°C remain an unqualified pairing;
the [inventory audit](balanced-electrical-experiment.md#costs-characterization-and-replay)
found no compatible delivered view or established bound. Competition pin/template
admission, complete paired refinement, B and clean-source replay remain open.

## Costs and reproduction

The antenna cells add **642.2976 µm²**. Signal-cell/SRAM/antenna area is
**375,294.8448 µm²**, 15,922.4065632 µm² / 4.4306% above the historical comparison
allowance. Fill/decap area is another 491,921.9424 µm²; the total placed area is
867,216.7872 µm² across 58,238 instances. Keep physical fill separate from useful
logic cost. The original 1,289.28 × 710.64 µm outline is unchanged.

The full flow takes **413.996 seconds**. Preflight, final-netlist checks, geometry
and fresh extraction checks bring this phase to **478.773 CAD seconds**;
including the preceding electrical phase, this continuation charges **568.830
seconds**. Cumulative campaign charge is **4,926.281 seconds / 82.10 minutes**
against 28,800 seconds. Both A attempts are used; the two B attempts remain
behind A's acceptance gate.

The first fresh-timing inspection used `nom` instead of the flow's `nom_*` SPEF
key and was rejected before timing. Its completed geometry readback, failed
receipt and 3.421-second charge remain. The corrected read-only run uses the
same extracted file with the original wildcard. A stale preflight invocation
counter is corrected in a separate qualification record; all elapsed preflight
time was charged from the outset.

Recipes under `build/validation/balanced-detailed-01/` bind 1,173 initial inputs,
the exact source database, native detailed-routing script, complete flow,
final-netlist replay and fresh STA. `analyze-final.py` applies the independent
acceptance gate and diagnoses loads from actual readback. Existing receipts
cannot be overwritten. Repeating physical routing needs a fresh identity and
allocation; reusing these hashes establishes artifact reuse, not a second run
or a clean-checkout reproduction.
