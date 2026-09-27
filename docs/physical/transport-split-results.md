# Wire-aware transport refinement

**The two transport repairs survive extraction; the third A layout remains
electrically rejected.** All 14 preceding fanout failures clear, but four different
nets gain excess antenna loads and one wire-heavy net still exceeds capacitance.
Timing, routing/full-rule Magic DRC, LVS, antenna, power connectivity and actual
circuit checks pass. All three allocated A full-flow attempts are now consumed.

The [frozen protocol](transport-split-experiment.md) records this September 27
continuation and its limits. The source is the [rejected 41-buffer placement](antenna-load-results.md);
its validated circuit and routing resources make it a suitable repair input,
although its electrical failures prevent physical acceptance.
The [manifest](../../physical/experiments/transport-split-results.json) binds
controls, recipes, saved artifacts, independent measurements and remaining gates.
[Research status](../research/status.md) owns the active decision.

## Select from measured routes

The earlier placement reduced functional receiver counts, but two connecting
wires alone exceeded the 0.300 pF capacitance limit. The refinement preserves all
41 buffers and inserts one noninverting transport buffer on each failing net.

The selector reconstructs each saved routing tree, weights wire segments with
the existing calibrated layer capacitances, and considers cuts with known
consumer membership. It minimizes the larger parent/child load. The proposal
includes worst-corner buffer input capacitance, the full difference between the
wire model and measured wire capacitance on both sides, and a doubled Manhattan
allowance for accessing the nearest vacant legal row site. These allowances
support selection; they are not a bound on subsequent routing detours.

| Parent | Moved consumer | Buffer origin, µm | Estimated parent / child, pF |
| --- | --- | --- | --- |
| `_03354_` | `antenna_branch_3/A` | (601.92, 555.66) | 0.158007 / 0.159078 |
| `paired_balanced_148_17_out` | `antenna_branch_26/A` | (611.04, 464.94) | 0.162986 / 0.165347 |

The two added `sg13cmos5l_buf_4` cells cost **29.0304 µm²**, bringing the coarse
signal-cell/SRAM area to **375,276.7008 µm²**. Every original cell and placement,
all 41 preceding buffers, the SRAM, power connections, package geometry and all
340 coarse clock routes remain fixed. Exactly four signal routes change.

## Coarse admission

The source import reproduces every saved grid capacity/usage entry and route.
Two removal/replay controls and exact edit/revert pass. Independent checks
reconcile all 174,035 native resource entries, with zero overflow under the
inherited conservative one-unit reservation; the edited routes do not touch it.

Arbitrary-state equivalence checks all 1,636 state output bits against all 5,000
state inputs and controls, including clock/reset. Hidden-state and inverted-control
mutations are rejected. Actual-circuit package-pin replay passes **331,401 edges /
1,517 frames**. These checks preserve the existing interpreted-circuit evidence;
they do not complete the paired memory/controller/package refinement in Lean.

| Corner | Setup / hold, ns | Cap / slew / fanout violations |
| --- | ---: | ---: |
| Slow | +0.845953 / +0.326675 | 0 / 0 / 0 |
| Typical | +6.814850 / +0.135776 | 0 / 0 / 0 |
| Fast screen | +9.968000 / +0.040186 | 0 / 0 / 0 |

Every consumed net has a wire estimate, all 64 SRAM write holds pass, and the
SRAM-to-rejection dependency stays absent. Minimum pin access passes with zero
standard-cell or macro pins lacking an access point. It does not establish
simultaneous routability.

| Fast-screen capacitance | Previous parent, pF | Repaired parent, pF | New branch, pF |
| --- | ---: | ---: | ---: |
| `_03354_` | 0.308709 | **0.173158** | **0.111028** |
| `paired_balanced_148_17_out` | 0.319284 | **0.164448** | **0.129658** |

Both sides of both buffers meet the additional 0.240 pF screening target in all
three corners. Source and candidate use the same calibrated global-route model;
these are estimates rather than extraction. No alternate placement is needed.

The source's antenna headroom is preserved: each affected parent has at most
three functional inputs, and each transport output drives one existing buffer.
Final antenna insertion is measured below.

## Final layout and extraction

The admitted candidate uses the existing third A slot. The full continuation
starts at detailed routing, with four threads, the same pinned image, floorplan,
timing constraints and nominal RC. It explicitly sets both native cap and slew
checker corner lists to `["*"]`; the independent shared gate also checks fanout.
The flow saves its final views and returns **failed** because all three corners
fail the now-enabled native capacitance gate. This is an electrical rejection,
not an interrupted route or a missing result.

| Corner | Extracted setup / hold, ns | Cap / slew / fanout violations |
| --- | ---: | ---: |
| Slow | +1.229028 / +0.302916 | 1 / 0 / 4 |
| Typical | +7.311548 / +0.119118 | 1 / 0 / 4 |
| Fast screen | +10.303861 / +0.026968 | 1 / 0 / 4 |

Fresh STA on the saved final netlist and extracted SPEF exactly reproduces the
flow's timing/electrical metrics. All consumed nets have wire annotation; the
128 unannotated SRAM outputs are unused and disconnected by the declared intake.
All 64 SRAM write holds pass: the minimum fast-screen write hold is
**+0.112675 ns**, and protected bit 54 has **+0.791296 ns**. The isolated
SRAM-to-rejection path remains absent.

| Transport net | Fast-screen extracted capacitance, pF | Physical input count |
| --- | ---: | ---: |
| `_03354_` | 0.153978 | 2 |
| `transport_split_net_0` | 0.098260 | 1 |
| `paired_balanced_148_17_out` | 0.157156 | 3 |
| `transport_split_net_1` | 0.134390 | 1 |

All four connections remain below the additional **0.240 pF** screening target
in every extracted corner. The transport-buffer hypothesis succeeds on its two
chosen routes; that local result does not make the whole layout acceptable.

The final database preserves all **12,232 original cells and placements**,
package pins, macro geometry, routing obstructions, power shapes and placement
exclusions. It adds **97 antenna cells** and **45,905 power-only fill/decap cells**.
Independent final-netlist identity checks allow only those additions, reject
hidden-state and clock corruption, and pass **331,401 package-pin edges / 1,517
frames**. These checks bind behavior to this exact physical circuit.

Routing DRC, full-rule Magic DRC, final antenna violations, critical disconnected
pins and all seven reported LVS difference/error counts are zero. Every added
cell's power binding is checked; both power rails have connected shapes. Eight
declared unused package inputs remain noncritical disconnections. KLayout DRC,
KLayout XOR and flow EQY remain disabled and are not counted as passes.

## What still fails, and why the next scope changes

All **14** fanout failures in the preceding detailed layout are absent. The four
new failures occur on branches that still had eight functional inputs before
antenna repair. Exact final terminal accounting gives:

| Net | Functional inputs | Added antenna inputs | Final inputs / limit |
| --- | ---: | ---: | ---: |
| `paired_balanced_100_21_out` | 8 | 4 | 12 / 8 |
| `paired_balanced_133_4_out` | 8 | 1 | 9 / 8 |
| `paired_balanced_140_0_out` | 8 | 1 | 9 / 8 |
| `paired_balanced_19_5_out` | 8 | 1 | 9 / 8 |

Their capacitance and slew pass. This is load-count exhaustion caused by actual
protection cells, with no change to their original logical consumers.

The separate `paired_balanced_5_4_out` capacitance failure remains at every corner:
**0.303477 pF fast**, **0.302570 pF typical**, **0.301837 pF slow**, versus
**0.300000 pF**. It drives three branch buffers and has no antenna inputs.
Fast-screen wire capacitance is **0.290461 pF**, with up to **0.013016 pF** of
pin capacitance. Partitioning receivers did not provide enough wire margin.

Read-only inventory finds **905 signal nets with eight physical input terminals**
before final protection. Of these, precisely the four failed nets gain antenna
inputs in this run. Overall, 97 protection inputs are distributed over 69 nets.
This does not predict that all 905 need protection, or establish a bound on
future antenna demand. It does show why repairing only the previous violation
list cannot establish complete closure.

**Next discriminator:** compare a load budget across the complete distribution
network with a bounded electrical-repair stage after antenna insertion. Either
approach must account for actual protection inputs and wire capacitance together,
preserve clock/write hold, and repeat routing, antenna and electrical checks
after edits. Include the separate wire-heavy branch in that budget. Cost the
alternatives before allocating another full route; observed antenna counts alone
are not guaranteed reserve requirements. This is a proposed scope, not another
authorized full-flow slot.

Compared with the preceding detailed layout, fanout failures fall **14 → 4** and
the worst reported capacitance falls **0.307562 → 0.303477 pF**. Slow setup loses
**0.222309 ns** but stays positive; fast-screen hold gains **0.006227 ns**.
These are combined consequences of 41 branch buffers, two transport buffers and
new detailed routing, not an isolated estimate of the two added buffers.

## Costs, artifacts and verification

Signal-cell/SRAM/antenna area is **375,804.6912 µm²**, including
**527.9904 µm²** of antenna cells. This is **509.8464 µm²** above the preceding
detailed layout and **16,432.2529632 µm² / 4.5725%** above the historical
359,372.4382368 µm² comparison allowance. Fill/decap occupies another
**491,412.0960 µm²**; total placed area is **867,216.7872 µm²**. The
**1,289.28 × 710.64 µm** outline is unchanged. The comparison allowance is not
a competition die limit.

| Charged stage | CAD seconds |
| --- | ---: |
| Coarse controls, candidate and circuit replay | 90.880 |
| Minimum pin-access preflight | 3.248 |
| Third A detailed flow | 444.182 |
| Final circuit identity and pin replay | 41.076 |
| Independent geometry and extracted STA | 20.656 |
| This continuation | **600.042** |
| Cumulative campaign | **5,652.722 / 28,800** |

Cumulative charge is **94.21 minutes**. All three A attempts are used; two B
attempts remain reserved behind accepted A. All scoped containers are absent,
and frozen input/artifact hashes remain unchanged. No second placement proposal
was needed, and no further route is allocated by this result.

The coarse recipes and controls are under
`build/validation/transport-split-01/`; final flow, circuit, geometry and extracted
timing receipts are under `build/validation/transport-detailed-01/`.
`analyze-final.py` verifies the saved evidence and applies the shared acceptance
gate. `publish-record.py` binds the manifest and derives the complete load-count
inventory in `closure-diagnosis.json`. Existing receipts use exclusive output
creation and must not be overwritten. Reproduction needs a new lineage-linked
output identity and allocation; these checks do not establish a clean-source
physical replay.

| Final artifact | SHA-256 |
| --- | --- |
| Database | `a74f4a35aa1c2baf1a37c86df55081c94873106afac64ea2679329d04c6c1ad1` |
| GDS | `e1decb4f9ea5a73692effd6da2d517e28708e4630bdfa9192d2b2f8a8a578455` |
| Netlist | `3c9e93948530355644bf31a97532752a76aa7b507dbfea256c933fee81566854` |
| Extracted SPEF | `52cb33331e4030e3bacbbb71b2fa2241725a9ea658212d8c6c2203e7e04f5888` |

Fast standard cells remain characterized at −40°C while the SRAM fast view is
−55°C, without a qualified pairing or established conservative bound. Complete
paired timed controller/loading/package refinement, A acceptance, the 64-record
B iteration and clean-source replay remain open. No new Lean theorem, competition
qualification or silicon result is claimed.
