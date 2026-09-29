# Chip electrical repair with preserved clocks

The September 27 continuation closes the five reported electrical failures on
the actual third A layout. **Five buffers and one protection cell pass fresh
whole-network timing/electrical checks, native routing DRC, antenna checking,
exact circuit checks and package-pin replay.** All 12,329 original instances
retain their placements, all 97 existing antenna cells retain their net
bindings, and all 340 clock wires remain exact through detailed routing.

This is a qualified local chip integration, not accepted A. Final fill,
streamout, full-rule DRC/LVS, final extraction/power checks, compatible fast
characterization and complete paired refinement remain. No fourth full-flow A
attempt was allocated. [Status](../research/status.md) owns the next decision;
the [manifest](../../physical/experiments/chip-closure-results.json) binds the
measurements and every failed recipe under the [frozen protocol](chip-closure-experiment.md).

## What changed and what passed

The source is the pre-fill, detailed-routed database from the
[third A attempt](transport-split-results.md). Four branches exceeded the
fanout limit after antenna insertion; a fifth weak driver exceeded its wire
capacitance limit. The checked candidate splits the four overloaded branches
and places a stronger buffer beside the capacitance-limited driver. Existing
diodes stay on their original nets. One new diode, immediately beside
`antenna_branch_40`, protects the new transport branch.

| Measure | Unchanged control | Checked candidate |
| --- | ---: | ---: |
| Capacitance / slew / fanout violations, each corner | 1 / 0 / 4 | **0 / 0 / 0** |
| Slow setup margin | +1.229029 ns | **+1.242753 ns** |
| Fast-screen hold margin | +0.026968 ns | **+0.026979 ns** |
| Native routing DRC / antenna violations | 0 / 0 | **0 / 0** |
| Original clock wires changed, before extraction | 0 | **0 of 340** |
| Instances, before fill | 12,329 | **12,335** |
| Added area | — | **78.0192 µm²** |

Fresh independent STA uses the new netlist and extracted SPEF, with no inherited
metrics. Every required corner reports zero setup, hold, capacitance, slew and
fanout violations. All 64 SRAM write holds pass in each corner.

| Recorded corner | Setup | Hold | Minimum SRAM write hold |
| --- | ---: | ---: | ---: |
| Fast screen | +10.304851 ns | +0.026979 ns | +0.112677 ns |
| Typical | +7.309177 ns | +0.119130 ns | +0.251519 ns |
| Slow | +1.242753 ns | +0.302933 ns | +0.457890 ns |

The repaired weak parent falls from 0.303477 pF to **0.004724 pF**, against
0.300000 pF. Its new branch measures **0.178732 pF** against the new buffer's
1.200000 pF cell limit. No existing cell or constraint was resized or relaxed.
The other repaired parent/child fanout counts are **7/6, 6/4, 6/4 and 5/5**;
the transport parent/child count is **1/4**, including its new diode.

Signal/SRAM/antenna area becomes **375,882.7104 µm²**, 4.5942% above the
359,372.4382368 µm² historical comparison allowance. The outline stays
**1,289.28 × 710.64 µm**. Fill/decap and competition admission remain separate.

## The integration lesson

The unchanged native initialization control preserves every cell, connection
and wire. The runtime map covers all **12,186** originally connected nets.
Its first conversion rewrites 2,520 guide records and rebuilds resource usage
from detailed wires; a second initialization reproduces the complete saved
grid and guides exactly, with zero overflow. This qualifies the explicit edit
used here, not arbitrary traversal by native electrical-repair algorithms.

Two independent hazards appeared when transferring the small fixture to the
chip. First, logical `dont_touch` does not fix physical routing. Second, the
incremental global-router callback treats changed pin-access metadata as a dirty
net, then deletes that net's detailed wire. Adding a nearby cell can therefore
invalidate an unchanged clock route. Merely marking that route fixed for the
detailed router can leave it missing altogether. An actual failed candidate
had **three missing clock wires while its native electrical, antenna and DRC
violation reports were zero**. Wire coverage and parasitic completeness are
separate mandatory checks.

The retained recipe therefore:

1. Changes only the clock wire-status bits to `FIXED`. Exact native
   encode/decode roundtrips and a separate raw-opcode comparison verify that
   all coordinates, extensions, patches, vias, terminals and other nets stay
   unchanged. The helper rejects unsupported encodings; it is scoped to this
   saved database.
2. Applies the declared buffer/diode edit without an active global-routing
   callback. It invalidates only the five named parent wires, then rebuilds
   native routing resources from the retained detailed wires. Native routing
   selects the five parents and five new child nets.
3. Checks the actual routed result, then extracts fresh parasitics. Measurement
   of the unchanged control runs in a separate process, preserving the live
   router's wire state during the edit.

Global routing changes exactly the five parent wires. Detailed routing also
changes **14 neighboring signal wires**, all recorded and included in the
whole-network checks. No clock changes. Exported resource grids have zero
overflow, and every one of **12,191** connected candidate nets retains detailed
wiring. Fresh annotation is complete for every consumed net; the 128
unannotated drivers are independently reconciled to unused outputs/inputs.

These decisions follow the pinned native implementation, including
[dirty-net deletion and pin-access callbacks](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/grt/src/GlobalRouter.cpp),
[fixed-wire handling](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/drt/src/io/io.cpp),
and [wire encoding](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/odb/src/db/dbWireOpcode.h).
The relevant source copies and tool identity are retained with the recipes.

## Independent checks and rejected work

The final readback permits exactly five known noninverting buffers and one
declared input-only diode. Contracting those buffers preserves every original
signal connection. Physical readback verifies the exact edit, original geometry,
power terminal bindings and the new diode's receiver binding. Corrupting a clock,
adding hidden state or moving an old antenna input to a different net is rejected.
The final circuit passes **331,401 package-pin edges / 1,517 frames** using the
retained functional cell/SRAM models. This is not SDF simulation or a new Lean
theorem.

| Retained recipe/control | Disposition |
| --- | --- |
| `control-01` | Unchanged initialization, full pin membership and repeatability pass. |
| `candidate-01` | Stops before editing: clock objects were passed where net names were required. |
| `candidate-02` | Five buffers clear electrical failures, but one antenna violation and two changed clock routes remain. Circuit/pin checks pass. Independent STA wrapper rejects an obsolete input path. |
| `candidate-03` | Incremental DEF import does not replace wire status; jumper-only repair leaves the antenna failure. STA reports are retained, but a missing wrapper state key prevents completion. |
| `clock-lock-01/02/03` | DEF-only replacement and a Python rectangle accessor fail; the final native recoder passes exact roundtrips for all 340 clock wires. |
| `candidate-04` | Adding the declared diode clears antenna; the active global-routing callback deletes three protected clocks. The same missing STA state key is retained. Reject regardless of zero native violation counts. |
| `candidate-05` | Explicit five-wire invalidation, fixed clocks, fresh extraction, independent STA, circuit/pin replay and route-coverage checks pass. |
| `clock-verification-01` | Independently verifies only status bits changed, exact clock routes, complete connected-net wires and rejection of the actual missing-clock control. |

All attempted artifacts and failures remain intact. The final preparation uses
only the declared additions and preserves original diode bindings; no historical
diode-to-receiver ownership is inferred from numbering or proximity.

## Evidence, cost and next gate

The local evidence root is `build/validation/chip-closure-01/`. The retained
candidate is `candidate-05/output/native/final.odb`, with its fresh
`repaired.spef`, `final.v`, independent `final-timing.json`,
`candidate-05-check/report.json`, `clock-verification-01/output/report.json`,
and `candidate-05-analysis.json`. The manifest records exact paths and hashes.
Launchers refuse to overwrite runs; a replay needs a fresh case and recorded
lineage. Ignored build artifacts are not a clean-checkout replay package.

Controls, failed CAD runs and both independent circuit/pin checks cost
**634.894 CAD seconds**, bringing the campaign to **6,324.523 seconds /
105.41 minutes** of 28,800 seconds. The integration allocation was 1,800 seconds;
each native invocation was bounded to 600 seconds, four CPUs and 6 GiB. All
receipted containers are absent. Three A full-flow attempts remain used; two B
attempts remain reserved. This work performs bounded incremental chip routing,
not a fourth full-flow attempt.

The next gate is final fill/streamout, full-rule DRC/LVS, power/connectivity and
final extracted timing on this exact candidate. The prior third A's signoff
checks do not transfer automatically. Standard-cell fast views at −40°C and
SRAM views at −55°C remain unqualified together. Complete timed paired-controller,
loading and package refinement, accepted A, capacity-change B and clean-source
replay remain open under the [complete iteration plan](../research/complete-design-iteration.md).
