# Seven-net electrical repair

**The bounded repair passes its complete coarse-route screen.** Seven added
buffers clear the four capacitance and 23 slow slew violations in the retained
[balanced layout](buffer-balance-experiment.md). The candidate has zero
conservative coarse overflow, +0.845816 ns slow setup and +0.040186 ns
fast-screen hold. This result admits the [second allocated detailed-layout
attempt](balanced-detailed-experiment.md); it is not physical acceptance.

The [manifest](../../physical/experiments/balanced-electrical-results.json)
binds the source, declared edit, controls, actual circuit and measurements.
[Research status](../research/status.md) owns the current decision.

## What changed and why

Four failures were excessive wire capacitance, two were weak-gate slew, and
one was slew at SRAM write input 54. Merely increasing drive strength would
not split the excessive wire loads. The declared plan therefore inserts six
`sg13cmos5l_buf_4` cells and one `sg13cmos5l_buf_2`, with each consumer partition
and legal vacant site recorded before routing.

The seven original nets and seven new branches are the only rerouted nets.
Every original cell, its placement, power binding and all **340 clock routes**
remain fixed. Macro geometry, package pins, reserved corridor and existing
hold-delay cells remain intact. No RTL, state, execution edge, clock period,
timing exception or generator default changes.

| Measured corner | Setup before → after, ns | Hold before → after, ns | Cap / slew / fanout before → after |
| --- | --- | --- | --- |
| Typical | +6.381760 → +6.809810 | +0.135776 → +0.135776 | 4 / 1 / 0 → **0 / 0 / 0** |
| Slow | +0.820730 → +0.845816 | +0.326675 → +0.326675 | 4 / 23 / 0 → **0 / 0 / 0** |
| Fast screen | +9.638520 → +9.968000 | +0.040186 → +0.040186 | 4 / 0 / 0 → **0 / 0 / 0** |

Each measurement starts with empty metrics, the saved database, propagated
clocks and calibrated global-route parasitics. Every consumed net has a wire
estimate; the 128 unannotated outputs are independently reconciled unused
terminals. The SRAM-to-rejection path remains absent.

All 64 SRAM write-input hold paths pass in each corner. Write bit 54's
fast-screen hold changes **+0.764382 → +0.668779 ns** after restoring its edge
slew. The other 63 hold results are unchanged; their minimum remains
**+0.100718 ns**. The smaller whole-chip +0.040186 ns margin is a different path.

## Controls and independent checks

The source-specific import control preserves all circuit connections, physical
geometry, route segments and timing measurements, but **does not reproduce one
saved usage entry exactly**. Metal3 grid entry `[21,72]` has saved capacity/usage
17/16 versus reconstructed 17/15. Capacity is unchanged everywhere. The retained
wires independently explain the reconstructed usage; this does not establish
why the extra saved unit exists.

The original strict rejection is retained. A narrower conservative screen
counts the extra unit against every candidate and prohibits any edited route
from touching that resource. Native capacity/reduction/usage at the corresponding
edge remain 11/6/9; all nine existing route contributors remain unchanged.
Both ordinary and conservative overflow are zero. This qualification applies
to this scoped edit and is **not a general strict-import pass**.

Seven independent removal/replay controls and a real seven-buffer edit/revert
restore all **174,035 native resource entries**, the saved grid and circuit.
Four nets reorder their terminal lists after reconnecting; sorted terminal lists
and byte-identical Verilog establish identity. The original overly strict
list-order comparison and its corrected checker are both retained.

The measured candidate reproduces the controlled edit's routes and resource
state. Independent readback checks exact buffer membership, consumer partition,
placement, power, row/site legality, area and buffer-contracted logic. Every
saved-grid usage delta agrees with independently expanded wire demand.

Actual-netlist SAT compares all package outputs and all FF/SRAM inputs,
including clocks and resets: **1,636 exposed state outputs and 5,000 observed
state inputs**. Hidden state and an inverted control are rejected. The actual
candidate also passes **331,401 package-pin edges / 1,517 frames**. These checks
preserve the existing circuit correspondence boundary; closed memory/controller/
package refinement is still open.

## Costs, characterization and replay

The seven buffers add **96.1632 µm² / 0.025674%**, giving **374,652.5472 µm²**
cell/SRAM area and 12,189 instances. The outline remains
**1,289.28 × 710.64 µm**. The historical 359,372.4382368 µm² comparison allowance
is exceeded by 15,280.1089632 µm²; that allowance is not a competition die limit.

The phase charges **90.057 CAD seconds**, including the failed startup, both
controls, candidate and independent circuit checks. Cumulative campaign charge
at this checkpoint is **4,447.508 seconds**. The following detailed-layout
experiment accounts separately for its preflight and full-flow attempt.

The fast corner remains unqualified: standard cells are characterized at
−40°C and SRAM at −55°C, both at 1.32 V. The read-only upstream inventory at
`5e6d592e4002946a4616f798c357f0f3c06cf3b6` supplies the same unmatched pair.
The [SRAM datasheet](https://github.com/IHP-GmbH/IHP-Open-PDK/blob/5e6d592e4002946a4616f798c357f0f3c06cf3b6/ihp-sg13g2/libs.ref/sg13g2_sram/doc/RM_IHPSG13_1P_512x64_c2_bm_bist.txt)
identifies the fast characterization at −55°C; its operating-temperature range
does not establish conservative propagation and setup/hold bounds at −40°C.
The audit requires a compatible characterized view or a justified bound. No PDK
file, label or temperature has been changed.

Retained recipes are under `build/validation/balanced-electrical-01/`:
`request.json`, `buffer-plan.json`, `candidate.tcl`, the no-edit/edit-revert
recipes, `launch-02.py`, `worker-02.py`, independent verification and circuit
checks. The initial `inspect.py` accidentally shadowed Python's standard module;
its failed startup and corrected launcher are retained. Replay requires the
hash-matching predecessor, pinned native adapter and fresh output identities;
existing outputs are deliberately not overwritten. This is a reproducible
local continuation, not the plan's clean-checkout A/B replay.
