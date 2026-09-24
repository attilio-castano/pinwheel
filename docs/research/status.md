# Research status

Updated 2026-09-24 for navigation; latest experimental evidence is dated
2026-09-23. This page owns the **active decision and next evidence gates**.
Read [results](results.md) for completed conclusions, [journal](journal.md) for
dated receipts, and the linked studies for measurements and reproduction.
The [research workflow](README.md) explains those record boundaries;
[submission obligations](../submission-plan.md) own final acceptance criteria.

## Objective and current decision

Build a reloadable, generally programmable protocol engine that preserves pin
timing, capture, branching and atomic program replacement, then establish that
the emitted chip is physically feasible under the
[competition constraints](../competition.md). Keep semantic proof, mapped RTL,
local electrical estimates, whole-chip routing and final layout as distinct
evidence layers.

| Role | Current position | Detailed owner |
| --- | --- | --- |
| Semantic reference | The unrestricted two-read flip-flop chip preserves the exact edge contract. The selected hybrid dictionary SRAM has a closed-loop initialized array/controller proof, with external macro and emitted-package binding still open. | [Storage and execution](../storage-primitives.md#closed-loop-hybrid-execution-2026-09-21) |
| Experimental execution candidate | The full-capacity paired controller retains canonical E64 operations and 256 positions/32 records using one 512×64 SRAM, banked parameters and a one-read successor schedule. Its 290-word image is experimental; mapped checks and conditional schedule lemmas do not close complete compiler, admission or package refinement. | [Compact execution](../compact-execution-study.md#full-capacity-follow-up) |
| Physical comparison | The latest paired locality edit passes its local budgets, but its independently rerouted whole-chip candidate is **rejected**. Its original area reference is 358,297.5456 µm², with a fixed cumulative 0.3% increment cap; the candidate uses 359,371.6704 µm², leaving 0.767837 µm². | [Physical targets](../physical-targets.md#shared-physical-edits-and-whole-chip-requalification) |

**Retain the shared physical-edit abstraction and independent admission checks;
do not promote the locality candidate.** One bounded coarse route keeps all six
local target gains, but only **1,142 of 1,146** scoped connections retain the
experimental 20% electrical reserve: three fail and one misses reserve. Another
capacitance failure lies outside that inventory. Slow setup is **−0.055813 ns**;
fast-screen hold is **+0.064551 ns**. The retained slow setup/fast-screen hold
floors are **+0.367343/+0.079278 ns**. Overflow rises
**22 → 33**, with all 33 new native markers reconciled to the saved grid. Exact
netlist/placement, power binding, area and minimum pin access pass; **121 focused
tests** and six admission mutations pass. The
[whole-chip route manifest](../../physical/experiments/paired-locality-route-results.json)
binds this rejected qualification separately from the successful
[local probe](../../physical/experiments/paired-locality-results.json).

The [matched-path diagnosis](../physical-targets.md#matched-clock-control-and-capacity-diagnosis)
separates the losses. Mode-to-status loses **2.318 ns**, mainly in data;
SRAM-to-status loses **0.307 ns**, mainly in launch-clock delivery; and input hold
loses **39.835 ps** through its capture clock. The
[coupling manifest](../../physical/experiments/paired-coupling-results.json)
binds four exact paths, five complete transport trees and thirteen clock nets.
These observations do not identify a single routing-policy cause.

The subsequent [timing and communication organization study](../physical-organization-study.md)
has **already screened all 1,152 watchlist connections** against the saved chip.
Twelve bounded consumer swaps across fourteen branches preserve virtual
buffer-contracted identity, but no complete family passes its conditional wire
budget. Two proposed local decoder copies cost **21.7728 µm²** before any
replacement credit, above the remaining **0.767837 µm²**. Replaying the earlier
clock environment still leaves both selected setup paths below their retained
floors. This was a **4.112-second read-only screen**, with no CAD run, physical
edit or candidate admitted; its [manifest](../../physical/experiments/paired-organization-study-results.json)
and study own the full comparison. Retain regional decoding as a structural
option with an explicit budget. The [43-buffer chip](../chip-physical-study.md#local-data-buffering-and-complete-wire-estimates--september-22)
remains the physical control; the upload pipeline stays opt-in.

## Next discriminators

1. **Complete the saved-chip boundary measurements.** Measure the two missing
   decoder parent nets, `_01590_` and `_01808_`, and collect the opposite
   setup/hold checks for the four matched timing paths. Preserve their clock
   identities and the thirteen-clock watchlist. The current one-sided clock
   bounds cannot establish a feasible clock tree.
2. **Compare complete regional organizations.** Cost replacement or reuse of
   existing distribution trees alongside local decoding, including the shared
   control and serial-bit-49/50/51 families, passing siblings, both sides of
   new gates, retained hold delays and shared routing capacity. Keep the
   original timing floors, 20% reserve and cumulative area reference. If a
   broader structural comparison needs more than 0.767837 µm², state its
   separate absolute limit and show the old-cap result beside it; do not
   retroactively qualify the rejected chip.
3. **Admit only a complete, falsifiable physical candidate.** Require an exact
   edit plan, independent functional identity, legal placement and a joint
   timing/electrical/capacity prediction before bounded placement or coarse
   routing. Recheck all **1,152 inherited/watchlist connections** plus any new
   branches and global violations, the matched data and clock paths, native
   congestion, pin access and original budgets after execution. No current
   organization clears this gate; detailed routing remains unadmitted.
4. **Bind the chosen implementation to the final chip.** Compose the paired
   controller's compiler/admission, actual macro behavior, complete package
   traces and atomic replacement before backend promotion. The upload stage
   has a separate memory-view obligation; host integration of the 290-word
   image follows the selected hardware decision. Final extracted timing,
   electrical, antenna, power-grid and layout-netlist checks remain required
   before the [submission package](../submission-plan.md).

## Evidence boundaries and where to go deeper

| Question | Evidence owner and current limit |
| --- | --- |
| What exactly did the paired physical attempts establish? | [Physical targets](../physical-targets.md) traces local repairs, reroutes, admission and diagnosis. Its [latest route manifest](../../physical/experiments/paired-locality-route-results.json) records successful collection and failed qualification. A local electrical pass does not imply whole-chip or detailed routing closure. |
| Why did the latest organization screen stop? | [Timing and communication organization](../physical-organization-study.md) gives the complete tree, timing and area comparison. Its span scaling and virtual identity are planning evidence, not measured routed benefit. |
| What does the chosen execution model prove? | [Compact execution](../compact-execution-study.md) gives the paired capacity, controller, mapped SAT and open refinement boundary. [Storage primitives](../storage-primitives.md) owns the earlier hybrid closed-loop theorem, which does not automatically transfer to the paired controller. |
| What happened in other physical and architectural branches? | [First chip physical study](../chip-physical-study.md), [chip architecture](../chip-architecture-study.md) and [map tiles](../map-tile-study.md) retain their experiments. [Results](results.md) indexes dispositions and reopening conditions; [journal](journal.md) retains dated receipts. No experimental backend is promoted by those screens. |
| What is demonstrated to a host? | [Host workflow](../host-workflow.md) covers RTL pin demonstrations and upload cost. Board transport, continuous supervision and the paired 290-word host path remain separate obligations. |

The fast-screen standard-cell and SRAM temperatures remain mismatched. The
20% connection reserve and 0.3% area increment are **experiment comparison
rules**, not organizer requirements. Pin-level RTL and mapped-corner checks
cannot establish extracted timing, electrical or board behavior. Historical
ignored `build/` artifacts may be absent in a fresh checkout; tracked manifests
identify their original reports but cannot reconstruct them.

## Stable constraints and deferred work

<a id="the-official-outline-2026-09-18"></a>

The repository's pinned competition assumption is a **6×4** allocation, a
**1,289.28 × 710.64 µm** rectangle with **43 Metal4 pins near the top-left
edge**. The
[pinned-file check](../competition.md#the-outline-and-the-pinned-files)
distinguishes historical core runs with stand-in port placement from the later
chip flow using the official template. A prior two-port core timeout is not an
impossibility proof or a universal utilization limit.

Both-synchronous indexed storage needs a different latency contract. One-port
UART changes, alternative gating and broad ISA expansion are deferred. The
resident-payload workload needs a bounded instruction and hardware cost before
promotion. Preserve the tested digital sampling conditions: SPI requires
`d + tco ≤ halfCycles`; I²C requires `d ≤ phaseCycles` and `d < waitCycles`.
These digital bounds do not establish analog sampling behavior. Root licensing,
publication and submission remain separate decisions under the
[submission plan](../submission-plan.md).
