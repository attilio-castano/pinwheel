# Research status

Updated 2026-09-27 after SRAM interface checks and bounded internal LVS controls.
This page owns the **active decision and next evidence gates**. Read
[results](results.md) for conclusions, [journal](journal.md) for receipts and
linked studies for measurements and reproduction.

## Objective and current decision

Make a complete chip-design iteration possible for someone without hardware
expertise. Pinwheel's reloadable protocol engine is the test case: preserve pin
timing, capture, branching and atomic replacement while connecting one exact
implementation to formal meaning and physical feasibility. Then repeat the
process for a declared capacity change. Competition admission remains separate.

**Active plan: [complete design iteration](complete-design-iteration.md).**
The filled chip retains its passing electrical, timing, full-rule GDS DRC and
package checks. The new [SRAM study](../physical/sram-extraction-results.md)
establishes a passing **351-pin exported-GDS boundary comparison** with signal
and power fault rejection. **Full GDS signoff and A remain unaccepted:** SRAM
internal extraction and layout/schematic qualification still fail.

| Checked result | Current evidence |
| --- | --- |
| Setup / hold / electrical limits | Positive at every recorded corner, zero violations; **+1.242753 ns slow setup**, **+0.026979 ns fast-screen hold** |
| Original circuit and physical layout | All **12,335** pre-fill instances, all original wire encodings, **340 clock nets** and **98 antenna bindings** preserved |
| Finishing | **45,901** signal-free filler/decap cells; no new signal circuitry or routing |
| Full-rule Magic GDS DRC / antenna | **0 / 0** |
| Connectivity / power | All **12,191** connected nets wired; complete consumed-net parasitics; both power grids connected and every power terminal bound |
| Functional replay | **331,401 package-pin edges / 1,517 frames** pass on the filled circuit |
| Exported-GDS SRAM boundary LVS | **Pass:** all 351 pins accounted for, zero differences; existing schematic SRAM blackbox retained |
| Deliberate signal / ground wiring faults | Both rejected by native LVS; four invalid pin-list cases also rejected |
| Supplied macro versus macro in chip GDS | All **32 layers** and **754,685 text labels** preserved exactly |
| SRAM internal qualification | **Rejected:** two residual Magic overlaps, 438 conversion diagnostics; independent strict hierarchical SRAM LVS fails |

The original extra ground terminal belongs to the raw ground equivalence class
and disappears when control hierarchy is imported consistently. The adapter
changes 338 bus-pin spellings and preserves every pin and connection. No ground
alias or terminal deletion is applied. Flattening all SRAM internals removes all
24 original overlap errors in isolation, but full-flat chip extraction times out.
The cheaper control import permits boundary LVS while leaving internal errors;
its blackbox pass cannot hide those failures.

The independent PDK checker records 23 matching cell pairs, two nonmatching
pairs, five schematic-only mismatches and a skipped top-level comparison. Its
flat-mode control times out before a verdict. The concrete diagnostics include
resistor-model disagreement in a delay dummy and two absent extracted NMOS
devices in a word-line driver. They do not yet distinguish physical defects
from context-dependent extraction.

**Next: qualify a small SRAM context fixture for device recognition and
resistor-model correspondence.** Preserve neighboring wells, contacts and
resistor markers around the failing cells and retain open/short/device-removal
controls. Require a complete strict SRAM result or justified supplied-IP
evidence before accepting the macro blackbox for signoff. Keep the current
filled chip; another chip routing run does not resolve this checking boundary.

This continuation costs **1,316.754 CAD seconds / 21.95 minutes**, including all
failures and timeouts. Campaign total is **8,028.479 seconds / 133.81 minutes**
of eight hours. Three A full-routing attempts remain used and two B attempts
reserved; no additional A slot, chip edit or PDK change occurred. The
[SRAM manifest](../../physical/experiments/sram-extraction-results.json) retains
the positive interface result, negative controls, internal failures and exact
source identities. The original failed finalization receipt remains unchanged.

The fast library audit still finds standard cells at −40°C and SRAM at −55°C,
with no compatible delivered fast pair or established conservative bound.
Complete timed controller/loading/package refinement remains open. Power-grid
continuity passes, but IR-drop results use default voltage-source placement and
modeled activity; package-level power delivery remains unqualified. Disabled
KLayout DRC, streamout XOR and whole-flow EQY are not passing checks. Establish
accepted A before admitting the 64-record B design; clean-source replay is open.

Signal-cell/SRAM/antenna area stays **375,882.7104 µm²**, 4.5942% above the historical
comparison allowance, on the unchanged **1,289.28 × 710.64 µm** outline. Filler/decap
adds 491,334.0768 µm² of occupied area, for 867,216.7872 µm² total instance area;
that fills existing space and does not enlarge the die. Competition admission
remains separate.

| Role | Current position | Detailed owner |
| --- | --- | --- |
| Semantic reference | Unrestricted two-read flip-flop chip preserves the edge contract; hybrid SRAM has an initialized array/controller proof. Complete paired correspondence remains open. | [Storage and execution](../storage-primitives.md#closed-loop-hybrid-execution-2026-09-21) |
| Experimental execution candidate | One 512×64 SRAM, 256 positions/32 canonical records, explicit host format and 290-word kernel-checked images. Timed controller/loading/package composition remains open. | [Image certificate](../storage/paired-image-certificate.md) |
| Retained filled chip | Electrical, timing, GDS DRC, antenna, circuit/pin replay and SRAM boundary LVS pass; internal SRAM qualification remains open. | [SRAM qualification](../physical/sram-extraction-results.md) |
| Historical third full-flow layout | Its one-cap/four-fanout failure is retained. The new GDS control also exposes its SRAM extraction gap; its earlier LVS used DEF/LEF. | [Third A layout](../physical/transport-split-results.md) |

## Earlier starting checkpoint

The following local results explain the checkpoint used by the first full
attempt. Its extracted measurements above supersede these estimates for current
physical acceptance; the historical experiments retain their original verdicts.

**`route-import-fix-01/candidate` was the starting physical checkpoint.**
The [import repair and signal experiment](../physical/route-import-fix-experiment.md)
qualifies a pinned native adapter, then adds one buffer beside a weak XOR driver.
Every original cell and all **342 clock routes** remain fixed. Independent actual
netlist/geometry checks and fresh whole-chip measurements pass.

| Measure | Hold-repair reference | Single-buffer continuation |
| --- | ---: | ---: |
| Slow setup / fast hold | +0.382789 / +0.143801 ns | Unchanged |
| Electrical reserve shortfalls | 5 | **4** |
| Reported capacitance / slew / fanout violations | 0 / 0 / 0 | 0 / 0 / 0 |
| Native / saved-grid / marker overflow | 25 / 25 / 25 | 25 / 25 / 25 |
| Added area | Reference | **14.5152 µm²** |

The import now reproduces every saved capacity/usage entry and all **126,729**
source segments. Native removal and a real buffer edit/revert restore all
**174,035** checked 2-D/3-D edge entries exactly. Four controls cover the initial
adapter and a follow-up correction to its derived overflow counter; the corrected
adapter reproduces the measured candidate's circuit, routes and resource state.
**79 focused tests**, **10 launcher refusal checks**, minimum pin access and
independent readbacks pass. The
[manifest](../../physical/experiments/route-import-fix-results.json) preserves
both tool versions, every control and the source/candidate identities.

The target's slow slew improves **2.082 → 0.355 ns**; both buffered branches
exceed the 20% reserve floor. Local setup gains **1.246 ns**, while local hold
margin falls **0.396 → 0.211 ns** and still passes. All 64 SRAM write hold checks
retain their floors. This is a useful measured tradeoff, not physical closure.

**The proposed `_01876_` consumer partition is deferred pending the complete
acceptance audit.** It remains a possible local repair if a demonstrated blocker
justifies it. The four reserve shortfalls are `_01876_`, `_02877_`, `_04597_` and
`_05213_`; they do not define completion. Congestion reduction remains a separate
gate: this experiment leaves **25** overflow units. Retain complete resource,
clock, setup/hold and electrical accounting in subsequent comparisons.

Total candidate area is **361,597.9392 µm²**, **2,225.5009632 µm²** above the
historical allowance. The hold-repair checkpoint remains the matched reference,
and the coordinated layout remains a lower-congestion comparison. Prior
[routing-policy](../physical/routing-policy-experiment.md) and
[import-control](../physical/incremental-routing-import-experiment.md) failures
retain their historical verdicts. No detailed-route or backend admission follows.

**September 23 baseline: retain the shared physical-edit abstraction and
independent admission checks; reject the locality candidate.** One bounded coarse route keeps all six
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

The September 23 [timing and communication organization study](../physical/physical-organization-study.md)
screened **all 1,152 watchlist connections** against the saved chip.
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

**Allow temporary size overages during architectural exploration.** The user's
September 25 direction permits an idea to exceed current size targets while its
benefit is tested and later optimizations are investigated. Record the original
target, candidate size and overage, benefit, regressions and next optimization
question under the [exploration policy](README.md#exploration-with-temporary-size-overages).
The remaining 0.767837 µm² from the earlier repair experiment is not a veto on
new architectural ideas. Historical verdicts and final qualification remain
separate from exploratory progress.

## Next discriminators

1. **Qualify the supplied SRAM checking boundary.** Use small context fixtures
   to resolve the two failing library comparisons and model conventions before
   repeating complete strict SRAM LVS. Preserve every pin, geometry and native
   failure; the passing chip boundary comparison retains a schematic blackbox.
   Keep fast characterization compatibility separate. No further chip route is
   justified by these extraction failures.
2. **Establish physically feasible A and its correspondence.** Use the
   [bounded plan](complete-design-iteration.md) to select full-flow candidates,
   permitting recorded exploratory size overages. Connect paired compilation,
   admission, closed memory execution, package and host behavior to the actual
   implemented netlist. Historical results from other backends do not transfer.
3. **Repeat for a meaningful capacity change.** Increase distinct record capacity
   from 32 to 64 while retaining 256 positions, atomic replacement and execution
   timing. Require the same behavioral and physical gates; record image-format,
   area and implementation consequences explicitly.
4. **Demonstrate a reproducible design iteration.** Recover both acceptance
   reports through the same documented workflow, with declared inputs and no
   unrecorded manual netlist edits. Required missing checks remain incomplete;
   experimental layout success is separate from the [submission package](../submission-plan.md).

## Evidence boundaries and where to go deeper

| Question | Evidence owner and current limit |
| --- | --- |
| What exactly did the paired physical attempts establish? | [Physical targets](../physical-targets.md) traces local repairs, reroutes, admission and diagnosis. Its [September 23 route manifest](../../physical/experiments/paired-locality-route-results.json) records the baseline's failed qualification; the [regional experiment](../../physical/experiments/regional-decoding-results.json) records the later measured alternatives. A local gain does not imply whole-chip or detailed routing closure. |
| Can saved routes be reopened for a local edit? | [Import repair and one signal buffer](../physical/route-import-fix-experiment.md) passes exact no-edit and actual edit/revert accounting. The first local edit removes one reserve shortfall with unchanged global timing and clock routes. The adapter remains pinned and restricted; four shortfalls and 25 overflow units remain. |
| What did routing-policy changes establish? | [Routing policy and reserve](../physical/routing-policy-experiment.md) records an ineffective grid option, matched reroute drift and a timing-priority candidate with worse congestion. No cells or area changed; all three saved congestion views reconcile. |
| What did the hold-fix continuation establish? | [Protected-load repair](../physical/hold-repair-experiment.md) reproduces and fixes the pinned optimizer failure, passes both retained timing floors and reported electrical limits, and records the area, reserve and congestion tradeoff. Preparation and repair effects are measured separately. |
| What did coupled repair establish? | [Routed repair](../physical/routed-repair-experiment.md) separates initialization from repair, demonstrates electrical/setup and congestion gains on the coordinated layout, retains two new hold violations and records the pinned-tool continuation failures. |
| What did coordinated placement establish? | [Status/decode placement](../physical/status-region-placement-experiment.md) records local gains, both rejected complete routes, an unmoved hold path damaged mainly by clock rerouting, global electrical failures outside the scoped inventory, and pinned-tool/checker recoveries. |
| What did the control-distribution follow-up establish? | [Competing read paths](../physical/control-distribution-experiment.md) records two failed variants, a reproducible control, whole-chip regressions, changing bottlenecks, congestion-accounting limits and the interrupted control. The earlier SRAM design remains the starting point. |
| What did SRAM distribution and write timing establish? | [SRAM distribution](../physical/sram-distribution-experiment.md) records two local variants, unchanged/candidate coarse reroutes, the full watchlist, minimum pin access, timing gains and new routed failures. |
| What did regional decoding establish? | [Regional decoding](../physical/regional-decoding-experiment.md) records two measured variants, one coarse reroute, actual readback checks, benefits and new limiting paths. [Timing and communication organization](../physical/physical-organization-study.md) retains the preceding saved-chip screen. |
| What does the chosen execution model prove? | [Compact execution](../storage/compact-execution-study.md) gives the paired capacity, controller, mapped SAT and open refinement boundary. [Storage primitives](../storage-primitives.md) owns the earlier hybrid closed-loop theorem, which does not automatically transfer to the paired controller. |
| What happened in other physical and architectural branches? | [First chip physical study](../chip-physical-study.md), [chip architecture](../physical/chip-architecture-study.md) and [map tiles](../physical/map-tile-study.md) retain their experiments. [Results](results.md) indexes dispositions and reopening conditions; [journal](journal.md) retains dated receipts. No experimental backend is promoted by those screens. |
| How is mapping hierarchy checked? | The [matched hierarchy comparison](../physical/map-tile-study.md#explicit-hierarchy-comparison--september-25) uses identical tiled RTL and explicit flat or retained-tile policies. Exact cell ownership survives flattening and Verilog read-back. Retaining tiles saves 2.021629% of standard-cell area, with mixed address-depth effects. Use the explicit policies and checked flat views for subsequent architecture comparisons; physical locality and timing remain separate measurements. |
| What is demonstrated to a host? | [Host workflow](../host-workflow.md) includes eight kernel-certified paired uploads and independent RTL pin peers. Board transport, continuous supervision and full paired-controller refinement remain separate obligations. |

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
