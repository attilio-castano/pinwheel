# Research status

Updated 2026-10-07 after the buffered latency-one SRAM implementation, following
the storage/fetch comparison and unified owned-transfer workflow.
This page owns the **active decision and next evidence gates**. Read
[results](results.md) for conclusions, [journal](journal.md) for receipts and
linked studies for measurements and reproduction.

## Objective and current decision

Make a complete chip-design iteration possible for someone without hardware
expertise. Pinwheel's reloadable protocol engine is the test case: preserve pin
timing, capture, branching and atomic replacement while connecting one exact
implementation to formal meaning and physical feasibility. Use UART, SPI and
I²C as the main contracts and bounded new waveforms to challenge their shared
abstractions; the larger iteration also retains its declared
capacity-change gate. Competition admission remains separate.

**Delivered local capability: [four SPI modes and bounded transactions](../protocols/spi-transactions.md).**
One- and two-byte transfers keep chip select continuous. Universal Lean
reference/compiler/E64 proofs, twenty resolved-wire cases, fresh upload
certificates and independently interpreted RTL cover the stated digital scope.
The fixed five-pad mapping separates MISO observation from MOSI drive. This is
a new digital candidate; retained A's physical receipts remain historical.

**Delivered local capability: [bounded I²C writes and bus clear](../protocols/i2c-capabilities.md).**
One/two payload bytes, separate ACK flags, first-NACK STOP and nine controller
clock-release attempts have universal compiler/reference/E64 proofs. Eleven
write and twelve recovery wire cases, guarded faults, reset/reload and recovery
followed by a write on the same engine pass. Fresh chip MLIR/RTL are identical
to the SPI checkpoint; no circuitry or physical evidence changes.

**Delivered local capability: [UART supervisor and retained results](../protocols/uart-supervisor.md).**
The opt-in paired wrapper adds one enabled bit, explicit arm/stop, automatic
rearm and retain-old/drop-newest ownership with sticky overrun. Conditional
UART/E64 and exact mailbox proofs, finite resolved streams, reset/fault/ownership
controls and fresh universal circuit interpretation pass.

**Implemented formal milestone: [initialized UART package sessions](../protocols/uart-session.md).**
Actual reset, certified upload and qualified serial ARM establish the relation
from arbitrary represented state. Resident execution derives image ownership,
SRAM/core correspondence, supervisor controls and pre-edge receipts. Certified
replacement and external restart preserve exact occurrence accounting and old
packet origins; every finite lifecycle prefix has the emitted package's same
pad observations. The sufficient receive theorem includes the actual sampler
and trailing ARM edges. Fresh foundation, resolved-wire, RTL interpretation and Python gates pass on
unchanged circuit bytes; all 230 historical physical inputs are preserved.

**Implemented capability: [reusable programs and bounded register reads](../protocols/reusable-programs.md).**
Named pins, captures and labels expose existing instructions. UART/SPI programs
stay resident while accepted START carries a changing byte. A separate resident
source certificate checks the actual paired upload/dispatch sequence; local
node proofs connect START/SHIFT/KEEP to the existing graph. The one/two-byte
I²C frontend uses all sixteen captures for successful data and reports NACK or
guarded bus fault through terminal status, discarding partial captures. The
196-position bound and reference/compiler/E64 refinement are universal; image
capacity and resolved-pin behavior are checked per declared upload/scenario.
No circuit or emitter changes are allocated.

**Implemented programming layer: [bound transaction workflow](../protocols/transaction-workflow.md).**
One compile/load/run/decode API carries the request, exact program, pin and
timing requirements, result layout and capacity. Fixed SPI/I²C requests go
through a static production Lean frontend; reusable UART/SPI/JTAG use the
generic builder. Artifacts are recompiled against their request on import.
Session ownership rejects replacement/reset before START and failed decoding
preserves the unread packet. Typed resident instructions include SHIFT/KEEP,
reuse ordinary Reactive semantics and encode canonically; their local proofs
do not establish a complete initialized resident package lifecycle.

**Flexibility experiment: an eight-bit JTAG data-register fixture.**
It uses the existing three outputs, one sampled input, START operand and
captures on unchanged circuit bytes. The independent target starts in any of
the sixteen TAP states, resets, scans LSB first, updates and returns to idle.
This assumes an eight-bit DR selected by reset; it does not select an IR or
support a chain/32-bit IDCODE. A request needing a 32-bit operand or result is
refused before chip I/O: the current engine has an eight-bit START operand and
sixteen captures.

**Implemented decision: [one finite transfer owns TX, RX and completion](../protocols/buffered-transfers.md).**
Outgoing data is copied before START, receive capacity is reserved, engine access
is exclusive and terminal data stays frozen until matching release. Lean proves
local bounds/identity/retention; finite exported transitions agree with Python.
The separate reference target exercises continuous four-byte SPI and 32-bit/non-byte
JTAG scans, with independent timing/capture/framing mutations and recoverable
host waits. Current chip widths, SRAM, serial transport and emitted circuitry
are unchanged; this model does not establish their extension.

**Implemented continuation: [shared buffered reactive execution](../protocols/buffered-reactive.md).**
Buffered entry effects now compose with the existing Reactive/Fetch rules and
compact counted lookup. The same Python engine handles timed SPI/JTAG and
reactive I²C, including scratch ACK decisions, clock stretching and diagnostic
RX prefixes. Four-byte I²C uses 105 stored syntax nodes for 270 virtual positions;
it does not expand a bank or fit the existing paired image by assumption.

**First digital slice: [owned buffered SPI hardware](../protocols/buffered-hardware.md).**
An opt-in linear parallel circuit implements dedicated 32-bit TX/RX registers,
versioned writable programs, finite ownership and retained indexed readback.
Emitted RTL and saved generic/CMOS5L gates establish a measurable register-store
baseline. The retained paired SRAM/serial chip is unchanged.

**Implemented continuation: [compact counted buffered hardware](../protocols/buffered-counted-hardware.md).**
The shared timed schedule now lowers to a circuit with 64 packed leaves, two
nested repeats and up to 1,024 virtual positions. Rollover enters the next timed
leaf on the dispatch edge. Four-byte SPI uploads four rows; JTAG is a different
program on the same emitted circuit. Owned buffers, retained indexed reads and
finite identities remain explicit. Saved mapping gives an early cost check.
Typical cell area is 350,479.332 µm² with 3,860 retained state bits; this is a
64-leaf target, compared with 128 rows in the linear baseline.

**Implemented continuation: [reactive counted buffered hardware](../protocols/buffered-reactive-hardware.md).**
SPI, JTAG and I²C now load programs into the same generic circuit. WAIT,
CHECKED and QUALIFY, independent scratch and explicit branch environments
preserve the owned TX/RX lifecycle, including partial failure results. Four-byte
I²C uses 50 rows and 270 virtual positions. Saved generic/CMOS5L comparisons
retain all 9,599 state bits; typical cell area is 876,881.3004 µm². Wider uploaded
rows account for 5,632 of the 5,739 added state bits versus the timed target.
This measures a programmability cost, without establishing routed chip fit.

**Implemented comparison: [shared branch storage and fetch deadlines](../protocols/buffered-storage-fetch.md).**
A separately admitted target replaces inline descriptors with a sixteen-entry
dictionary below the same execution equations and owned-result interface.
Its declared state is 7,183 bits; programs needing more distinct descriptors
retain the inline target. Kernel rewriting/runtime correspondence, joint
upload coverage and actual fetch-deadline fixtures establish the comparison
contract. Complete mapping and replay measurements belong to the linked study.
Matched typical cell area falls 26.45% to 644,939.6310 µm², while maximum
next-state cell levels rise from 40 to 43. Full emitted wires, saved mapping
equivalence/replays and the portable foundation pass; timing remains unqualified.

**Implemented continuation: [buffered latency-one SRAM](../protocols/buffered-sram-hardware.md).**
Two replicated 64×64 instruction memories serve both prospective branch
successors. Metadata/dictionary stay in FFs; a row-zero mirror supports immediate
START. The controller declares 3,151 FF bits and preserves the shared program,
owned-result interface and waveform edges. Local kernel laws connect actual
requests, array edges, mirror and tail projection. Full hardware acceptance
passes 232 command cases and 2,311 emitted wire cases plus both saved mappings;
the 55-suite portable foundation also passes.
Typical cell area plus macro footprints is 395,524.3706 µm², 38.67% below the
shared-branch FF baseline, excluding routing/clock tree. Complete behavior relies on
finite comparison with the unchanged predecessor oracle and macro-bound RTL;
initialized loader/trace and universal native/compiler refinement remain open.

**Next decision: a concrete versioned serial command/result package.**
Carry the common load/submit/wait/read/release lifecycle to a serial boundary,
including framing, backpressure, reset, rejected uploads and retained results.
Keep image admission and one transfer owner explicit. In parallel, derive live
resident bank agreement from initialized upload coverage and compose the
selected response/metadata/dictionary with the execution relation. The current
local availability law assumes that agreement.
Actual SRAM return/address timing, physical sampling, SRAM qualification and
package power retain their distinct evidence gates. First-stage prediction is
a separate alternative and still requires synchronizer qualification.

The larger [complete design iteration](complete-design-iteration.md) remains open.
The merged contribution collects the conditional proofs, retained RTL
interpretation and physical evidence. The three remaining physical requirements
are tracked in [qualification follow-ups](../physical/qualification-followups.md),
with a [prepared upstream SRAM follow-up](../physical/sram-maintainer-followup.md).
Merging the contribution does not accept A, admit B or complete the iteration.

The user has authorized the [local iteration continuation](local-iteration-continuation.md):
portable current-A replay, fresh-source RTL interpretation and a concrete
package-power contract. The [moved-bundle replay](current-a-replay.md#recorded-local-replay)
now checks all 749 recovered inputs and freshly kernel-checks eight certificates,
with the same three physical blockers. The source interpretation passes
independently of historical mapping/admission receipts, and the checked
[power request](../physical/package-power-contract.md) names eight missing
integration/component inputs. Historical receipts and physical acceptance
criteria remain unchanged.

The filled chip retains its passing electrical, timing, full-rule GDS DRC and
package checks. The new [SRAM study](../physical/sram-extraction-results.md)
establishes a passing **351-pin exported-GDS boundary comparison** with signal
and power fault rejection. **Full GDS signoff and A remain unaccepted:** SRAM
internal extraction and layout/schematic qualification still fail. The new
[comparison policy](../physical/sram-comparison-results.md) now qualifies all four
unchanged context fixtures in both extraction modes, with explicit physical
port ownership and defect rejection. The subsequent
[macro integration](../physical/sram-integration-results.md) preserves all
351 ports and four array levels but exposes eight remaining failing circuit
types. The [complete tile diagnostic](../physical/sram-tile-results.md) now
isolates a source/physical resistor-width disagreement: 0.260 versus 0.200 µm.
An explicitly edited diagnostic matches completely; the supplied tile and
macro's cross-block connections remain unqualified.

The [provenance investigation](../physical/sram-trust-results.md) confirms all
seven supplied views and the simulation dependency match one pinned release.
The width discrepancy predates Pinwheel. The linked reference deliberately
abstracts SRAM internals; the new native boundary controls demonstrate both
wiring-fault sensitivity and blindness to an internal width edit. The
[component contract](../../physical/fixtures/sram-trust/contract.json) proposes
an explicit premise for further formal work. It is not a production admission
rule, and external physical qualification remains open.

The first [conditional paired proof gate](../storage/paired-formal-correspondence.md)
now connects the actual shared graph, retained validation optimization and
package adapters to an explicit SRAM contract. It proves legal memory modes,
active-bank SRAM preservation and agreement with the graph model before and
after every edge. It allows arbitrary initial memory and adds no global axiom.
The default build, whole-library audit and focused controls pass; fresh core,
package and interface artifacts are byte-identical to the retained mapping
inputs.

The subsequent [upload gate](../storage/paired-upload-coverage.md) proves that
every valid active bank matches a complete 290-word accepted transcript, through
arbitrary decoded commands after initialization. It covers all parameter
registers, SRAM rows, boot and idle metadata; incomplete uploads preserve the
active image. A certificate for that transcript now describes the stored image.
Enabled reads of a valid image return the row for the token installed on the
edge. The retained-controller theorem keeps the SRAM law explicit and permits
arbitrary initial storage. The library audit, adversarial upload controls and
retained emission identity pass. The subsequent timed gate is described below.

The [running-state gate](../storage/paired-runtime-ownership.md) now connects
the current instruction, cached parameter and usable SRAM response through
every initialized command history. A certified active image supplies the
current source instruction and the successor selected on an actual dispatch
edge. The controller refreshes Q on every edge whose result is running;
stopped states may hold stale Q. Finite tests agree with the reference on
100 edges across both banks; the subsequent timed gate now derives dispatch
times and branch choices from the reference.

The [timed execution gate](../storage/paired-timed-execution.md) proves
cycle-for-cycle agreement of the retained controller's public execution state
with E64: mode, PC, both counters, all samples, and pin levels/enables. It derives
capture ordering, branch choices, guard priority, wait deadlines and qualification
retries from the actual graph. Initialization and certified accepted-upload
coverage establish storage ownership from arbitrary prior state; a reset
establishes the execution relation. Every subsequent finite history is covered
under the explicit SRAM law, with no reinitialization or command 3 during that
program segment. The subsequent package/lifecycle gate below establishes the
relation at commit and composes it with host observations. Hardware and physical
acceptance are unchanged. The focused gate passes the complete library audit
(8,585 theorems), 686 new before/after edge comparisons and eight live mutation
controls; fresh hardware artifacts match the retained mapping inputs.

The [package and host lifecycle gate](../storage/paired-host-lifecycle.md)
connects that result to the retained pin map, two samplers, serial receiver and
mailbox. Three reset-low edges initialize arbitrary state; any later accepted
commit of a certified staged transcript establishes the E64 relation directly.
The normal commit/start sequence needs no additional reset. Every package
output agrees before and after each execution-segment edge, including retention
of an unread result across certified replacement. Qualified serial delivery is
connected to the actual consumed stream. Loader status retains its graph
interpretation. The subsequent admission gate below discharges certified-upload
success; physical qualification is separate.
The fresh gate passes in **199.413 seconds**: **8,696 audited theorems**,
**794 package pin-edge pairs**, three rejected corruptions and unchanged
hardware artifacts. No CAD calls or hardware edits occur.

The [certified upload-admission gate](../storage/paired-upload-admission.md)
now derives acceptance for every qualified begin/290-word/commit session of a
certified image. The first 32 accepted words install the inactive parameter
table used by actual row validation; accepted-prefix ownership carries the
proof to commit. Arbitrary quiet gaps are allowed. From arbitrary represented
state, three reset-low samples and two idle release samples prepare the actual
package; qualified serial delivery then establishes E64 execution and host
observations without an extra reset after commit. Stopped initialized
replacement is covered by the decoded/package upload theorem. The SRAM law,
digital delivery contract and execution-segment rule remain explicit.
The fresh gate passes in **235.829 seconds**, with **8,757 audited theorems**,
**580 accepted pushes**, **168 quiet edges**, four executed refusals and two
wrong-source certificate rejections. Fresh hardware artifacts retain their
identities; no hardware edit or CAD call is required.

The initial [combined acceptance report](implementation-acceptance.md) bound the
eight concrete host certificates, conditional proof, emitted circuit, scoped
implementation checks and final physical candidate. The host's original paired
RTL connects to the proved validation-isolated RTL through the recorded SAT
comparison. Subsequent mapping and physical checks connect to the exact filled
netlist and GDS. Fresh structural comparisons account for the five buffers,
declared protection diode and signal-free finishing cells. **At that checkpoint A
remained unaccepted:** SRAM qualification, compatible fast conditions, typed-circuit-to-RTL
correspondence and package power qualification are explicit blocking rows.
The intake checks **572 input files / 58 evidence connections** and rechecks all
**eight host certificates** in **111.130 seconds**. All **17 refusal tests** pass
normally and under optimized Python. No CAD calls or physical edits occurred.

The subsequent [RTL interpretation gate](../storage/paired-rtl-interpretation.md)
now connects both exact retained emitted modules to their typed components and
the certified upload/E64 session theorem. It covers all **81 controller and 110
package register fields**, **44 output fields** across both modules, and **1,082
local equivalences**. Both compiled-environment audits allow only Lean's standard
axioms. Six actual RTL corruptions and two injected axioms are rejected; both
unchanged reimports pass. The fresh run takes **315.149 seconds**. The Yosys
frontend/lowering and restricted interpreter remain explicit trust boundaries.
The refreshed acceptance intake consumes this proof and these exact RTL bytes:
**the formal interpretation row passes; A remains blocked by SRAM qualification,
compatible fast conditions and package power qualification.** No physical-design
run or hardware edit is involved.

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
| Reduced SRAM fixtures | All four fixtures pass deep and flat: complete driver has 64 MOS devices / 34 ports; complete delay has 28 MOS devices / six separate resistors / four ports. All 42 defect checks reject. Full SRAM remains unqualified. |
| Hierarchical SRAM integration | Reproduced failure: 23 matching types, eight nonmatches, 19 skipped parents including the macro. All 351 physical ports and array multiplicities survive. Both sides contain 215,806 MOS devices; count equality does not prove wiring. |
| Complete 32-bit tile diagnostic | Source refuses: 96 resistor widths disagree with geometry. Changing three width tokens in a separate diagnostic yields 288 device / 182 net / 42 port matches in both modes, without ambiguity. All 42 fault comparisons reject. Supplied tile remains unqualified. |
| SRAM provenance / abstraction coverage | Seven views plus behavioral dependency match the pinned PDK. A 351-pin abstract fixture matches and rejects signal/power faults; an internal width edit is invisible. Native GDS abstraction still reports 23 overlaps and 518 conversion diagnostics. |

The original extra ground terminal belongs to the raw ground equivalence class
and disappears when control hierarchy is imported consistently. The adapter
changes 338 bus-pin spellings and preserves every pin and connection. No ground
alias or terminal deletion is applied. Flattening all SRAM internals removes all
24 original overlap errors in isolation, but full-flat chip extraction times out.
The cheaper control import permits boundary LVS while leaving internal errors;
its blackbox pass cannot hide those failures.

The [reviewable recipe](../../physical/fixtures/sram-comparison/README.md) binds
ports from original top-owned labels and extracted metal at their positions,
reconciles only the small netlists' hierarchy, and retains every dimensional
resistor and declared port through preparation. Its private deck copy changes
one comparison file; extraction geometry and installed PDK remain unchanged.
The final replay passes eight fixture comparisons and two unchanged-carrier
comparisons, rejects 42 injected defects, and refuses eight incomplete-evidence
cases. Six ambiguous internal net pairs remain in each complete delay result;
all devices and declared pins match. Unique dummy-instance net identity is not
claimed.

**Correction:** six matches in the earlier context report were database matches
with a failing final native port check. The new study audits all 24 earlier
invocations and retains their raw receipts. With physical ports recognized,
a new ablation also demonstrates a real final-native false positive when
disconnected-output safeguards are removed. The retained recipe refuses it.

The [integration diagnostic](../../physical/fixtures/sram-integration/README.md)
adds explicit layout/schematic name correspondence and expands only the admitted
driver/delay families. The prior near-flat macro arose during comparison
alignment, not extraction. The new recipe preserves two matrices, 128 columns,
1,024 tiles and 32,768 bit cells. All 548 macro label positions bind consistently
to 351 distinct connected nets. Eight remaining circuit mismatches prevent a macro
comparison; the full device census alone cannot verify the expanded blocks'
connections. A packaged replay reproduces the same failure and audit.

The [tile recipe](../../physical/fixtures/sram-tile/README.md) preserves the
whole source hierarchy and physical context, reconciles ownership inside its
netlists and retains all resistor dimensions and 42 physical ports. Its 96
markers measure 0.200 × 0.600 µm while source CDL says 0.260 × 0.600 µm.
The strict adapter refuses the original. A separate width-corrected diagnostic
passes deep and flat; restoring original widths fails. The packaged run also
rejects 42 defects, seven incomplete-evidence cases and 13 adapter faults.

**Next: obtain component evidence and a qualified integration boundary.** The
[qualification assessment](../physical/physical-qualification-assessment.md)
audits nine libraries against the pin and current upstream inventories. The
captured development tree supplies no new fast pair. The current unmerged
SRAM proposal retains the width discrepancy and adds bit-cell layer annotations
that appear inconsistent with the physical witnesses. Both issues need an
authoritative component interpretation or characterization.

The [power sensitivity study](../physical/power-boundary-results.md) now
reproduces the retained rail drops and exposes their boundary assumptions:
7,912 VDD and 7,832 ground sources. Four audited contacts per rail increase the
conservative combined loss from **0.542 to 8.636 mV** with unchanged default
activity. At those contacts, illustrative 1/10 Ω resistance per source node
raises loss to **12.635/47.225 mV**. Three checked finite workloads draw
**6.817–7.029 mW** in the nominal model; the highest, replacement, gives
**36.620 mV** with 10 Ω feeds. All 38,497 signal pins are annotated. Three earlier
zero-annotation runs are explicitly rejected despite successful tool exits.
No connected waveform bit is unknown after both banks are initialized.

The remaining power gate needs actual parent supply geometry, source tolerance,
external impedance and an applicable activity/voltage envelope. The recorded
values are sensitivities, not package values or a bound over every program.
The nominal study does not qualify slow-corner headroom or transient droop.
The [acceptance report](implementation-acceptance.md) retains its passing RTL
interpretation row and all three physical blockers; A remains unaccepted.

For physical acceptance, obtain exact-version qualification or a documented
source/deck interpretation before changing the strict tile contract. The
[prepared maintainer report](../physical/sram-maintainer-report.md) is unsent.
Historical commercial LVS evidence supports investigating this route but is
not a report for our exact inputs. Further independent internal verification
would still need the recorded edge/control contexts and a passing macro
positive control before cross-block wiring-fault claims. Keep the filled chip
and all failed receipts; no error waiver or width correction is adopted.

The tile continuation cost **86.455 CAD seconds**. The new provenance and
abstraction continuation adds **21.779 CAD seconds**, including the failed
first probe and cleanup. The power study adds **430.957 CAD seconds**, including
all setup failures and rejected activity runs. Campaign total is now
**8,843.120 seconds / 147.39 minutes** of eight hours. The
[power manifest](../../physical/experiments/power-boundary-results.json) binds
the measurements, complete-annotation gate and resource ledger. The
[provenance manifest](../../physical/experiments/sram-trust-results.json)
records source history, three bounded invocations and the boundary-coverage
controls.
Three A full-routing attempts remain used and two B attempts reserved; no
additional A slot, chip edit or installed-PDK change occurred. The
[tile manifest](../../physical/experiments/sram-tile-results.json) binds four
bounded invocations, the original refusal, causal comparison, controls and
independent audit. An auxiliary local fault-area reporting error is corrected
by separate GDS readback; whole-tile geometry checks and verdicts remain valid.
Earlier fixture and integration evidence remains separately recorded.

The fast library audit still finds standard cells at −40°C and SRAM at −55°C,
with no compatible delivered fast pair or established conservative bound.
Conditional certified-upload admission and timed package refinement now pass;
source-to-GDS correspondence remains open. Power-grid
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
| Semantic reference | Unrestricted two-read flip-flop chip preserves the edge contract; hybrid SRAM has an initialized array/controller proof. Certified delivery through paired package execution is now proved under explicit digital and SRAM premises. | [Storage and execution](../storage-primitives.md#closed-loop-hybrid-execution-2026-09-21) |
| Experimental execution candidate | One 512×64 SRAM, 256 positions/32 canonical records and 290-word images. Certified upload admission, actual storage, timed E64 execution and package/result lifecycle are proved under explicit premises. | [Admission/session proof](../storage/paired-upload-admission.md) |
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

1. **Qualify the supplied SRAM.** Resolve the exact-version width
   interpretation or obtain applicable component evidence. Independent internal
   verification still needs the remaining contexts and a complete macro positive
   control before cross-block fault claims. The prepared maintainer report remains
   unsent; the interpreted session theorem retains the explicit memory law.
2. **Qualify fast conditions and package power.** Obtain compatible logic/SRAM
   characterization or a justified conservative timing bound, then connect the
   power analysis to qualified package sources and an activity envelope. The
   [completed sensitivity study](../physical/power-boundary-results.md) supplies
   the saved-layout evaluator; the checked
   [package-power request](../physical/package-power-contract.md) assigns the
   eight absent input classes, typed values and stop criteria. The
   [updated intake](implementation-acceptance.md) keeps these separate from the
   now-passing formal interpretation row. Preserve the candidate while collecting
   qualification evidence.
3. **Establish physically feasible A and its correspondence.** Apply the
   [bounded plan](complete-design-iteration.md) to the retained filled candidate
   and close its physical acceptance obligations. Its interpreted emitted RTL
   already composes certified upload and E64 package execution; scoped mapping,
   cell-function and connectivity checks retain their separate boundaries.
   All three allocated A routes are used. Historical results from other backends
   do not transfer. Record exploratory size overages separately.
4. **Repeat for a meaningful capacity change.** Increase distinct record capacity
   from 32 to 64 while retaining 256 positions, atomic replacement and execution
   timing. Require the same behavioral and physical gates; record image-format,
   area and implementation consequences explicitly.
5. **Demonstrate a reproducible design iteration.** The current-A assessment
   now replays from a movable, hash-checked source/evidence bundle. This retains
   physical observations rather than rebuilding them. Recover both accepted A/B
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
| What is demonstrated to a host? | [Host workflow](../host-workflow.md) includes eight kernel-certified paired uploads and independent RTL pin peers. [Initialized UART sessions](../protocols/uart-session.md) now compose the supervisor through actual upload/ARM and its declared finite lifecycle. Board transport and physical qualification remain separate obligations. |

The fast-screen standard-cell and SRAM temperatures remain mismatched. The
20% connection reserve and 0.3% area increment are **experiment comparison
rules**, not organizer requirements. Pin-level RTL and mapped-corner checks
cannot establish extracted timing, electrical or board behavior. Historical
ignored `build/` artifacts may be absent in a fresh checkout; tracked manifests
identify their original reports but cannot reconstruct them.

## Stable constraints and deferred work

<a id="the-official-outline-2026-09-18"></a>

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
resident-payload workload now exposes existing SHIFT/KEEP with source
certification and package tests; universal initialized resident protocol
composition and physical promotion remain open. Preserve the tested digital sampling conditions: SPI requires
`d + tco ≤ halfCycles`; I²C requires `d ≤ phaseCycles` and `d < waitCycles`.
These digital bounds do not establish analog sampling behavior. Root licensing,
publication and submission remain separate decisions under the
[submission plan](../submission-plan.md).
