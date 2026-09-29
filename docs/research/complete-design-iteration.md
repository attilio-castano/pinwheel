# Complete design iteration

Plan dated **2026-09-26**, following the user's request to organize autonomous
work around complete design iterations. **Status: execution authorized; milestone
0 is recorded in the [acceptance audit](design-iteration-acceptance.md); the
[first detailed layout](../physical/design-iteration-experiment.md) and
[paired image/host integration](../storage/paired-image-certificate.md) have
executed. A is not yet accepted.** [Research status](status.md) owns the
active milestone; this page owns the execution sequence and completion criteria.

The initial physical allocation has reached its three-configuration limit.
One full-flow attempt and two completed calibrated alternatives consume a
conservatively charged **2,640.603 CAD seconds (44.01 minutes)**, including
controls, failed work and independent checks. The remaining A full-flow attempt
is preserved because neither alternative passes its screen. The
[campaign manifest](../../physical/experiments/design-iteration-results.json)
records the incomplete outcomes and the next architectural hypothesis; this is
not completion of the A/B design-iteration plan.

The user subsequently authorized one
[validation-lookup isolation experiment](../physical/validation-isolation-experiment.md).
It keeps the same total CAD budget and remaining full-flow attempt. The opt-in
circuit passes a kernel-only local proof, complete emitted-core/package SAT,
mapped and actual-physical equivalence, and pin traces. The SRAM-to-rejection
path disappears for 6.12% additional mapped area. Its measured unrepaired coarse
layout retains 8,911 overflow and −9.287 ns slow setup; the subsequent repair was
stopped. Retain the architectural result and investigate physical control
distribution. The second A full-flow attempt remains unused. This extension
does not complete A, B or the full correspondence chain.

The approved [balanced-distribution continuation](../physical/buffer-balance-experiment.md)
preserves that RTL and every nonbuffer mapped connection. It clears initial
coarse overflow, with only 0.2376% additional mapped area. Completed repair
reaches +0.820730 ns slow setup and +0.040186 ns fast-screen hold, but four
capacitance and 23 slow slew violations on seven nets remain. Both actual
physical circuits pass independent equivalence, pin replay and geometry checks.
The fast-view mismatch is still open. Cumulative charge is **4,357.451 CAD
seconds**; the second A full-flow attempt remains unused. Retain the candidate
for bounded electrical closure, without treating this screen as accepted A.

The subsequent [seven-net electrical repair](../physical/balanced-electrical-experiment.md)
clears all coarse electrical violations for seven buffers and 96.1632 µm².
The [second allocated A layout](../physical/balanced-detailed-experiment.md)
completes detailed routing, extraction, full-rule Magic DRC, LVS, antenna and
power connectivity with **+1.451337 ns** slow setup and **+0.020742 ns**
fast-screen hold. Independent final-circuit checks and pin replay pass.
**A remains unaccepted:** 14 fanout failures arise from added antenna loads and
one separate net exceeds capacitance. Fast characterization and full paired
refinement remain open. Both A full-flow attempts are now used; cumulative
charge is **4,926.281 CAD seconds**. A further physical experiment needs an
explicit allocation. B remains behind A's acceptance gate; unused aggregate
time does not reset attempt limits. The new shared all-corner timing gate rejects
this layout even though the native flow exits successfully.

On September 27 the user approved a bounded antenna-load follow-up, adding one
A full-flow slot while preserving the two B slots and eight-hour aggregate limit
(three A plus two B at most). Its single [coarse candidate](../physical/antenna-load-results.md)
is rejected before detailed routing: lower receiver counts leave two parent
wires above the capacitance limit. Circuit, timing and resource checks pass; the
additional A slot remains unused. Cumulative charge is **5,052.680 CAD seconds**.
The frozen one-candidate allocation is closed; [status](status.md) owns the next
plan. The original four-attempt envelope below is expanded only by that extra
A slot; the aggregate, per-run and tool-repair limits remain unchanged.

The subsequently approved [transport refinement](../physical/transport-split-results.md)
repairs those two parent wires and passes coarse admission for **29.0304 µm²**.
The third A layout completes and preserves both repairs after extraction. Final
slow setup is **+1.229028 ns**, fast-screen hold **+0.026968 ns**, and the stated
layout/circuit checks pass. All previous 14 fanout failures clear, but four other
nets gain excess antenna inputs; one separate wire-heavy cap failure remains.
Native all-corner cap enforcement and the shared gate correctly reject A.
**All three A slots are now used**, with cumulative charge **5,652.722 CAD
seconds / 94.21 minutes**. The next proposed scope is complete-network protection
and electrical closure; another A full route requires a new explicit allocation.
Two B slots remain reserved behind accepted A, and the formal/fast-view/replay
obligations are unchanged. Earlier attempt counts above are dated receipts.

The next authorized [closure assessment](../physical/protection-closure-results.md)
costs blanket reserve and tests the existing native electrical repair command
after antenna insertion. A four-receiver additive policy requires at least 1,949
buffers before physical costs. The restarted process reproduces the five final
failures but crashes on router state absent from its initialization sequence.
No candidate is produced. Qualify the transition with live routing state on a
small fixture before another full route. The assessment adds **10.648 CAD seconds**
for **5,663.370 seconds cumulative**; all three A slots remain used, with no new
full-flow allocation. This advances the flow-integration diagnosis, not A's
physical or formal acceptance.

The authorized [live repair fixture](../physical/live-closure-results.md) now
passes a complete local repair/reroute/extract/check iteration. Explicit
protection grouping and four native wire repeaters clear all three fixture
corners while retaining circuit identity, placement, clocks and power bindings.
The prepared chip intake names the five remaining electrical targets, all 97
antenna cells and 340 clock nets. Qualify its runtime repair-tree coverage and
protection groups before another full chip attempt. This continuation adds
**26.259 CAD seconds**, for **5,689.629 cumulative**. All three A slots remain
used and both B slots reserved. The result advances the integration mechanism;
it does not complete chip acceptance or the paired Lean refinement chain.

The subsequent [chip integration](../physical/chip-closure-results.md) now passes
on the actual saved third A layout: five buffers and one diode clear all three
corners after fresh extraction, with +1.242753 ns slow setup and +0.026979 ns
fast-screen hold. Original placements, 97 existing antenna bindings and all 340
clock routes are retained. Native DRC/antenna, exact edit checks and 331,401 pin
edges pass. A rejected control with three missing clock wires establishes the
need for independent route and parasitic coverage alongside violation reports.

The next gate is final fill/streamout, full-rule DRC/LVS, power/connectivity and
final extracted timing on this exact candidate. Fast-view qualification and
complete paired refinement remain. This continuation adds 634.894 CAD seconds,
for **6,324.523 seconds** cumulatively. No fourth A full-flow attempt was
allocated; three A slots are used and two B slots remain reserved. Local chip
integration does not complete accepted A, B or clean-source replay.

The subsequent [final layout checks](../physical/chip-finalization-results.md)
finish the repaired circuit without changing any original instance or wire.
Fresh electrical/timing, full-rule GDS DRC, antenna, power connectivity and
331,401 pin edges pass. **Final signoff is rejected:** GDS extraction reports 24
illegal overlaps and LVS fails. Matched pre-repair and standalone SRAM controls
reproduce all overlap boxes; pin spelling and an extra internal ground terminal
identify a focused SRAM extraction/interface gate. Earlier passing LVS used
DEF/LEF and does not close this gap. The continuation costs **387.202 CAD seconds**,
for **6,711.725 seconds** cumulatively, without another full-routing A slot.
Fast characterization, complete refinement, accepted A/B and replay remain open.

The [SRAM interface continuation](../physical/sram-extraction-results.md) now
passes a 351-pin GDS boundary comparison and rejects deliberate signal/power
wiring faults. All supplied macro geometry and labels survive streamout. The
SRAM remains a schematic blackbox: two Magic overlaps, 438 conversion diagnostics
and the independent internal LVS failure prevent final signoff. Full-flat
controls time out within their declared limits. That continuation costs
**1,316.754 CAD seconds**, for **8,028.479 seconds** cumulatively. A/B, fast-view
qualification, complete refinement and replay remain open.

The [context-fixture continuation](../physical/sram-context-results.md) isolates
the two failing cells in their complete local neighborhoods. All 64 driver
transistors match flat; deep extraction assigns the NMOS devices to the parent.
A dimension-preserving resistor-model translation passes the complete delay
parent deep, with physical and dimensional fault rejection. Flat delay comparison
still combines resistors inconsistently; the database comparison also matches a
disconnected declared output until the explicit fixture pin-use guard rejects it.
The later final-verdict audit corrects six database-only matches, including the
flat driver parent and that output control: their native port checks failed.
No further chip route is allocated. This continuation
costs **39.179 CAD seconds**, for **8,067.658 seconds** cumulatively; acceptance
and the remaining formal/physical gates are unchanged.

The [comparison-policy qualification](../physical/sram-comparison-results.md)
then passes all four unchanged fixtures in both modes. It binds ports from the
original top-owned physical labels, reconciles the small netlists' hierarchy,
preserves each dimensional resistor and guards the complete final verdict.
Its packaged replay has ten positive comparisons, 42 defect rejections and
eight incomplete-evidence refusals. A controlled ablation now demonstrates a
real native pass for the disconnected-output fault when safeguards are removed.
Six ambiguous internal dummy-net pairs per complete delay result are retained;
devices and declared pins match. This adds **198.128 CAD seconds**, for
**8,265.786 seconds** cumulatively.

The bounded [hierarchical integration](../physical/sram-integration-results.md)
then preserves all 351 physical ports, two matrices, 128 columns, 1,024 tiles and
32,768 cells. Explicit name correspondence prevents comparison alignment from
flattening the array. Scoped driver/delay expansion preserves devices and
parameters, but eight other circuit types fail and the macro comparison is
skipped. Both sides contain 215,806 MOS devices after preparation; that census
does not establish wiring equivalence. The packaged replay reproduces the same
negative result. Four invocations add **38.143 CAD seconds**, for **8,303.929
seconds** cumulatively. Next qualify the complete 32-bit tile's ownership and
96 metal2/metal3 resistor interpretations, then the recorded edge/control
contexts. A passing macro positive control precedes cross-block fault tests.
Full signoff, fast compatibility, timed refinement, accepted A/B and replay
remain open; no additional A route or chip edit occurred.

The subsequent [32-bit tile diagnostic](../physical/sram-tile-results.md)
reconciles bounded hierarchy ownership but finds a dimensional disagreement:
96 physical resistor markers have 0.200 µm width while source CDL declares
0.260 µm. A separate diagnostic changes only three repeated width tokens, then
applies the checked metal2/metal3 model translation. Both extraction modes
match all 288 devices, 182 nets and 42 ports without ambiguity; original widths
still fail. The packaged controls reject 42 faults, seven incomplete-evidence
cases and 13 adapter faults. The supplied tile remains unqualified.

Resolve that exact source/physical width contract before promoting the tile
or extending its interpretation to the macro. The counterfactual pass supports
causal diagnosis, not adoption of an unsupported reference change. Four bounded
invocations add **86.455 CAD seconds**, for **8,390.384 seconds** cumulatively.
No chip/installed-PDK change or additional A route occurred. Remaining contexts,
macro wiring, fast views, timed refinement, A/B and replay retain their gates.

The [provenance and trust-boundary investigation](../physical/sram-trust-results.md)
then verifies that all seven SRAM views and the simulation dependency match the
same pinned PDK. The source/geometry width discrepancy already exists in 2023.
The linked reference uses macro abstraction; our native probe retains 351
terminals but omits the macro's internal circuit and retains import diagnostics.
A bounded boundary comparison rejects signal/power faults and deliberately
fails to detect an internal width edit. Historical upstream commercial LVS
evidence supplies a possible component-qualification route, not an exact-input
certificate.

The next design-iteration work separates two obligations: complete paired
controller/loading/package correspondence under the
[explicit memory contract](../../physical/fixtures/sram-trust/contract.json),
and physical qualification of that supplied component in its permitted
environment. The contract is proposed and is not a new global Lean axiom or
production admission override. The [maintainer report](../physical/sram-maintainer-report.md)
is ready but unsent. Conditional formal work need not wait for independent
reverse engineering of every memory cell. Physical admission still requires
its exact-version evidence, compatible timing corners and the existing gates.
Three bounded invocations add **21.779 CAD seconds**, for **8,412.163 seconds**
cumulatively; all chip and PDK inputs remain unchanged.

The first [conditional correspondence gate](../storage/paired-formal-correspondence.md)
now proves graph construction, retained validation equivalence, package adapter
composition, legal SRAM modes and active-bank SRAM preservation. Under an
explicit memory behavior premise, the retained typed package and the graph
model agree before and after every clock edge. This permits arbitrary initial
state; it does not promise E64 behavior before a qualified upload. The proof
audit and focused checks pass, with byte-identical retained hardware IR and no
CAD cost.

On September 28, the subsequent [upload gate](../storage/paired-upload-coverage.md)
establishes loader coverage and committed-image agreement for arbitrary decoded
command histories after initialization. A valid bank contains the complete
accepted transcript across all 32 parameters, 256 SRAM rows, boot and idle
metadata; the image certificate therefore describes actual storage. Inactive
updates preserve the prior active bank. Enabled reads return the loaded row for
the token installed on that edge, under the same explicit SRAM law. The complete
library audit and retained-controller controls pass with unchanged hardware IR
and zero CAD calls. The next formal gate is usable Q and cached parameters
through every execution edge, followed by timed E64 behavior and composition
with the package and host-delivery conditions. Physical qualification and
complete iteration acceptance remain open.

The subsequent [running-state gate](../storage/paired-runtime-ownership.md)
establishes current-token, cached-parameter and SRAM-response ownership for
every initialized history, including transfer to the retained controller under
the explicit memory law. A certified transcript identifies the running source
instruction and the successor selected by an actual dispatch. The graph reads
SRAM on every edge whose result is running; stopped Q may remain stale. Finite
controls compare 100 edges with the independent E64 reference across both banks
and reject stale-response, parameter and token corruptions. Full timed control
refinement remains next: derive dispatch/branch decisions and preserve the
reference's counters, samples and pin commands, then compose with package and
host delivery. Hardware and physical acceptance are unchanged; no CAD calls.

The subsequent [timed execution gate](../storage/paired-timed-execution.md)
closes that control and observation gap for a certified program segment. Every
before/after edge of the retained controller agrees with E64, including captures,
branches, wait/qualification timing, counters, reset and pin commands. The
initialized-segment theorem starts with arbitrary storage, uses the actual
accepted transcript certificate, and establishes its initial execution relation
with a reset. It then admits arbitrary finite histories without initialization
or command 3. The SRAM law remains explicit. The next formal gate connects this
result to the package, result observer and host lifecycle, including whether
commit itself establishes the relation before start and how certified program
replacement composes. Physical qualification and complete A/B acceptance remain
separate; no CAD calls or hardware changes were needed.

The subsequent [package/lifecycle gate](../storage/paired-host-lifecycle.md)
closes the accepted commit/start boundary and carries E64 through the actual
samplers, serial receiver and result observer. Three sampled reset-low edges
initialize arbitrary state; later certified accepted commits establish the
execution relation without another reset, including replacement with an unread
mailbox. Qualified delivery refers to the actual consumed command stream.
The subsequent admission gate below discharges the accepted-commit and
staged-transcript premises for a qualified upload of a certified image. Physical
SRAM, fast-view, source-to-GDS and A/B acceptance remain separate; no hardware
edit or CAD call occurs.

The [certified admission gate](../storage/paired-upload-admission.md) completes
that conditional digital session: reset/release, qualified serial upload,
accepted storage and commit, then timed E64 package observations. It derives
validation from the source certificate and the actual installed inactive
parameter table, with arbitrary quiet gaps. Stopped initialized replacements
use the same argument. The next integration gate should bind the host/source
certificate, this proof, emitted implementation and retained physical evidence
into one reproducible acceptance report. Keep missing SRAM and compatible fast
qualification visible as refusals; this result adds no route allocation or
physical acceptance.

The [combined acceptance report](implementation-acceptance.md) now supplies that
integration gate. It rechecks eight concrete host certificates, binds the
conditional proof's source and emitted artifacts, follows scoped SAT comparisons
through mapping and the implemented circuit, and reproduces the final repair
and finishing connections from retained readbacks. Actual timing and component
identities are checked separately. A remains unaccepted for SRAM qualification,
compatible fast conditions, typed-circuit-to-RTL correspondence and package power
qualification. The next independently actionable formal gate is the paired
artifact interpretation; the report adds no hardware change or CAD allocation.

That [interpretation gate](../storage/paired-rtl-interpretation.md) is now complete
for both retained raw RTL modules. Total component equality and session
composition pass with standard axioms only; actual RTL faults are rejected.
The refreshed intake retains the same candidate and advances the formal row to
passed. SRAM qualification, compatible fast conditions and package power remain
blocking requirements. The next useful work is to qualify those physical
assumptions; a capacity change still requires A's acceptance gates.

The bounded [physical qualification assessment](../physical/physical-qualification-assessment.md)
now distinguishes provider dependencies from a local power experiment. Nine
library files retain the same bytes in the captured development tree; no new
compatible fast view is available there. The current SRAM proposal leaves the
width discrepancy and raises a layer-annotation question. Power needs explicit
source geometry, external impedance and activity before the saved layout can
be evaluated against a justified voltage budget. The source/inventory replay
adds no CAD, and all three acceptance blockers remain. Provider questions and
the power experiment's admission/exit conditions are recorded in the study.

The [power experiment](../physical/power-boundary-results.md) is now complete
as a sensitivity study. Four audited contacts per rail raise default modeled
loss from 0.542 to 8.636 mV; illustrative 10 Ω feeds raise it to 47.225 mV.
Checked idle/replacement/execution traces fully annotate 38,497 signal pins.
Replacement is highest among these observations at 7.029 mW and gives 36.620 mV
loss with 10 Ω feeds. Rejected zero-annotation runs are preserved. Actual parent
geometry, supply tolerance/impedance and an applicable activity/voltage envelope
remain required. The 430.957-second continuation adds no routing attempt;
campaign cost is 8,843.120 seconds. This advances the evaluator without waiving
SRAM, fast-condition or package qualification.

## Outcome

Make one complete, reproducible path from a declared chip requirement to an
interpreted and checked circuit, a physically validated layout, and an
understandable account of its costs. Then exercise that path with a meaningful
requirement change. The user supplies behavior and constraints; the agent handles
implementation choices and explains measured tradeoffs.

Three outcomes must hold together:

1. **A physically feasible reference:** complete the physical flow under a
   declared platform and validated timing assumptions.
2. **Evidence for that same implementation:** connect its program representation,
   controller, package, emitted RTL, mapped logic and physical netlist. Do not
   borrow a proof from a different backend.
3. **A second design through the same process:** a requirement change reaches
   the same verification and physical gates without a separately hand-built flow.

This is a pre-silicon milestone. Competition fit and measured silicon behavior
remain separate outcomes. An explicitly oversized experimental layout can meet
this milestone, but cannot be described as fitting the pinned competition tile.

## The two design briefs

**A: establish the reference.** Start with the paired controller: 256 logical
positions, 32 distinct canonical E64 records, two atomic program banks and the
existing pin, capture, branching, reset, replacement and result semantics.
Retain the 20 ns clock and existing I/O timing/load assumptions. Its current
290-word experimental image format must be integrated with the host path and
identified explicitly; it is not the older backend's raw upload format.

The retained `route-import-fix-01/candidate` is the first physical checkpoint,
not an irrevocable architecture selection. Its actual source/candidate identities
are in the [route-import manifest](../../physical/experiments/route-import-fix-results.json).
The earlier proved backend remains a semantic reference, not a substitute proof
for this checkpoint. Local availability and source correspondence need auditing
before any old receipt is reused.

**B: increase useful capacity.** Support 64 distinct canonical E64 records while
retaining 256 positions, atomic replacement, the operation set, clock and exact
execution-edge behavior. This is a hardware change, not another program loaded
into the same chip. All A programs must retain their observable behavior after
recompilation; B must also exercise programs that need more than 32 distinct
records and more than 32 distinct parameter entries.

The initial implementation hypothesis is a 64-entry parameter bank and a
six-bit parameter index. The present 32-bit token has two reserved bits, so this
is a plausible encoding change, not a proof of feasibility. With the same upload
organization, B would use 64 + 256 + 2 = 322 words. Derive and check that layout;
do not confuse its length with the unrelated older 322-word image format. Host
encoding and hardware admission must agree on an explicit format identity.

Capacity is the requested difference. Floorplan, cell count, routing and area
may change as implementation consequences, and must be reported. Do not silently
relax the clock, introduce protocol cycles, narrow supported programs or remove
timing paths to obtain a passing result.

## Milestone 0: make the contract and remaining work concrete

Produce one concise acceptance table for A, with links to existing evidence and
each missing obligation. Separate behavioral requirements, actual electrical and
layout limits, competition size, and optional experimental margins. In particular,
the 20% reserve and old 0.3% incremental area allowance are not definitions of
correct operation. Reclassifying them does not change historical verdicts.

Audit the exact saved candidate, generation/mapping receipts, current source,
tool/PDK inputs, final-flow check availability, and existing proof interfaces.
Check whether the saved physical netlist can be reproduced from declared inputs
and recipes. A stale or missing artifact requires a new receipt, not attribution
of an old result to new source. Preserve the existing uncommitted campaign work.

Resolve the current fast-corner cell/SRAM temperature mismatch before claiming
all-corner closure. Use compatible characterized views or establish a justified
conservative evaluation. A missing qualified view remains a blocker; editing a
temperature label is not a fix. Inventory the actual DRC, LVS, antenna, extraction
and power-connectivity checks; do not count disabled checks as passes.

**Exit:** a frozen design brief, proof-obligation map, physical acceptance table,
reproducible input inventory and a ranked list of actual blockers. Select the
smallest discriminator for the first blocker. No broad sweep is needed.

## Milestone 1: establish physical feasibility for A

Use the existing target preparation, bounded runner, checkpoint, readback and
reporting machinery. Diagnose the retained 25 overflow units as routing evidence;
do not treat that count or the four reserve shortfalls as a completion percentage.
Further local repairs need a causal link to an actual acceptance failure or to
admission of the next full-flow stage.

Screen at most three candidate configurations, including the retained baseline.
Choose alternatives from the diagnosed mechanism: for example a coordinated
region change or more routing space. Record the hypothesis before measuring it.
Do not automatically continue the queue of individual weak-net repairs.

Prefer the pinned footprint. If space is the demonstrated obstacle, use one
explicitly larger experimental floorplan, capped initially at twice the pinned
die area. Preserve the original target and record absolute/percentage overage.
A changed outline requires consistent DEF, pin placement, power distribution and
layout checking; changing only a die-area number is insufficient. This is a new
platform comparison, not a competition-qualified result.

Admit at most two A configurations to full-flow attempts. Require completed
detailed routing, extracted setup/hold and electrical limits under the declared
valid corners, DRC/LVS/antenna checks, power connectivity and implemented-netlist
behavior checks. Minimum pin access or passing coarse-route timing is insufficient.
Preserve the actual post-repair netlist as the artifact used by later evidence.

**Exit:** a passing physical A artifact and its complete report, or a bounded
failure diagnosis that identifies the unsatisfied requirement. A failure is useful
research, but does not complete this outcome or permit calling A buildable.

## Milestone 2: connect A's implementation to its meaning

Begin the model/interface work after milestone 0, using inexpensive checks while
physical uncertainty is being reduced. Finish the expensive artifact binding only
for the selected A implementation. Keep these obligations explicit:

- Source program to uploaded paired image. Prefer a Lean-checked per-image
  certificate with a soundness theorem if that avoids proving the Python
  compiler implementation. A certificate must establish the real encoding and
  closure premises, not merely repeat compiler assertions.
- Paired image, initialized memory and actual controller transition to reference
  execution, including capture order and exact edges. Discharge the current
  conditional schedule's premises through the image/load relation.
- Serial loading, malformed-image rejection, reset, commit/start, replacement
  and result observation through the complete package. State legal environment
  and initialization assumptions; do not silently exclude existing error cases.
- Actual generated RTL to the selected Lean circuit interpretation, reusing the
  restricted importer and artifact-proof approach where applicable. Extend only
  the missing operations/interfaces; retain explicit parser and SRAM trust bounds.
- Synthesis and physical edits to the implemented circuit. Use appropriate
  equivalence and independently checked transformation evidence, alongside the
  final-netlist external-pin regression. Finite tests alone are not universal
  correspondence, and mapped comparison with unconstrained SRAM Q does not
  establish the closed memory behavior.

Do not needlessly prove the entire CAD toolchain. Name the theorem and scope for
each proved edge, the checker for each checked edge, and every trusted interface.
Keep the standard axiom audit and meaningful corruption cases. The successful
baseline must survive its checks; behaviorally corrupted artifacts must fail
for the intended reason.

Integrate the paired image with the existing host workflow and independent peers.
Bind proof, image, RTL, mapped and final physical identities in one acceptance
report using existing receipts. Make this report describe one artifact lineage.

**Exit:** A has an explicit, completed correspondence chain under its declared
assumptions, an executable host demonstration and the physical result from
milestone 1. An open required theorem/check leaves A incomplete.

## Milestone 3: perform the capacity change as a design iteration

Implement only the parameterization needed for A and B in the existing model,
image encoder, admission logic, typed circuit, host adapter and checks. Preserve
an A regression after the change. Avoid a new general hardware framework.

Accept the capacity brief without requiring users to name mapped cells, net
numbers, Tcl commands or placement coordinates. The agent may derive internal
recipes, but all implementation choices must be captured so a clean replay does
not require unrecorded manual edits.

Exercise old A programs and new capacity witnesses, boundary rejection, branch
and capture timing, and interrupted upload/replacement. Apply the same formal,
mapped and physical acceptance requirements to B. After cheap functional and
cost screens, admit at most two B configurations to full-flow attempts within
the campaign budget. Keep timing assumptions fixed and record any size overage.

**Exit:** a passing B implementation plus a comparison of capacity, image/upload
cost, area, timing, routing, proof obligations and agent intervention. A rejected
B provides an understandable limit, but does not establish the second completed
design promised by this plan. Do not substitute a smaller change silently.

## Milestone 4: replay and demonstrate the workflow

Provide one documented entry point, or short reproducible command sequence,
that composes the existing runners. It accepts the design brief and produces
the acceptance report. Add orchestration only where it removes a real manual
handoff; do not build another receipt framework or new UI for this milestone.

Replay each design from a fresh output directory using its pinned toolchain and
declared inputs, with no undisclosed saved-route dependency. Reused expensive
physical evidence must be hash-bound and labelled as reuse; it cannot claim a
second physical run or physical repeatability. If a changed source or identity
requires new routing, count that attempt against the same budget.

The user-facing demonstration explains the requirement, what changed, what was
proved/checked/assumed, the measured tradeoff, and the one-command or documented
replay. A and B can share proof structure, but must each have their own accepted
artifact identities. Record elapsed resource use and manual interventions as
observations; two examples do not establish general ease of chip design.

**Exit:** both designs satisfy their acceptance tables, a fresh replay recovers
their evidence chain, and the same documented workflow supports the capacity
change. This is the complete design-iteration milestone.

## Autonomous execution and bounded allocation

The user approved execution on 2026-09-26 after reviewing this local execution
envelope. The original planning turn changed documentation only. Proceed through ordinary local implementation,
proof, tests, candidate selection and measurement without asking about each
routine step. Preserve existing work and use fresh output identities.

- **CAD:** at most eight hours aggregate across the campaign, including failed
  attempts, controls and retries; at most four full-flow attempts, each capped
  at 90 minutes. Use one CAD process at a time, at most four CPUs and 6 GiB,
  consistent with the existing runner. If preflight shows those limits cannot
  support the required run, report that before launching it.
- **Cheap discrimination:** normally cap an individual synthesis/placement/local
  screen at ten minutes. Prefer existing evidence and targeted checks before
  full routing. Use bounded proof subprocesses with progress retained separately.
- **Tool repairs:** at most two repair-and-control cycles for the same blocking
  tool problem and at most one aggregate CAD hour inside the eight-hour total.
  An exhausted repair budget triggers a recorded alternative or a stop, not an
  unlimited CAD-internals project.
- **Decision checkpoints:** finish each milestone with its outcome, artifact
  identity, remaining uncertainty and cumulative resource use. If a required
  milestone cannot pass, continue independent work where useful but do not
  proceed as though its dependent gate passed. Missing authority, qualified
  inputs or exhausted resources requires a concrete blocker report.
- **Research direction:** after two failed physical hypotheses without improved
  evidence about the blocker, reconsider the architecture/platform before more
  repairs. Reallocate within the remaining budget; a new run tag never resets it.
- **External boundaries:** remote publication, push/PR, paid compute, fabrication
  and license decisions retain their separate authorization requirements.

The runtime limits bound expenditure, not a prediction that closure is possible
within them. Do not declare completion merely because the allocation is consumed.

Hardcaml remains optional. Introduce it only if a named generation bottleneck
survives a bounded attempt with the existing typed Lean generator, and a focused
comparison can decide the issue. It must produce an interpreted, checked artifact
through the same acceptance chain; changing languages is not a milestone itself.

## Record ownership and first action

Keep active allocation in [status](status.md), detailed measurements in their
existing studies, conclusions in [results](results.md), and dated receipts in
[journal](journal.md). Use existing manifest/checker structures and ignored
`build/` outputs. Do not rewrite historical receipts to match this plan.

**First execution action:** perform milestone 0 and publish the acceptance table
and blocker ranking. The first experiment follows from that ranking; the previous
proposal to partition `_01876_` is no longer the automatic next task.
