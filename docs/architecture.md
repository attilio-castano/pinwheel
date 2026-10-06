# Architecture: Lean as the foundation

This document owns the design layers, implementation boundaries, and module map.
[Research status](research/status.md) owns the active question; [results](research/results.md)
and the [journal](research/journal.md) own conclusions and history. The original
architecture plan dates to 2026-09-12; this consolidation removes its accumulated
progress updates and speculative file inventory.

## Design objective

Build a programmable protocol engine whose instruction semantics make precise pin
timing explicit. Lean specifies behavior, executes reference models, and proves
properties that constrain circuit design. The [competition brief](competition.md)
owns external requirements; [processor verification](engine/processor-verification.md)
owns the evidence needed across the implementation boundaries.

Hardware generation produces the circuit that would be fabricated. Protocol
compilation produces reloadable instructions for that circuit. Replacing a
protocol program must not require regenerating RTL. The fixed protocol controllers
provide independent behavioral references for the shared engine.

## Three connected layers

| Layer | Responsibility | Evidence |
| --- | --- | --- |
| Protocol specification | Define observable pins, timing, and sampled-input assumptions independently of implementation transitions. | Executable contracts and controller proofs for the supported UART, SPI, and I²C subsets. |
| Machine and program compiler | Define instruction semantics, bounded state, loading, and execution on each edge; compile supported protocols into programs. | Invariants and correspondence between compiled execution and protocol behavior under stated assumptions. |
| Circuit implementation | Realize the machine with encoded registers, combinational logic, memory ports, and loading control. | Circuit-to-engine refinement, separate generated-artifact validation, and mapping/physical measurements. |

The [original engine design](engine/shared-engine.md) explains the UART/SPI-derived timed
Action/Halt model. The [reactive engine](engine/reactive-engine.md) adds drive/release,
observed-input waits, guarded timing, and conditional control needed by I²C.
These have distinct capacity and encoding contracts; a later backend does not
silently redefine the original baseline.

The [UART link contract](uart-link.md) relates independently clocked TX and RX
execution through a bounded digital observation age. Its numerical conditions
discharge the receiver's start/data/stop premises and compose through both
compilers. This environment relation belongs beside the protocol; it leaves a
concrete physical sampler responsible for meeting the assumed observation bound.

The [continuous UART receive model](protocols/uart-stream.md) separates reception from
consumer ownership. A one-entry buffer preserves the oldest unread result,
supports simultaneous consumption and arrival, and makes overrun and reset
flushes explicit. A Lean supervisor composes automatic rearm with the existing
compiled RX program. Its ideal finite-stream theorem includes time to rearm
between frames. The [continuous clock contract](protocols/uart-stream-clocks.md) extends
that result to unequal clocks and varying bounded observation age. It reserves
two additional RX ticks beyond the one-frame bound, establishes agreement with
the continuous wire, and preserves the timing conditions after each rearm.
A circuit implementation of this supervisor remains a separate refinement
obligation.

The chip's [host result mailbox](engine/whole-chip.md#host-result-interface-version-1)
uses the same oldest-unread ownership convention for one-shot programs of any
protocol. It snapshots the 16 capture slots and engine outcome and exposes them
through the chip pins. It does not implement the UART supervisor's automatic
rearm or finite-stream theorem.

The [timed component contract](engine/timed-components.md) defines input-dependent
observations before and after each edge and composable refinement between
implementations. Checked signal interfaces give typed identities and complete
named observations. These abstractions describe digital behavior; they do not
model propagation delay or establish a memory macro's availability schedule.

## Let timing obligations inform hardware

An action that drives a level for N cycles must specify its entry and exit edges.
Adjacent actions have no implicit fetch interval. Conditional execution must
preserve terminal capture, branch selection, and successor entry capture in their
defined order, including uninterrupted one-cycle branches and self branches.

The implementation must supply each instruction by that edge. Register-backed
combinational reads and synchronous memories have different contracts; SRAM
replacement needs a proved availability/buffering schedule. See [fetch contracts](engine/timed-components.md)
and [storage primitives](storage-primitives.md) for those obligations.

The [atomic loader](storage/atomic-loader.md) owns staging, validation, bank selection,
commit, and busy-write rejection. Account for the old and staged images together.
Reset behavior, invalid programs, initialization, and public observations belong
to the contract. Serialized transport, synchronization, and package pins require
an explicit relationship to these synchronous core semantics.

## Hardware and program paths

```text
Circuit:
Lean structural circuit -> hardware MLIR -> CIRCT -> SystemVerilog
                                                -> simulation / synthesis / physical flow

Program:
Transaction request -> Lean compiler or named resident builder
                    -> execution records / paired load image -> writable engine memory
```

The circuit path uses a restricted width-indexed language with explicit register
and combinational semantics; it does not synthesize arbitrary Lean functions.
Emitters write ordinary CIRCT hardware dialects. [PWL images](storage/binary-images.md)
represent serialized programs, while [E64 records](storage/execution-records.md) describe
literal execution words. Counted load images can be expanded before execution;
the [bounded repetition prototype](storage/storage-study.md#bounded-runtime-repetition)
separately investigates reconstruction at runtime. Load-image byte counts and
allocated hardware storage are different measurements.

The [transaction layer](protocols/transaction-workflow.md) gives these program
paths one public compile/load/run/decode interface. It binds request data to
the compiled image, named pins, timing units, resource use and result layout.
Fixed SPI and compact I²C use `Program.Requests`; resident UART/SPI/JTAG use
the Python builder. This common workflow preserves independent protocol
references; it does not turn every frontend into one Lean compiler.

`Program.Resident` extends the typed Reactive instruction language with SHIFT
and KEEP. It lowers their entry effects to ordinary timed actions using the
pre-edge operand and output levels, while delegating waits, guards, captures
and successors to Reactive semantics. Canonical encoding and local transition
proofs are checked separately from complete initialized package lifecycle
refinement. Requests exceeding the operand or result capacity fail at this
programming boundary before pin I/O.

The [finite-transfer model](protocols/buffered-transfers.md) makes the next data
ownership decision explicit: one preloaded TX value, reserved RX capacity,
exclusive engine access during execution and immutable retained completion
until matching release. `Program.Transfer` proves bounded lifecycle/identity
invariants. A separate generic timed Python target exercises four-byte SPI
and 32-bit/non-byte JTAG with independent resolved-pin peers. The target has
no paired upload encoding or circuit integration; current SRAM allocation,
host command/readback format and physical evidence are unchanged. Data bits
and scratch/control captures are separate. The counted hardware continuation
below implements timed lookup, admission and indexed result readback; reactive
decisions and memory-backed fetch remain the next engine contract.

The [buffered reactive continuation](protocols/buffered-reactive.md) now composes
owned TX/RX entry effects with `Reactive.Fetch` execution and a generalized
`Counted.Schedule`. The old counted grammar has a proved equal-span/equal-lookup
embedding. A single Python interpreter executes linear SPI/JTAG and reactive
I²C programs. Four-byte I²C uses 50 instruction leaves and 55 sequence/repeat
descriptors for 270 virtual positions, with distinct ACK scratch and RX data.
This is a reference schedule, not a larger admitted paired image. Its lowering,
data storage, command admission and indexed readback need a new circuit contract.

The [first buffered hardware slice](protocols/buffered-hardware.md) implements
linear timed programs, dedicated 32-bit TX/RX, coverage-checked image loading,
finite identities and retained indexed readback in a typed circuit. Its writable
128-by-32 register store supplies a measurable baseline. Actual emitted and saved
gate RTL exercise SPI; this parallel target does not extend the paired SRAM
image or serial package.

The [counted hardware continuation](protocols/buffered-counted-hardware.md) lowers
the shared timed schedule to 64 packed instruction/control rows. Two nested
loop counters select up to 1,024 virtual positions, entering the next leaf on
the dispatch edge without an extra waveform clock. The host binds the complete
source tree and exact row metadata; local circuit guards reject malformed
entry before data effects. SPI and JTAG are uploaded programs in the same
emitted circuit, with the same owned TX/RX and retained readback.

The [reactive counted continuation](protocols/buffered-reactive-hardware.md) adds
WAIT, CHECKED and QUALIFY, scratch capture, inverted enable shifts and explicit
branch endpoints that restore the physical row, virtual PC and loop indices.
SPI, JTAG and multi-byte I²C load different programs into this same circuit.
Its 64 rows are 144 bits each; host admission binds declared successful demands
and maximum RX reservation to the full source tree. Fault/timeout retain raw
prefixes and scratch until release. The register-backed target now supplies
a measured fetch/ownership baseline for a memory and serial implementation.

The [composed dense cached backend](engine/hardware-closure.md#composed-backend) uses
typed combinational bindings so shared successor/PC logic has one explicit
definition. Its netlist semantics evaluates all bindings from the same pre-edge
register state. The generic serializer consumes that proved netlist; the legacy
emitter remains the comparison baseline. The [external timing contract](engine/external-interface.md)
separately defines the proposed sampled-pin delay and open-drain interpretation.
The [full-backend read-back](engine/hardware-closure.md#full-backend-rtl-read-back) checks
the actual emitted RTL against that netlist and composes its initialized trace
refinement. Source/MLIR matching and solver queries only suggest proof boundaries;
Lean must check every accepted equality.

## Physical organization beside the semantic netlist

A semantic module boundary says who defines or proves a transition. A physical
block boundary says where state lives, which logic consumes it, and which values
must cross to another block before a particular edge. These boundaries need not
coincide. The current `Netlist` binds shared expressions in one emitted module;
typed interfaces do not yet preserve a physical partition through synthesis.

The [chip architecture comparison](physical/chip-architecture-study.md) supplies a concrete
starting point: two existing SRAM organizations, complete state/port budgets and
their worst-case schedule. Both macro responses feed both address ports, so the
execution/fetch feedback must be considered together. Direct's upload scratch
and hybrid's execution map have different lifetimes and consumers despite both
representing the same uploaded program.

The assembly description connects four views:

| View | Required information | Check |
| --- | --- | --- |
| Observation | Public pin/capture edges, accepted programs and atomic replacement | Existing machine/trace refinement |
| Ownership | Every state element, its updater and consumers; shared combinational producers | Complete emitted-name census with no conflicting owners |
| Schedule | Requests, response availability, resource use and ownership on each phase/edge | Lean lemmas tied to controller expressions; independent artifact checks |
| Physical budget | Macro geometry, mapped area, crossing nets and locality requirements | Matched mapping/placement measurements; later extracted checks |

`Storage.SramAssembly` now owns the existing composition, typed state owners,
register enumeration and request/response crossings. Both emission and analysis
consume it; classification follows register constructors rather than name
patterns. Eight width-indexed computations bind successor/candidate selection,
read addresses and upload requests to values already in the emitter cache;
diagnostics cannot add operations or change the emitted circuit.
`Storage.SramSchedule` connects access exclusivity, actual read/write address
cuts, hybrid branch
availability, response timing, commit/start ownership and broadcast writes to
the existing controller/array model. These additions preserve RTL bytes.

Typed bank/word coordinates also support the [map-slice census](physical/map-slice-study.md).
`chip_map_slice.py` traces stored-bit dependencies, owns control logic only when
all consumers are local, and keeps remaining shared support explicit. Bit planes
and tiles following the actual read-tree order expose different cuts in the
same circuit. Smaller private area can mean that more computation sits outside
the block; compare full shared support and every input/output boundary before
turning a grouping into an implementation interface.

The [local-decoding tile experiment](physical/map-tile-study.md) reuses the existing
`Memory.Flops` circuit rather than defining another memory. `Storage.MapTile`
proves its projection onto actual controller reads and updates. A separate
map-only probe preserves 32 tile boundaries and accounts for their glue;
arbitrary-state SAT checks cover emission and technology mapping independently.
The narrow interface survives, but shared input fanout initially rises to 224.
Explicit distribution adds 346 buffers while preserving child internals and
reduces that maximum to ten. It consumes most of the area advantage: 0.2189%
remains, with read depth ten versus the flat map's 14/13. Independent arbitrary-
state checks confirm the buffered composition. Distribution belongs in the
organization's cost alongside state, computation and port ownership; a compact
interface alone does not bound its drive cost.

The complete-chip follow-up moves the map interface and glue into shared
`TiledMap`, preserving the earlier emitted bytes. `TiledController` exposes
actual admitted writes and candidate PCs, reuses the controller/adapters and
omits the map registers that the 32 tiles now own. General `Netlist.toCircuit`
substitution has step/observation proofs; independent full-chip checks validate
the emitted composition and all macro terminals. The retained baseline remains
unchanged.

The candidate saves about 1.26% of standard-cell area, but loses the standalone
depth advantage: a longest address path has twenty engine gates and ten map
gates. Shared cursor bits drive eight engine pins plus seven map pins, exceeding
the map-internal budget. Keep stored-word ownership explicit while choosing
combinational optimization boundaries from complete dependencies and aggregate
loads. The [combined controller/selection follow-up](physical/map-tile-study.md#combined-controller-and-selection--september-22)
retains the 32 storage tiles and fixes aggregate fanout to ten. It saves about
1.08% of standard-cell area versus the baseline, but address depth remains 30/29.
The [fetch contract study](fetch-contract-study.md) now separates that structural
count from measured timing. Terminal capture can affect a branch on the same
edge; a forwarding alternative is proved for arbitrary states. The entered-word
candidate calculation needs only 21 metadata bits, or 18 under an explicit
valid-word premise. These statements do not change emitted RTL or authorize
timing exceptions.

Retained-netlist STA identifies the SRAM return path as the slow setup limit,
and upload data as the hold problem. The library fanout limit is eight, whereas
the earlier structural budget was ten. A proved buffer-only repair adds
9,935.6544 µm² and removes reported electrical violations, with essentially no
setup benefit and unresolved hold. It is retained as a cost probe. Use actual
arrival windows and aggregate library loads when choosing decode/selection
boundaries; do not require fewer gate levels before a cheap timing comparison.
The [local eight-load follow-up](fetch-contract-study.md#local-mapping-with-the-library-budget--september-22)
applies the budget during mapping, reducing tile write-data input load seven→two.
Shared distribution then needs 225 buffers instead of 354. The complete chip
costs 290,943.9540 µm², below the baseline, with zero reported cell-only electrical
violations and slow setup slack +10.52 ns; cell-only hold is −0.86 ns. The useful
contract is each driver's aggregate load, composed across storage and logic
boundaries. Mapped area includes all distribution, and STA checks its effect.
The [exact-mapping physical follow-up](chip-physical-study.md#exact-mapping-placement-and-hold-repair--september-22)
now verifies every imported connection before placement. Its candidate keeps a
2.52% area advantage after clock and hold repair. Both placement hold screens
pass, but candidate coarse routing reopens two upload hold failures and exposes
clock fanout and SRAM return-load violations. Thus the implementation contract
must include earliest/latest arrival, clock arrival and physical load. The
shared microarchitecture description identifies the obligation and its owner;
the physical artifact measures whether that implementation satisfies it.
The [clock-budget follow-up](chip-physical-study.md#clock-budget-and-post-routing-repair--september-22)
extends this lesson to hierarchy: bounding clock leaves removes 199 fanout
violations, but four upper branches still exceed the budget. SRAM outputs with
only one or two sinks can exceed capacitance limits because of wire load.
Generic post-route repair left that netlist and all cell positions unchanged
despite its repair counter. The [local diagnosis](chip-physical-study.md#local-clock-and-sram-repair--september-22)
finds two distinct owners: ordinary repair skips clock nets, and the SRAM
repair tree lacks layer RC values that timing already accounts for. Explicit
RC initialization enables data buffering. Splitting upper clock loads between
copies at the same tree level preserves depth while satisfying fanout eight.
All original cells and placements survive the eleven-buffer local edit.
The [fresh coarse route](chip-physical-study.md#coarse-routing-the-local-repair--september-22)
preserves those identities, clears the seven targeted SRAM output load failures
and improves hold. It also leaves 58 slow slew failures on 28 driver nets,
including every SRAM address input, and 1,302 overflow. Output load isolation,
input transition quality and routing capacity therefore remain distinct
obligations even when the logical interfaces and cell locations are unchanged.
The [data-buffer follow-up](chip-physical-study.md#local-data-buffering-and-complete-wire-estimates--september-22)
then reduces slow slew 58→22 and improves slow setup +2.02→+5.34 ns with 43
buffers and unchanged original placement. New failures appear outside the
target list after rerouting. Electrical ownership belongs to a driver and its
complete wire/sink tree; checking only the edited cells misses those changes.
The [electrical-cost diagnosis](chip-physical-study.md#electrical-cost-and-sram-interface-geometry--september-22)
measures 82–97% wire capacitance on all ten remaining groups despite only two
or four sinks each. Saved congestion is concentrated around the SRAM footprints,
with little in the already reserved corridor. A useful physical boundary must
therefore include pin escape, routing capacity and the nearby communication
tree, alongside state ownership and edge deadlines. The failed incremental
repair supplies no proof that a different storage/fetch schedule is necessary.

The [interface screen](chip-physical-study.md#sram-interface-geometry-and-upload-staging--september-22)
now traces upload traffic through buffer/delay chains and binds pin escape to
actual obstructions and power geometry. Saved OpenROAD capacity includes its
reductions in both capacity and usage; equal capacity arrays alone cannot
establish equal blockage effects. Keep the underlying exporter semantics in
the measurement contract.

`Storage.UploadPipeline` is an opt-in output-side observer that owns a 71-bit
pending write. It uses actual busy/start/commit outputs to preserve SRAM read
priority, while reusing the original controller transition and typed assembly.
The queue schedule, logical memory view and emitted write-priority expression
have proofs. Because the observer changes the memory responses reaching the
core, generic observer composition alone does not establish its full execution
refinement. This is the useful discipline behind explicit hardware interfaces:
own the state, name the edge obligation, bind it to emitted signals, then measure
the resulting circuit. Its functional success and 1.93% matched mapped-area cost
do not establish physical locality or routed timing benefit.

The [upload-locality follow-up](chip-physical-study.md#upload-stage-locality-and-available-placement-space--september-22)
distinguishes a source-bit family from exclusive physical ownership. Directed
traversal finds that 41/44 interior guide crossings also serve other logic, and
106/128 associated hold-delay cells are shared. Placing just the new stage into
remaining row gaps fails even an optimistic data-register allocation. A useful
physical component must include shared producers/consumers and the space taken
by displaced cells, as well as its typed ports and cycle contract. Preserve all
other consumers when evaluating a proposed cut through a buffer tree.

Physical annotations must therefore form an explicit checked interface:
pin identity, corner, units, wire model and annotation completeness must agree
between the reporter and the optimizer. The data-buffer study finds partial
annotations even on its unchanged control under placement-only estimation;
apparently passing slack and electrical counts are therefore unqualified.
A repair counter does not establish a changed implementation;
a passing placement estimate does not establish that routed detours fit the
load budget. Contract known noninverting buffers to check preserved signal
connectivity, then measure earliest/latest arrival with the changed clock tree.

Use existing `Interface`, `Netlist`, `FetchPolicy`, feeders and observers for
their established responsibilities. `chip_organization.py` assigns each mapped
cell by its sequential/package consumers and counts shared producers once.
Add hierarchy or placement constraints only when the
description is bound to actual emitted/mapped names and provides a measurable
locality hypothesis. A smaller proof or a more reusable function is not by itself
a smaller circuit; a smaller gate graph is not by itself a cheaper routed chip.

`scripts/report-chip-architecture.py` verifies current Lean checks and exact
regenerated MLIR/RTL identity before applying the assembly manifest to the saved
mapped artifacts. It checks state names/widths and macro crossings, including
address narrowing. Its census distinguishes named registers from real FFs,
broadcast pins from distinct nets, and overlapping cones from additive area.
Source bit-dependency analysis separates read/write branches without treating
their operation counts as mapped cells or phase-qualified STA paths. Optional
saved-OpenDB analysis selects private address stages by connectivity anew and
measures geometric projections across all incident nets; cell names from a
different mapping cannot establish physical membership. The first projection
was rejected because incoming-net cost outweighed shorter final connections.
These geometric proxies do not assign activity or delay to Lean expressions. A schedule
certificate can eliminate invalid organizations early; physical capacity,
parasitics, timing and layout rules retain their own evidence boundary.

The [physical organization policy](physical-targets.md#physical-organization-policy-and-saved-chip-screen)
adds a small decision layer between measured distribution and an exact repair
plan. The inventory identifies the actual source, complete transport tree and
consumers; the policy says which consumers may be grouped together, which drive
changes are allowed, what geometry must remain fixed and which budgets apply.
The plan must then name every actual edit. Independent readback and fresh
physical measurements determine whether that implementation qualifies.

`physical_organization.py` reconstructs shared trunks once, distinguishes buffers
from protected delay cells, and costs both output branches and upstream input
loads. The first policy permits same-source leaf exchanges, fixed-origin buffer
growth and a separate SRAM receiver. It protects clock, state, macro and hold
boundaries, and retains the original area, timing and electrical-reserve contract.
Virtual exchanges are checked against an independently saved mapped netlist;
shorter pin-envelope spans remain geometry estimates, not timing evidence.
The first eighteen choices expose a placement-policy limitation on one failing
branch before any CAD run. The [bounded refinement](physical-targets.md#local-qualification-of-the-organization-policy)
then permits one named buffer to move within ten sites on its original row and
orientation. Pinned LEF geometry checks both its input and output locations;
all incident connections enter the cost and validation scope. Grouping ranks
weak branches by their own saved wire load and remaining capacitance budget.
Proportional span scaling is a conditional search heuristic, never an electrical
bound. The selected mixed plan meets every original numerical budget locally.

The [shared edit and route follow-up](physical-targets.md#shared-physical-edits-and-whole-chip-requalification)
now separates candidate search from four declared operations:
`resize_buffer`, `move_resize_buffer`, `regroup_consumers` and `insert_receiver`.
`physical_organization_edits.py` validates policy, exact connectivity and geometry;
the historical recipe builder delegates to it. `physical_organization_route.py`
independently recomputes the candidate's ancestry, complete scope, raw measurements
and original budgets before shared intake can admit one coarse route. The helper
supports different operation counts within the pinned technology's rules; it is
not a general placer or a proof that local margins survive routing.

The first full-route test retains all six original target gains but fails on
other nets, clock delivery and shared capacity. A control net outside the family
inventory appears on the new worst setup path; independent whole-chip checks
catch it. On a matched input-hold path, unchanged data delivery and a **39.834 ps**
later capture clock explain the loss of margin. Thus a physical distribution
contract needs both local edit obligations and a global environment check.
Identical logical clocks and stored routing rules do not guarantee identical
clock arrival or runtime rule decisions. Family coverage must remain explicit,
with whole-chip checks providing a separate guard against omissions.

The [matched saved-chip diagnosis](physical-targets.md#matched-clock-control-and-capacity-diagnosis)
makes that environment observable without changing the circuit. Four exact paths
retain their pin, transition and cell sequences; thirteen clock nets and five
complete transport trees expose clock delay separately from data delay. The
mode/status regression is almost entirely data-path delay, whereas SRAM/status
and input hold are sensitive to clock delivery. A register self-hold path keeps
its margin as launch and capture move together. These observations support a
path-specific clock-delivery contract, rather than a blanket rule that every
clock shift or longer wire has the same effect. The proposed next inventory
adds the shared-control tree's six branches while retaining global checks.

The [timing and communication study](physical/physical-organization-study.md) now joins
those measurements to explicit same-edge observations, conditional clock-shift
bounds and alternative distribution costs. `physical_organization_study.py`
owns the small timing/replication calculations; the existing planner still owns
consumer exchanges. The reporter verifies 1,152 endpoint connections and reuses
saved parent-net measurements. Its bounded exchange portfolio has no complete
conditional pass. Local decoder copies remain a structural alternative whose
area, upstream wires and clock environment must be budgeted explicitly. No
study result bypasses the independent physical route intake.

## Proof and validation boundaries

[Processor verification](engine/processor-verification.md#the-chain-of-evidence) defines
the state relation and acceptance gates. Its central requirement is exact modeled
observation preservation for the supported programs, input histories, and initial
states. Proofs must disclose assumptions and contain no unfinished proof placeholders.

A proof of Lean circuit semantics does not prove the emitter, CIRCT transformations,
or mapped gates. Independent RTL checks, translation/equivalence work, and physical
checks supply different evidence. Likewise, exact cycle counts do not establish
nanosecond timing or external electrical compliance. Use the [research workflow](research/README.md#evidence-standards-for-hardware)
when reporting those claims and artifact identities.

## Choosing a composition operation

Use the operation whose dependency boundary matches the change:

| Need | Owner | Constraint |
| --- | --- | --- |
| Change the interpretation of an input without adding state | `InputMap` | Prove substitution correct; retain explicit shared wires and specialized literal comparisons where timing depends on them. |
| Add input transport or sampled delay | `Feeder` | Inner inputs depend on outer inputs and feeder state; feeder state does not observe the core. |
| Retain or present a core result | `Observer` | Observer state may see core outputs, but cannot change the core's register updates. |
| Supply successors under a different read schedule | `FetchPolicy` and `PolicyBackend` | State the available reads and edge timing; reuse the loader, scheduler and backend realization. |
| Restrict uploaded programs | `Admission` and `AdmissionNetlist` | Reject invalid pushes; preserve other commands and keep commit/start decoding independent of payload data. |
| Certify a compiler's programs for an organization | `Compile.Readiness` | Depend on the storage rule from the compiler layer, rather than importing protocol compilers into storage. |

`Loader.ProgramImage` is the shared upload encoding. Storage owns whether an
image fits and when fetched words are ready; compiler certificates discharge
those conditions. Host transport delivers commands and the result observer owns
unread data. A new SRAM adapter must satisfy the chosen fetch contract without
moving these responsibilities into a second loader or protocol compiler.

`Storage.Sram` now owns the hybrid's synchronous response state: Q holds on a
dictionary write, commit reads the new start word, and the following edge both
bypasses and saves that response. Initialization and every later observation
refine the unrestricted atomic machine. Its start-bypass expression is shared
with the experimental emitter. `Memory.Sram` owns replicated-array semantics,
held responses, initialization and bank isolation. `Storage.SramController`
owns the controller expressions used by both proofs and emission; its hybrid
request lemmas connect actual enables, bank/index addresses and broadcast data
to that array contract. `Storage.SramCoverage` uses the existing loader transition
to prove initialization of the accepted upload prefix and complete valid bank,
then definedness of actual selected-bank reads and physical responses.
`Storage.SramContents` identifies those values with the existing loader image;
`Storage.SramExecution` composes that correspondence with actual array Q,
controller address selection and start/current/branch ownership. Its initialized
trace matches the capacity-adapted atomic reference, and `core_step` checks every
controller register against the shared netlist. The retained backend image is
specification bookkeeping; successors come from Q or the saved start word.
`Storage.SramAssembly` owns package composition and its emitted state/interface
description; the test emitter serializes it. `Storage.SramSchedule` exposes
selected edge obligations from these proofs. Moving the composition into the
library does not complete its full Verilog binding/read-back proof.

The [host workflow](host-workflow.md) uses a transport interface and raw result
type independent of the engine oracle. Protocol peers own wire interpretation;
the client owns upload, start and result consumption. It runs different programs
on one fixed chip, so protocol compilation stays separate from circuit generation.

Validation follows the same separation: `hardware_targets.py` describes semantic
boundaries, while measured register/equivalence counts belong to a specific
recipe. `validation_run.py` owns command capture, timeouts and reasoned failure
checks; each gate retains its oracle, expected observations and evidence scope.

<a id="proposed-repository-structure"></a>

## Repository structure

This map describes existing owners rather than promising individual future files.
The legacy section anchor above preserves links from the original experiment plan.
Proofs remain beside the definitions they establish; emitters depend on semantic
modules rather than defining their contracts.

| Path | Responsibility |
| --- | --- |
| `Pinwheel/UART/`, `Pinwheel/SPI/`, `Pinwheel/I2C/` | Independent protocol specifications, reference controllers, and proofs. |
| `Pinwheel/Engine/` | Original and reactive instruction semantics, loading/execution, compatibility, functional fetch, and counted programs. |
| `Pinwheel/Compile/` | Protocol compilers and correspondence; `Readiness.lean` owns compiler-specific admission certificates. |
| `Pinwheel/Program/` | Pure JSON request frontend and typed resident SHIFT/KEEP semantics, encoding and local proofs. The static export executable lives under `scripts/`. |
| `Pinwheel/Binary/` | PWL codecs, layout, round trips, decoded execution, and serialized-size accounting. |
| `Pinwheel/Hardware/Circuit.lean` | Width-indexed expressions, register updates, and their digital semantics. |
| `Pinwheel/Hardware/Netlist.lean`, `NetlistEmit.lean` | Typed shared combinational bindings, their semantics, and generic MLIR serialization. |
| `Pinwheel/Hardware/NetlistTools.lean`, `NetlistInputs.lean` | Timed views/output maps and proved input substitution preserving shared wires. |
| `Pinwheel/Hardware/Feeder.lean`, `Observer.lean` | Stateful input adapters and output observers; observers cannot change the wrapped core's transition. |
| `Pinwheel/Hardware/Chip.lean`, `HostResult.lean`, `Serial/` | Pin map, sampler/serial composition, host sessions, and retained result ownership. |
| `Pinwheel/Hardware/CountdownContract.lean`, `scripts/countdown_import.py` | Countdown trace correspondence and restricted read-back of actual emitted RTL. |
| `Pinwheel/Hardware/Storage/BackendReadback.lean`, `scripts/backend_readback.py`, `check-backend-readback.py` | Full-backend artifact interpretation, composed Lean proofs, initialization/trace closure and corruption checks. |
| `Pinwheel/Hardware/PinBoundary.lean` | Proposed digital input-pipeline delay and open-drain pad interpretation; no physical wrapper. |
| `Pinwheel/Hardware/Timed.lean`, `Pinwheel/Hardware/Interface.lean` | Exact-edge component refinement and checked signal interfaces; the latter is not a physical loading interface. |
| `Pinwheel/Hardware/Encoding.lean`, `Core*.lean`, `Refinement.lean`, `Protocols.lean` | Original encoded UART/SPI core and compiler-proof composition. |
| `Pinwheel/Hardware/Execution/` | E64 encoding/lowering, decoder, direct/indexed storage, and proofs. |
| `Pinwheel/Hardware/Reactive/` | Structural reactive scheduler, capture/fetch order, interfaces, and integrated core refinement. |
| `Pinwheel/Hardware/Loader/` | Atomic two-bank loading, delivery and proofs; `ProgramImage.lean` owns the generic 322-word upload encoding. |
| `Pinwheel/Hardware/Storage/` | Capacity-limited, cached, dense, and repetition variants; fetch-choice and command-split experiments. |
| `Pinwheel/Hardware/Storage/FetchPolicy.lean`, `PolicyBackend.lean` | A common successor-supply contract and structural realization; one-, two-, and three-port organizations provide their schedules and invariants. |
| `Pinwheel/Hardware/Storage/Sram.lean` | Abstract hybrid response holding and commit/start ownership, initialized trace refinement, and shared start-bypass expression. |
| `Pinwheel/Hardware/Memory/Sram.lean` | Replicated synchronous-array contract, broadcast initialization, defined reads, held Q and bank isolation; permits unrelated initial contents. |
| `Pinwheel/Hardware/Storage/SramController.lean` | Shared experimental controller expressions, hybrid request correspondence and actual loader-control updates. |
| `Pinwheel/Hardware/Storage/SramCoverage.lean` | Accepted-cursor initialization coverage, preservation through command histories, selected-bank read definedness and physical responses. |
| `Pinwheel/Hardware/Storage/SramContents.lean` | Defined dictionary values agree with the existing loader image; actual read responses return its selected program words. |
| `Pinwheel/Hardware/Storage/SramExecution.lean` | Closed-loop array/controller execution, actual register-step correspondence and initialized trace refinement to the capacity-adapted machine; external binding/read-back remain separate. |
| `Pinwheel/Hardware/Storage/SramAssembly.lean` | Shared experimental chip composition, register enumeration, typed state ownership and SRAM crossings; consumed by emission and mapped-artifact analysis. |
| `Pinwheel/Hardware/Storage/SramSchedule.lean` | Actual request-port resource use, hybrid Q/candidate availability, commit/start bypass and atomic write obligations; no physical timing claim. |
| `Pinwheel/Hardware/Storage/FetchContract.lean` | Entered-word metadata dependence and a valid-word simplification, with explicit premises and no timing exceptions. |
| `Pinwheel/Hardware/Reactive/CaptureRead.lean` | Arbitrary-state read-after-capture forwarding identity and correspondence to the existing branch expression; not selected by production emission. |
| `Pinwheel/Hardware/Storage/Admission*.lean`, `OnePortAdmission.lean` | Generic rejecting admission and its emitted one-port specialization; capacity remains a separate storage rule. |
| `Pinwheel/Hardware/Storage/ProgramUpload.lean`, `Readiness.lean` | Storage capacity/upload contracts and generic readiness propagation; neither imports protocol compilers. |
| `Pinwheel/Hardware/Emit.lean` and subsystem emission modules | Structural-to-MLIR serialization and concrete wiring adapters. |
| `test/`, `scripts/` | Executable Lean checks, independent oracles, RTL testbenches, audits, and measurement runners. |
| `scripts/validation_run.py`, `hardware_targets.py` | Common command/log/provenance plumbing and semantic target descriptions; individual runners retain their independent oracles and historical expectations. |
| `scripts/pinwheel_host.py`, `pinwheel_sim.py`, `host_demo.py` | Public host transactions, an interactive pin-only RTL transport, and independent protocol peers. |
| `tools/`, `physical/` | Tool/library pins, physical constraints, controlled experiment configuration, and selected result manifests. |
| `docs/`, `docs/research/` | Technical owners and the central research workflow/status/results/journal. |
| `build/`, `.lake/` | Ignored generated evidence and Lean build artifacts respectively. |

`Pinwheel.lean` and `lakefile.toml` define the library entry point and build targets.
Tool installation and reproduction commands belong in [development](development.md),
and [the technical catalog](README.md) routes subsystem records. Add abstractions
or entry points when an implemented need establishes their contract; no standalone
`Trace.lean`, general generation CLI, or empty example tree is promised here.

Tiny Tapeout integration must reconcile its conventional `src/`, `test/`, and
`info.yaml` paths with existing test ownership, generated RTL staging, explicit
source lists, and the pinned upstream template. Lean sources remain under `Pinwheel/`.

## Toolchain decisions

The repository pins Lean through `lean-toolchain` and uses Lake. Bundled Lean
libraries supply the current package; Mathlib is not a dependency. [Development setup](development.md)
owns verified versions, installation details, and commands.

[Hardware tool pins](../tools/hardware-toolchain.json),
[technology-library pins](../tools/technology-library.json), and
[physical toolchain pins](../tools/physical-toolchain.json) identify the distinct
measurement environments. Reproduction must use the versions and constraints
recorded for that experiment, not assume every historical run used today's tools.

## Primary technical sources

- [Lean bitvectors](https://lean-lang.org/doc/reference/latest/Basic-Types/Bitvectors/): fixed-width values and bitvector proof automation.
- [Lean Lake documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/): package configuration, builds, and dependency management.
- [CIRCT hardware representation](https://circt.llvm.org/docs/Dialects/HW/RationaleHW/): modules, ports, and hardware dialects.
- [CIRCT sequential operations](https://circt.llvm.org/docs/Dialects/Seq/): clocked state and registers.
- [CIRCT Verilog generation](https://circt.llvm.org/docs/VerilogGeneration/): RTL export.
- [CIRCT setup](https://circt.llvm.org/docs/GettingStarted/): toolchain setup and LLVM/MLIR revisions.

These links are live documentation, not immutable snapshots. Verify compatibility against selected revisions during setup.
