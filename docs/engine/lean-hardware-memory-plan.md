# Memory library and streaming accelerator campaign

The first reusable memory component will implement the existing exclusive
single-port command contract. The two existing RAM semantics must stay distinct:

| Existing module | Reusable behavior |
| --- | --- |
| `Hardware.Memory` | One enabled write and unconditional reads; read-first collisions; configurable modeled read latency |
| `Memory.Flops` | Decoded full-word writes and balanced combinational reads, proved against latency-zero memory |
| `Memory.Registered` | Output registers update on every edge, including writes; proved against latency-one memory |
| `Memory.SinglePort` | Exclusive idle/read/write: read updates Q, write holds Q, idle holds both memory and Q |
| `Memory.Sram` | A partial initialized-value model related to arbitrary initial physical memory; replicated read ports and broadcast writes |

`Memory.Registered` therefore cannot be used directly as an implementation of
`SinglePort.Contract`. Neither contract silently supplies reset, initialized
contents, response validity, backpressure or byte enables. Current capacities
are powers of two, so all address-bit patterns are legal.

## First implementation slice

1. Add a complete typed command interface: enable, write, address, write data
   and Q. Disabled commands decode to idle. Prove physical codec round trips.
2. Construct `CommandFlops` from the existing decoded word updates and balanced
   read mux. Update Q only on reads. Preserve the existing memory array on idle
   and preserve Q on idle and writes.
3. Prove the state transition for arbitrary input and register bits, then
   package both `SinglePort.Contract` and the shared `Implementation` certificate.
   Provide exact state encode/view correspondence without an initialization or
   reset assumption.
4. Check independent model/RTL replay, complete endpoint correspondence and
   state/output mutation rejection. Cover disabled writes, consecutive reads,
   same-address read/write/read sequences, all addresses and arbitrary initial
   arrays and Q.

The generic read mux currently lives in `Hardware.Execution.Memory`. Reuse it
first; a later move should preserve compatibility aliases and rerun its existing
clients. The command RAM adds no fictitious memory-clearing reset.

### Implemented command RAM

`CommandInterface`, `CommandFlops` and `CommandFlopsProofs` now supply the
interface, structural implementation and universal proofs above. `view` and
`encode` are inverse on every physical state. `contract` discharges
`SinglePort.Contract`; `implementation` uses the common hardware certificate
with `Valid = True`. `trace_correct` starts from arbitrary words and Q.
They are available from `Pinwheel.Hardware.Library`.

```sh
lake build Pinwheel.Hardware.Library
lake env lean -DwarningAsError=true --run test/MemoryCommandFlops.lean
lake env lean -DwarningAsError=true test/MemoryCommandContracts.lean
python3 scripts/check-memory-command.py --tag command-flops-local
python3 scripts/check-memory-command-artifact.py --tag command-artifact-local
python3 scripts/check-memory-command-artifact-negatives.py --tag command-negatives-local \
  --positive-report build/memory-command-artifact/command-artifact-local/report.json
```

The retained `build/memory-command/command-flops-01/report.json` passed four
address/data width configurations: 1/1, 1/8, 2/8 and 3/17. Across 1,412 edges,
an independent Python array oracle matched Lean structural replay and every
emitted RTL register plus pre/post-edge Q. Twelve actual RTL mutations were
rejected: ignored enable, reads on write edges and cleared held Q. Generic
synthesis used 8, 36, 106 and 430 cells respectively; these are not physical
area or timing results.

Synthesized RTL starts uninitialized. Full writes and a read establish its
state before Q is compared (1,396 checked edges). Unsynthesized RTL is also
checked throughout that prefix from explicitly chosen arbitrary words and Q.
The separate Lean oracle test covers 4,100 exhaustive state/input combinations,
9 directed edges and a 240-edge trace; the declaration audit checks 427 memory
declarations for standard axioms only. Semantic zero widths are tested in Lean;
the HDL emitter requires positive address and data widths.

Complete imported-RTL correspondence passed for the same four configurations
in `build/memory-command-artifact/private-imports-01/report.json`. The generated
`memory_trace` theorem relates every raw-input trace from arbitrary initial
words/Q to the command specification; `command_step` supplies the original
single-port command transition. Every register and output is included, and
the generated declarations pass the standard-axiom audit. Yosys and the
restricted JSON interpretation remain trusted.

`build/memory-command-artifact-negatives/private-imports-01/report.json`
binds that positive receipt and rejects an inverted output and an inverted
word next-state expression at Lean's semantic proof stage. Each rejection is
paired with a separately kernel-checked concrete mismatch. The earlier
constant-output experiment was rejected during parsing after dead-state
removal; it is retained as a failed harness attempt and is not counted as a
semantic negative control.

## Streaming adapter and accelerator

Add a request/response adapter with one outstanding read and a held response
under downstream stalls. Reset cancels pending responses while preserving the
array. Reuse the common typed implementation and stream handshake operations,
with a memory-specific snapshot ledger. Then move a bounded range from one
source memory through proved stream components into a separate destination
memory.

The central completion theorem should establish that after `N` completed writes,
each address in the destination range contains the transform of the corresponding
initial source value; all other destination addresses are unchanged. Assumptions
include initialized source coverage and nonwrapping ranges. Reset may leave a
written prefix, but must suppress stale responses and further writes from the
aborted transfer. Eventual completion requires explicit service assumptions.

The executable `Memory.StreamModel` is implemented and tested. It reuses Q as
the held response and adds one pending bit. Both reads and writes wait behind
a blocked response; an old response may retire while a new read is accepted.
The proved ledger records each read's pre-edge memory value and conserves it
as delivered responses plus at most one pending response. Writes have no
response. Reset masks both handshakes and preserves the complete memory state,
including Q, while starting a new response-accounting epoch. Its tests cover
6,424 exhaustive cases, 11 directed edges and a 240-edge trace.

`Memory.StreamInterface`, `StreamFlops` and `StreamFlopsProofs` now implement
the physical adapter and its all-state refinement. The circuit instantiates
the command memory through expression substitution and adds exactly one bit.
The fixed-initial-state reset certificate is not applied to its state-preserving
reset. Its raw-state tests cover 18,464 exhaustive cases plus 13 directed and
240 trace edges; the retained audit checks 753 memory declarations.

```sh
lake build Pinwheel.Hardware.Library
lake env lean -DwarningAsError=true --run test/MemoryStreamModel.lean
lake env lean -DwarningAsError=true --run test/MemoryStreamFlops.lean
lake env lean -DwarningAsError=true test/MemoryStreamContracts.lean
python3 scripts/check-memory-stream.py --tag stream-memory-local
python3 scripts/check-memory-stream-artifact.py --tag stream-artifact-local
python3 scripts/check-memory-stream-artifact-negatives.py --tag stream-negatives-local \
  --positive-report build/memory-stream-artifact/stream-artifact-local/report.json
```

`build/memory-stream/stream-flops-01/report.json` passed the four command-memory
configurations. An independent Python array/pending-bit oracle records accepted
read snapshots, delivered responses and reset epochs. Every emitted register
and pre/post output agrees; synthesized outputs agree after a reset and full
initial writes establish observable state. All twelve actual RTL faults were
rejected: ignored response stalls, dropped pending state and a word incorrectly
cleared by reset.

Imported RTL certification passed in
`build/memory-stream-artifact/private-imports-01/report.json`: 133 local
equalities and all 36 typed register/output endpoints across the four cases.
The composed theorems cover arbitrary-state traces, traces after protocol reset,
preservation of every memory word and Q, and clearing of pending. The matching
`build/memory-stream-artifact-negatives/private-imports-01/report.json`
rejects active-response inversion, pending/word next-state corruption and a
word erased by reset. Each rejection includes a kernel-checked concrete
counterexample. The RTL interpretation trust boundary is unchanged.

### First transfer controller

Use separate source and destination memories, a common address width, and
`Stream.Map wi wo` for the transform. That existing API already packages the
pure function, register-free expression and universal correctness proof.
The first reusable circuit has explicit source read-request/response ports and
destination write-request/ready ports. A composed theorem connects it to two
`StreamFlops` memories.

Runtime commands carry source base, destination base and an `a+1`-bit length.
Accept start only while idle. Check both nonwrapping ranges without truncated
addition: `length ≤ 2^a - base`. Invalid commands pulse error and send no memory
request; zero length pulses done immediately at its acceptance edge. A start
held valid is accepted again whenever ready, following ordinary handshake
semantics. Busy commands cannot replace the latched configuration.

`Memory.TransferRange` implements the checked range codec, nonwrapping and
injective indexing, and incremental destination-prefix update algebra.
`Patched` describes the current memory independently of its representation;
`patch_step` extends that invariant after one accepted write. The copy
specialization transforms a fixed source snapshot and preserves every
destination word outside the written prefix. It does not assume in-place
source stability. Tests cover 682 raw range encodings and 43,203 prefix checks,
including zero/full-depth ranges, all small source/destination arrays and
modular transforms. Its 84 declarations pass the standard-axiom audit.

The serial controller has Idle, IssueRead and Transfer phases. IssueRead waits
for the source read acceptance. Transfer couples source-response retirement to
destination-write acceptance and applies `Map` combinationally. Source Q holds
the payload under stalls; no additional payload register is needed. A completed
write increments the index and either issues the next read or pulses done.
Reset wins over every handshake, clears protocol state and preserves both
arrays/Q values. Unused physical phase encodings must have explicit safe
recovery behavior.

`Memory.TransferModel` implements both the open controller and its closed
composition with two backpressured memories. Its parameterized `Session`
invariant relates each committed write to the initial source snapshot and the
destination's written prefix. `session_step` preserves the invariant and
`completed_patch` establishes the full transformed range. Every destination
word outside the written prefix retains its initial value.

`started_complete` proves completion after two further edges per word after a
valid start; zero length completes on the acceptance edge. The closed composition
supplies the memory service internally. Open-controller progress instead uses
an explicit `Service` predicate: `work_step` decreases remaining work by one
on a service edge, while `work_stalled` preserves it. These theorems do not
assume an arbitrary external memory eventually responds or holds responses
stable; an external adapter must supply that contract.

`abort_preserves_prefix` preserves both arrays and Q registers, cancels the
pending protocol state, and retains the committed-prefix property after reset.
`no_start_run` excludes stale work after abort until a new start. Valid start
requires the source to have no pending response. Idle control alone is not a
drain guarantee; reset or the later host wrapper must establish this condition.
The destination response is drained under the composition's exclusive ownership.

```sh
lake build Pinwheel.Hardware.Memory.TransferModel
lake env lean -DwarningAsError=true --run test/MemoryTransferModel.lean
```

Validation compares pre/post outputs and the complete composed state with an
independent integer/array oracle: 14,474 exhaustive-command edges, 100
abort/busy/restart edges, and 12 open-controller stalled edges. Cases include
zero/full-depth/invalid ranges, semantic zero widths, all small memory contents,
an 8-to-4-bit transform, held start, and reset with incoherent protocol state.
All 308 model declarations pass the standard-axiom audit.

### Open controller hardware

`Memory.TransferInterface` exposes nine inputs and eleven outputs, including
the auxiliary adapter reset. `Memory.TransferCircuit` uses seven registers:
phase, source/destination bases, length, completed index and done/error pulses.
Length and index retain `a+1` bits, so full-capacity transfers do not truncate.
Range admission subtracts a widened base from capacity before comparing length.
There is no payload register.

`TransferCircuitProofs` supplies parameterized step/output correspondence,
`Implementation`, arbitrary-state reset recovery and reset-initialized traces.
Normal refinement uses `Control.Valid`; output correspondence needs no validity
premise. Reserved phase 3 suppresses all transactions, asserts `memory_reset`,
and recovers empty control with an error pulse. `paired_memory_reset` proves
that the canonical two-adapter bindings clear both pending bits while preserving
every word and Q. An external memory implementation must honor the same contract.

```sh
python3 scripts/check-memory-transfer.py --tag controller-local
python3 scripts/check-memory-transfer-artifact.py --tag controller-artifact-local
python3 scripts/check-memory-transfer-artifact-negatives.py --tag controller-negatives-local \
  --positive-report build/memory-transfer-artifact/controller-artifact-local/report.json
```

The structural tests check 21,320 edges, including semantic zero widths,
raw command ranges/handshakes and mixed-width traces. The broad imported-memory
audit checks 1,462 declarations with standard axioms only.
`build/memory-transfer/controller-matrix-01/report.json` passes independent
integer-oracle replay of all emitted registers/pre/post outputs and synthesized
external outputs: 1,950 edges per form, eight additional raw phase-3 recovery
edges, and 20 actual RTL faults rejected with concrete value mismatches.

| Address/input/output widths | Replay edges per form | Generic synthesized cells |
| --- | ---: | ---: |
| 1 / 1 / 1 | 393 | 68 |
| 2 / 8 / 8 | 459 | 104 |
| 3 / 8 / 4 | 639 | 148 |
| 2 / 4 / 17 | 459 | 101 |

The tested transform inverts input bits and then zero-extends or truncates to
the output width. The implementation theorem itself accepts any proved Map.
These cell counts are not a matched independent baseline or physical timing result.

`build/memory-transfer-artifact/controller-artifact-02/report.json` certifies
259 local equalities and all 72 typed register/output endpoints, plus the
reset-initialized open-controller trace theorem. Yosys `pmuxtree` normalizes its
case-derived parallel mux before restricted JSON import; pre-normalization JSON
is retained. Each configuration's selectors compare the same raw phase bits
with 2, 1 and 0, so they are mutually exclusive for every binary state, including
phase 3. The first attempt is retained as a failed unsupported-`$pmux` import.
The importer was not relaxed, and normalization remains inside the stated
trusted Yosys interpretation boundary.

`build/memory-transfer-artifact-negatives/controller-negatives-01/report.json`
rejects active write-payload corruption and erased progress-index updates through
semantic local-proof failures. Both include kernel-checked concrete mismatches
with a destination write actively offered and ready. No whole-accelerator,
external-memory, post-synthesis proof or physical behavior follows from these
open-controller certificates.

### Host ownership and readback

`Memory.TransferHostModel` adds host loading and readback around the same state.
An offered start blocks new host requests; existing responses remain visible
and retire only when their host is ready. Start is accepted on a later edge
with both pre-edge pending bits clear. Busy edges exclusively reserve both
memories for the controller, so host offers cannot delay an active coherent
session. After completion, ordinary host traffic can resume immediately.

The wrapper proves pending-free start readiness, independent idle memory effects,
drain-before-start, accepted-start and busy-step equality with the closed model,
lifted session/completion proofs, reset prefix preservation, and absence of stale
controller work after abort. Invalid accepted commands preserve both complete
memory states while changing controller status/configuration. Quiet continuation
preserves a completed session; new idle host writes start a different memory history.

```sh
lake build Pinwheel.Hardware.Memory.TransferHostModel
lake env lean -DwarningAsError=true --run test/MemoryTransferHostModel.lean
```

Its independent integer/array oracle checks 18,015 complete-state and pre/post
observation edges: loading/transfer/readback, pending responses before start,
exhaustive idle host commands, range commands, abort/recovery and seeded traffic.
All 113 wrapper declarations pass the standard-axiom audit. Host readback also
keeps destination storage observable to synthesis.

### Host accelerator hardware

`TransferHostInterface`, `TransferHostCircuit` and `TransferHostCircuitProofs`
implement the wrapper using the existing open controller and two `StreamFlops`
instances. All seven control registers, every source/destination word, both Q
registers and both pending bits have typed identities. The physical wrapper has
15 inputs and 10 outputs. Idle host requests, drain-before-start, exclusive
transfer ownership and post-completion readback follow the existing host model.

The parameterized implementation theorem needs only the control validity
invariant; it permits arbitrary memory contents, held values and pending bits.
Reset and reserved-phase recovery are proved separately from arbitrary register
bits, preserving both complete memories including Q. They cancel pending
responses and restore an idle controller; reserved-phase recovery additionally
reports an error. There is no fixed initial memory image.

`RunRefinement` extends the common certificate API with final encoded state
correspondence. Its downstream host test recovers entire memory states after an
arbitrary reset and input history, including written words absent from current
outputs. This does not require an injective encoding or recovery of erased ghosts.

```sh
lake build Pinwheel.Hardware.Library
lake env lean -DwarningAsError=true --run test/MemoryTransferHostCircuit.lean
lake env lean -DwarningAsError=true --run test/HardwareRunRefinement.lean
python3 -m unittest discover -s test -p 'test_transfer_host_validation.py'
python3 -m unittest discover -s test -p 'test_readback_control_proofs.py'
python3 scripts/check-memory-transfer-host.py --tag host-local
python3 scripts/check-memory-transfer-host-artifact.py --tag host-artifact-local
python3 scripts/check-memory-transfer-host-artifact-negatives.py --tag host-negatives-local \
  --positive-report build/memory-transfer-host-artifact/host-artifact-local/report.json
```

The structural test checks 2,701 complete-state/pre/post-output edges and 10 raw
reset/recovery cases; its 421 declarations use standard axioms only. The generic
final-state specialization has a separate 16-declaration audit.

`build/memory-transfer-host/host-matrix-01/report.json` records 2,532 replay
edges per RTL form, 141 completed/aborted job snapshots and eight additional raw
reserved-phase recovery edges. Emitted RTL checks every register and pre/post
output. Synthesized replay observes outputs after loading every memory word
through the host interface. Independent read-response ledgers retain the value
sampled at acceptance; per-job snapshots check every destination prefix and
completion/abort behavior. All 24 actual RTL faults produce complete binary
trace mismatches, covering disabled start, ignored host stalls, active readback
corruption, erased progress, reset-erased memory and a busy host-write leak.

| Address bits | Input/output bits | Registers | Replay edges/form | Generic cells | Artifact equalities/endpoints |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 1/1 | 15 | 365 | 128 | 109/25 |
| 2 | 8/8 | 19 | 541 | 403 | 118/29 |
| 3 | 8/4 | 27 | 1,085 | 501 | 133/37 |
| 2 | 4/17 | 19 | 541 | 463 | 118/29 |

`build/memory-transfer-host-artifact/host-artifact-03/report.json` certifies all
120 endpoints through 478 local equalities. Each configuration additionally
checks encoded traces, encoded final state, memory-preserving post-reset traces
and final state, and reserved-phase recovery traces. A proof-search helper
exhaustively splits two-bit controls into all four encodings; it changes tactics
only and introduces no legal-state restriction. The full generated declarations
pass the standard-axiom audit. Yosys `proc`/`pmuxtree` normalization and the
restricted JSON interpretation remain trusted; pre-normalization JSON is retained.
The imported certificate covers unsynthesized binary RTL. Generic cell counts
are not a baseline comparison, physical area or timing qualification.

`build/memory-transfer-host-artifact-negatives/host-negatives-02/report.json`
binds that exact positive receipt and rejects three actual RTL corruptions at
local semantic proof obligations. Kernel-checked witnesses show reset erasing a
word (165 to 0), an unaccepted host write leaking into a busy transfer (10 to
231), and corruption of an active read response (60 to 195). The witness also
checks the corresponding reset, busy/not-ready or valid/ready condition.
Malformed import, timeout and parser failure do not count as semantic rejection.

### Accelerator synthesis comparison

`transfer_host_baseline.py` constructs an independent conventional SV array/FSM
implementation from the host contract. It does not inspect generated Lean
expressions or RTL. The matched baseline receipt
`build/memory-transfer-host-baseline/baseline-matrix-02/report.json` checks the
same 2,532 edges at every unsynthesized register and pre/post output, synthesized
outputs, eight raw recovery edges and 12 actual RTL faults. Synthesis uses the
same Yosys flow; longest generic paths are measured on the exact synthesized
cell graph, excluding flip-flops.

| Address/input/output bits | Cells: Lean / baseline | Generic logic depth: Lean / baseline |
| --- | ---: | ---: |
| 1/1/1 | 128 / 115 | 9 / 8 |
| 2/8/8 | 403 / 307 | 11 / 9 |
| 3/8/4 | 501 / 413 | 12 / 10 |
| 2/4/17 | 463 / 358 | 11 / 8 |

`build/memory-transfer-host-technology/mapped-matrix-02/report.json` maps both
implementations independently at the pinned typical and slow IHP CMOS5L corners,
with matching drive, 10 fF output load and 10,000 ps ABC target. All 16 mapped
circuits pass functional replay (10,128 edges total). Functional cell models
come from the same hashed Liberty files; actual merged ABC library inputs are
retained in a fresh bundle-local SCL cache.

Typical-corner results:

| Address/input/output bits | Cell area sum: Lean / baseline (library units) | ABC combinational delay: Lean / baseline (ps) |
| --- | ---: | ---: |
| 1/1/1 | 1,846.91 / 1,954.03 | 1,102.23 / 920.20 |
| 2/8/8 | 8,413.11 / 8,511.20 | 1,667.85 / 1,207.37 |
| 3/8/4 | 11,182.49 / 11,566.46 | 1,624.45 / 1,239.57 |
| 2/4/17 | 10,345.41 / 10,483.45 | 1,732.58 / 1,417.84 |

Mapped cell area is 1.2–5.5% lower for the Lean composition, despite its larger
generic cell count. The material regression is delay: approximately 20–40%
higher across both corners. The generic longest path exposes the chain from
reset/start readiness through accepted-start and host ownership into the source
RAM's address/read selection. The phase-only ownership candidate below addresses
that path while retaining the certified reference and its measurements.

```sh
python3 scripts/check-memory-transfer-host-baseline.py --tag host-baseline-local \
  --positive-report build/memory-transfer-host/host-local/report.json
python3 scripts/check-memory-transfer-host-technology.py --tag host-mapped-local \
  --positive-report build/memory-transfer-host-baseline/host-baseline-local/report.json
```

The technology files are pinned by `tools/technology-library.json` and use the
existing technology-library installer. Area is in the library's unspecified
area units, not an asserted square-micron measure. ABC estimates omit sequential
setup/clock-to-Q, clock trees, placement, routed parasitics and full STA; they do
not establish clock frequency or physical qualification. Baseline simulation
and mapped replay do not provide a baseline or post-synthesis kernel proof.

### Proved ownership optimization

`Memory.TransferHostOwnershipCandidate` selects host memory inputs whenever the
controller is idle. It removes accepted-start logic from the memory ownership
mux. At a start acceptance, both pending bits are already zero and start-valid
suppresses new host requests, so either branch performs the same idle memory
transition. The parameterized `step_eq` and `output_eq` prove equivalence for
every raw binary input/register state, including malformed controller states;
there is no reachable-state or valid-controller premise. Trace, final-state,
memory-preserving reset and reserved-phase recovery proofs follow through the
original certificates.

Import this optional constructor directly:

```lean
import Pinwheel.Hardware.Memory.TransferHostOwnershipCandidate
```

`test/MemoryTransferHostOwnership.lean` checks 20,480 raw phase/pending/handshake
combinations, including zero semantic widths, and audits 50 declarations.
`build/memory-transfer-host-ownership/ownership-matrix-01/report.json` passes the
same 2,532 edges per form, all emitted registers/pre/post outputs, synthesized
outputs, eight recovery edges and 24 actual RTL faults. The source receipt and
independent baseline remain immutable inputs to the comparison.

`build/memory-transfer-host-ownership-artifact/ownership-artifact-01/report.json`
checks 470 local equalities and all 120 endpoints, with the candidate itself as
the source of every `rfl` endpoint binding. All four configurations also carry
encoded and reset final-state proofs, reset traces and reserved-phase recovery
traces. The corresponding `ownership-negatives-01` receipt under
`build/memory-transfer-host-ownership-artifact-negatives` rejects the reset-word,
busy-host-write and active-readback faults with exact audited kernel witnesses.

The matched mapping receipt is
`build/memory-transfer-host-ownership-technology/ownership-mapped-01/report.json`.
It independently remaps reference, candidate and baseline at both corners and
replays all 24 circuits (15,192 edges total). Typical results:

| Address/input/output bits | Candidate cells / generic depth | Candidate cell area (library units) | ABC delay: reference / candidate / baseline (ps) |
| --- | ---: | ---: | ---: |
| 1/1/1 | 128 / 8 | 1,859.46 | 1,102.23 / 1,038.27 / 920.20 |
| 2/8/8 | 404 / 10 | 8,504.02 | 1,667.85 / 1,438.47 / 1,207.37 |
| 3/8/4 | 500 / 12 | 11,037.45 | 1,624.45 / 1,551.21 / 1,239.57 |
| 2/4/17 | 465 / 10 | 10,461.75 | 1,732.58 / 1,638.27 / 1,417.84 |

The candidate improves ABC delay 4.5–14.3% across the tested corners; mapped
area changes by −1.30% to +1.12% relative to the reference. It remains roughly
12–25% slower than the independent baseline. The same mapping assumptions and
limits apply; full timing checks and any further optimization remain separate.

```sh
lake env lean -DwarningAsError=true --run test/MemoryTransferHostOwnership.lean
python3 scripts/check-memory-transfer-host-ownership.py --tag ownership-local \
  --positive-report build/memory-transfer-host-baseline/host-baseline-local/report.json
python3 scripts/check-memory-transfer-host-ownership-artifact.py --tag ownership-artifact-local
python3 scripts/check-memory-transfer-host-ownership-artifact-negatives.py --tag ownership-negatives-local \
  --positive-report build/memory-transfer-host-ownership-artifact/ownership-artifact-local/report.json
python3 scripts/check-memory-transfer-host-ownership-technology.py --tag ownership-mapped-local \
  --positive-report build/memory-transfer-host-ownership/ownership-local/report.json
```

### Pure byte-lane semantics

`Memory.ByteAccess` defines accesses within one 32-bit little-endian word.
Two raw size bits encode byte, halfword, word or reserved; two offset bits select
a lane. Halfwords require offset 0 or 2 and words require offset 0. Reserved
size takes fault priority over alignment. Loads sign or zero extend byte/halfword
values; stores use the low data bytes and retain every untouched lane.

The public operations return explicit faults. A faulting store's `StoreResult`
contains the unchanged original word; a memory adapter must additionally suppress
the actual read/write command. This pure layer includes no address mapping,
ownership, handshake, MMIO or reset behavior. Its universal theorems establish
raw classification, alignment fit, retained/written bytes, load-after-store,
sign extension and word preservation on faults.

```sh
lake build Pinwheel.Hardware.Library
lake env lean -DwarningAsError=true --run test/MemoryByteAccess.lean
```

The test checks 11,520 independent arithmetic-reference cases (division and
remainders, rather than the implementation's lane/pack operations), both load
modes, stores and later all-lane readback. Eight semantic mutation controls are
detected; 166 declarations pass the standard-axiom audit. Transactional byte RAM
composition and its effect/acknowledgement contract are the next integration step.

External SRAM remains a supplied implementation contract. Digital trace proofs
do not independently qualify a macro's electrical behavior. Native byte-enable
RAMs, non-power-of-two depth, multiple outstanding reads and shared
source/destination storage need separate implementation contracts.
