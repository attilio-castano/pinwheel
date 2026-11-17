# Using the Lean hardware library

Import the reusable library without importing Pinwheel's protocol processor or
physical-design packages:

```lean
import Pinwheel.Hardware.Library
open Pinwheel.Hardware
```

The library is under active development. It currently covers synchronous
two-state circuits, complete typed interfaces, stream composition, independent
banks, arbitration, a buffered multiport switch and exclusive-command memory.
The memory adapter also supports backpressured requests and read responses.
A memory-transfer specification, completion proof and certified host accelerator
are available; comparative synthesis and processor integration are ongoing campaigns.

## Construction and proof layers

`Expr I R width` describes combinational logic over typed input and register
families. `Circuit I R O` supplies every next-register and output expression.
Expression substitution (`Expr.bind`) instantiates proved components without
textual wiring. All next-register expressions read the same pre-edge snapshot.

`WordOps` adds modular addition, word OR/XOR, signed comparison and fixed or
variable logical/arithmetic shifts as ordinary expression trees. Universal
evaluation and substitution theorems cover every width, including zero.
Variable amounts are unsigned and unmasked: logical overshifts produce zero,
and arithmetic overshifts replicate the sign bit. An ISA-specific low-bit mask
must be supplied explicitly. The barrel network uses existing slices, muxes and
fixed shifts, so it adds no primitive or emitter interpretation.

```sh
lake env lean -DwarningAsError=true --run test/HardwareWordOps.lean
```

The independent integer campaign checks 2,909 operand pairs and 11,697 shift
cases, including zero widths and overshifts, and rejects eight actual expression
faults. All 126 audited declarations use standard axioms only.

`WordALU` selects those operations at runtime using a four-bit control. Codes
0–9 denote add, subtract, AND, OR, XOR, signed less-than, unsigned less-than,
left shift, logical right shift and arithmetic right shift. Codes 10–15 return
zero and deassert validity. Operand width and shift-amount width are independent;
all raw selector values have universal evaluation/substitution proofs. Validity
reports selector legality, not arithmetic overflow or an overshift.

The separate `Processor.RV32I.ALU` adapter proves agreement with the instruction
semantics, including explicit low-five-bit register shifts and signed 12-bit
immediates for SLTIU. The public generic import does not pull in processor modules.

```sh
lake build Pinwheel.Hardware.Processor.RV32I.ALU
lake env lean -DwarningAsError=true --run test/HardwareWordALU.lean
```

The campaign checks 147,632 generic runtime-selector cases and 31,344 RV32
adapter cases against integer oracles, and rejects twelve actual expression
faults. The 293-declaration audit uses standard axioms only. These are structural
expression proofs; complete processor decoding and RTL evidence remain separate.

`AddressWindow` checks the entire positive access footprint against a validated
half-open window. It widens addresses and arithmetic to `w+1` bits, so the upper
bound may equal `2^w` and an overflowing access cannot wrap into the window.
Every width, including zero, has universal evaluation and substitution proofs.
The local-offset theorem requires successful admission before narrowing.
`Processor.AddressDecode` specializes this API to checked processor layouts and
proves complete runtime routing against `AddressMap`, including fault priority,
permissions and invalid raw kind/size controls.

```sh
lake build Pinwheel.Hardware.Processor.AddressDecode
lake env lean -DwarningAsError=true --run test/HardwareAddressDecode.lean
```

The independent integer/table oracle checks 505 window configurations, 43,275
complete footprints and 103,888 routing cases, including relocated regions and
an upper endpoint exactly at `2^32`. Eleven actual expression faults are rejected;
all 187 audited declarations use standard axioms only. This is structural
combinational evidence; RTL replay/certification will be part of CPU integration.

`RegisterFile` provides two combinational read ports and one synchronous write
port for arbitrary address/data widths. Address zero always reads zero and has
no storage; the remaining `2^a - 1` words use the existing balanced read-mux
construction. Reset wins over writing. Reads observe the pre-edge bank even
while reset is asserted, then observe zero after the reset edge. There is no
write-through forwarding. Complete step/output/reset/trace and register-update
proofs cover arbitrary raw state, including the zero-width Lean boundaries.

`Processor.RV32I.RegisterFile` specializes it to 31 stored 32-bit registers and
proves agreement with the architectural register operations. Writeback scheduling
and retirement remain CPU obligations.

```sh
lake build Pinwheel.Hardware.Processor.RV32I.RegisterFile
lake env lean -DwarningAsError=true --run test/HardwareRegisterFile.lean
```

The integer/array oracle checks 70,588 exhaustive raw edges, 10,584 mixed-width
trace edges and 5,120 RV32 projection edges, rejecting twelve expression faults.
All 156 audited declarations use standard axioms only. Positive-width RTL export,
artifact correspondence and synthesis measurements remain separate gates.

`Interface P` completely enumerates a typed family and proves inverse lookup and
unique names. It drives traversal, emission, observation and imported endpoint
assembly. `Bank count P` replicates an interface; `Bank.circuit` independently
replicates a circuit. `Implementation.bank` transfers the component proof to
arbitrary bank size without inspecting its registers.

`Timed.Component` defines specification transitions and observations.
`Implementation circuit spec` packages a valid-state predicate, state encoding
and universal state/output correspondence. Its encoding may erase logical
provenance. `Implementation.Reset` separately establishes initialization from
arbitrary register bits. This interface is shared by ordinary stream components
and the multiport switch.

`Implementation.run_eq` and `Artifact.Correspondence.encoded_run` additionally
transport the final represented state through any finite input history. This
covers memory contents and held read values that need not appear on a current
output. The conclusion is equality after encoding; it does not assume that
erased logical provenance can be recovered from physical registers.

`DecodedImplementation circuit spec` supports the other common representation:
a physical-state projection `view`, which may forget inactive metadata. Several
raw register states can represent one logical state. The certificate proves
preservation of a raw-state invariant, projected next-state equality and output
equality. Its trace and final-state theorems compose with an explicit
`Artifact.Correspondence`; they do not require an inverse encoding. This lets a
component retain unused request bits instead of clearing them merely to obtain
a canonical register image.

`DecodedImplementation.Reset` establishes the invariant from arbitrary raw
state and a logical initial state that may depend on retained pre-reset memory.
Separate component theorems still specify which physical bits reset preserves;
the projection alone makes no such claim. The regression demonstrates distinct
inactive metadata, equal traces, retained storage through reset, and projected
final-state transport, with 151 declarations audited for standard axioms only.

```sh
lake env lean -DwarningAsError=true --run test/HardwareDecodedImplementation.lean
```

`Timed.EventRefinement` adds architectural event paths above cycle models.
Its fixed event extractor and legal-input predicate are explicit parameters;
an empty event list preserves the abstract state. The finite-prefix theorem
composes with cycle-for-cycle refinement using an event-agreement proof.
`InitialCoverage` covers all admitted initial states and requires that domain
to be nonempty. Separate `ProgressBound` theorems bound service opportunities
without an outcome; eventual or bounded service remains an environment obligation.
Timer and device effects must remain visible even on edges without retirement.

The event-layer test applies this API to transfer read samples, actual writes,
abort and completion markers. It proves reconstruction of the memory effects;
the meaning of a completed destination range still comes from the transfer
session theorem, and this is not yet processor architectural refinement.

```sh
lake env lean -DwarningAsError=true --run test/HardwareEventRefinement.lean
```

`Memory.CommandInterface` provides complete typed enable/write/address/data/Q
interfaces. `Memory.CommandFlops` implements the exclusive single-port command
contract: read captures the addressed word in Q; write changes one word and
holds Q; disabled commands hold the entire state. Every physical state is
represented, so `implementation` and `trace_correct` require no initialization
invariant. There is no reset or implicit zero-filled memory. Its power-of-two
capacity makes every address-bit pattern legal.

`Memory.StreamFlops` adds one pending bit and reuses Q for its held response.
It can retire a response while accepting the next read. Its memory-specific
ledger relates delivered responses to the values sampled when reads were
accepted; writes produce no response. Reset cancels pending responses while
preserving words and Q, so this component uses a state-preserving reset theorem
instead of `Implementation.Reset`'s fixed initial state. The raw-input
`implementation` and `trace_correct` still use the shared certificate API.

`Memory.ByteAccess` supplies pure 32-bit little-endian byte, halfword and word
operations. It checks all raw size/offset encodings, sign or zero extends loads,
preserves untouched store bytes and returns the original word on faults.
Its universal lane/readback theorems are a building block for a transactional
memory adapter; they do not by themselves suppress bus or device side effects.

`Memory.ByteAdapterModel` composes those operations with the existing exclusive
word-RAM contract. It permits one outstanding request, samples the old word into
RAM Q at request acceptance, and commits a store on the same edge as response
acceptance. A blocked acknowledgement performs no write. Faults issue no RAM
command; reset drops pending work while retaining words/Q. Its snapshot and
byte-preservation proofs require exclusive ownership, so this model is not an
MMIO adapter.

`Memory.ByteAdapterCircuit` reuses `CommandFlops` storage and Q, adding six
retained request fields and one pending bit. Its `DecodedImplementation` proves
the functional projection and all output pins for arbitrary raw states. Inactive
metadata is retained, so there is deliberately no canonical encoding requirement.
Reset preserves words, Q and metadata, clears pending, and masks all outputs.
It also establishes the stronger owned-word snapshot invariant needed for
atomic byte-access effects. Emitted and synthesized RTL replay passes three
memory depths with an independent byte-level oracle, explicit full-memory
loading and 24 actual RTL corruption controls. Complete imported unsynthesized
artifact certificates cover all 50 state/output endpoints across those depths;
four actual RTL faults also fail the local proofs with kernel-checked witnesses.

`Memory.ByteAdapterEffects` relates its actual completion events to atomic RAM
accesses. Every delivered read, store acknowledgement and fault remains in the
event stream with the completing request. Under the snapshot invariant, replaying
those events reconstructs the final memory contents. A separate theorem folds
all actual full-word writes across arbitrary histories, including resets, without
a validity premise. Reset emits no completion and never rolls back prior writes.
These are finite-prefix safety results; consumer readiness is still required
for completion.

`Memory.ByteAdapterRefinement` connects those atomic effects to the hardware's
actual response-valid/code/data pins and retained request fields. Event replay
reconstructs final RAM contents from every snapshot-valid raw state, and reset
recovers arbitrary raw states. Initial coverage admits arbitrary words, Q and
inactive metadata. Artifact transport keeps complete RTL correspondence as an
explicit premise; it does not substitute model-expected responses for observed
hardware responses.

The byte artifact campaign discharges this premise for address widths 1, 2 and 3,
including actual-event replay, arbitrary-state reset recovery and retained memory.
Snapshot validity remains explicit for atomic effects. The [memory campaign](lean-hardware-memory-plan.md)
records reproducible commands and the Yosys/JSON interpretation boundary.

`Memory.TransferRange` supplies checked nonwrapping ranges and incremental
memory-patch proofs. `Memory.TransferModel` composes two exclusively owned
backpressured memories with a serial controller and a proved `Stream.Map wi wo`
transform. Its completion theorem covers arbitrary source/destination snapshots
and preserves words outside the destination range. Reset aborts future work
while preserving completed writes. `Memory.TransferCircuit` implements the open
controller using seven registers and any proved `Stream.Map wi wo`, with generic
state/output refinement and arbitrary-state reset recovery. It stores no payload;
the source memory holds a stalled response. Its auxiliary `memory_reset` output
also cancels attached adapter responses during reserved-phase recovery while
preserving memory words/Q. See the memory campaign for start/drain and
external-service assumptions and the complete controller RTL certificates.

`Memory.TransferHostModel` adds independent host memory channels for loading and
readback. It drains outstanding host responses before start acceptance and gives
an active transfer exclusive memory ownership. Its completion and abort proofs
reuse the closed transfer model. `Memory.TransferHostCircuit` composes the open
controller with two existing `StreamFlops` memories. Its parameterized
implementation, trace and final-state proofs accept arbitrary host traffic.
Reset and reserved-phase recovery preserve arbitrary memory words and Q while
clearing pending responses; reset is state-dependent, with no implicit memory
image. Four emitted RTL configurations carry complete artifact, reset-trace,
recovery-trace and final-state certificates. This uses the existing two-state
RTL interpretation boundary; synthesis replay is a separate check.

`Arbitration.OneHotSelect` shares a round-robin winner decoder across arbitrary
payload and control selections. Its correctness theorem requires a legal
one-hot cursor and allows arbitrary request/value/fallback expressions. It is
an alternative to `RoundRobinMasked`, with documented synthesis tradeoffs.

`Stream.BufferedMerge` is a second arbitration/buffering integration:
multiple inputs feed one output holding register, with no input queues. It
directly composes round-robin selection and the elastic register. Its multiport
contract tracks source provenance, conservation and order; a persistent request
is accepted within N eligible refill opportunities. Downstream stalls do not
count as opportunities, and output delivery needs downstream service. Its
`Structural.circuit`, `implementation` and `resetCertificate` reuse the existing
one-hot selector and elastic circuit. Complete RTL artifact certificates cover
15 configurations through eight inputs and 17-bit payloads. The
[merge record](lean-hardware-buffered-merge.md) documents its interfaces,
provenance erasure, initialization boundary and validation commands.

`Artifact.Correspondence` compares a particular imported RTL interpretation with
every structural register/output expression. It composes with `Implementation`
or `DecodedImplementation` and reset recovery to obtain whole-trace
correspondence. Yosys and the restricted
JSON interpretation remain trusted boundaries. Simulation, artifact proof,
generic synthesis and physical timing are separate evidence levels.

Protocol contracts sit above this common implementation layer. A stream
`Certified` component includes its accepted/emitted/pending transaction law.
`Stream.Multiport.Contract` handles per-flow accounting across independently
handshaken lanes. Neither contract is forced onto all circuits.

Processor-specific checked routing is available by importing
`Pinwheel.Hardware.Processor.AddressMap`. It validates layouts before routing,
proves full byte footprints and permissions, and justifies local-address
narrowing with reconstruction and no-alias theorems. The
[processor contract](lean-hardware-processor-plan.md) records its environment
choices and independent validation.

## A client example

[`IndependentLanes.lean`](../../examples/IndependentLanes.lean) constructs a bank
of independently buffered increment pipelines using only the public import. It
proves trace correspondence for arbitrary lane count, payload width, FIFO depth,
pipeline depth, traffic and independent backpressure/reset histories by applying
the existing certificates. Its emitter instantiates three 17-bit lanes.

```sh
lake build Pinwheel.Hardware.Library
lake env lean --run examples/IndependentLanes.lean /tmp/independent-lanes.mlir
```

This demonstrates library composition without changes to internals. It does not
claim an RTL artifact certificate or physical timing result for that example.

See the [stream foundation](lean-stream-hardware.md),
[bundle/fork-join guide](lean-stream-graphs.md), and
[multiport switch record](lean-hardware-switch.md) for the corresponding
semantics, validation commands and current limitations. The
[memory campaign](lean-hardware-memory-plan.md) distinguishes its two existing
read/write contracts and records command-memory validation. The
[roadmap](lean-hardware-roadmap.md) records the remaining integration gates.
