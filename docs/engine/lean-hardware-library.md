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

`Stream.BufferedMerge` is a second arbitration/buffering integration model:
multiple inputs feed one output holding register, with no input queues. It
directly composes round-robin selection and the elastic register. Its multiport
contract tracks source provenance, conservation and order; a persistent request
is accepted within N eligible refill opportunities. Downstream stalls do not
count as opportunities, and output delivery needs downstream service. Physical
construction and RTL validation remain in progress.

`Artifact.Correspondence` compares a particular imported RTL interpretation with
every structural register/output expression. It composes with `Implementation`
and reset recovery to obtain whole-trace correspondence. Yosys and the restricted
JSON interpretation remain trusted boundaries. Simulation, artifact proof,
generic synthesis and physical timing are separate evidence levels.

Protocol contracts sit above this common implementation layer. A stream
`Certified` component includes its accepted/emitted/pending transaction law.
`Stream.Multiport.Contract` handles per-flow accounting across independently
handshaken lanes. Neither contract is forced onto all circuits.

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
