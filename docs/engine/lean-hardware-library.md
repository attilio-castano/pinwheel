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
A memory-transfer specification and completion proof are available; its hardware
implementation and processor integration are ongoing campaigns.

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
while preserving completed writes. These model proofs currently precede the
physical controller implementation; see the memory campaign for start/drain
and external-service assumptions.

`Arbitration.OneHotSelect` shares a round-robin winner decoder across arbitrary
payload and control selections. Its correctness theorem requires a legal
one-hot cursor and allows arbitrary request/value/fallback expressions. It is
an alternative to `RoundRobinMasked`, with documented synthesis tradeoffs.

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
