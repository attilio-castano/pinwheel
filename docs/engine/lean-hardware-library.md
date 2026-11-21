# Using the Lean hardware library

Import the reusable library without importing Pinwheel's protocol processor or
physical-design packages:

```lean
import Pinwheel.Hardware.Library
open Pinwheel.Hardware
```

The library is under active development. It currently covers synchronous
two-state circuits, complete typed interfaces, stream composition, independent
banks, arbitration, a buffered multiport switch, and synchronous memories.

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

`Implementation.run_eq` and `Artifact.Correspondence.encoded_run` carry final
represented state through a finite execution. This captures memory words and held
read data that may be invisible on the current output pins.
`DecodedImplementation` provides a projection from raw registers to a logical
state that can omit inactive request metadata. `Timed.EventRefinement` relates
effects sampled at completion to changes to the logical state.

`Artifact.Correspondence` compares a particular imported RTL interpretation with
every structural register/output expression. It composes with `Implementation`
and reset recovery to obtain whole-trace correspondence. Yosys and the restricted
JSON interpretation remain trusted boundaries. Simulation, artifact proof,
generic synthesis and physical timing are separate evidence levels.

Protocol contracts sit above this common implementation layer. A stream
`Certified` component includes its accepted/emitted/pending transaction law.
`Stream.Multiport.Contract` handles per-flow accounting across independently
handshaken lanes. Neither contract is forced onto all circuits.

## Memory and stream components

- `Memory.CommandFlops` provides exclusive command RAM. A read captures the
  addressed word in Q, a write holds Q, and a disabled command holds all state.
- `Memory.StreamFlops` adds a pending response. Reset cancels that response while
  preserving RAM contents and Q.
- `Memory.ByteAdapterCircuit` exposes byte, halfword, and word operations over
  command RAM. A store commits when its response is accepted. The adapter's
  event refinement reconstructs the memory effects from completed operations.
- `Memory.TransferHostExport` wires the host controller and two memories with
  `TypedHierarchy`. The imported RTL proof compares each next-state and output
  equation with the flat reference and carries memory preservation through
  reset and recovery.
- `Stream.BufferedMerge` uses one elastic output slot and round-robin arbitration.
  The multiport contract carries per-input ordering, conservation, and
  conditional fairness into the implementation.

The [memory campaign](lean-hardware-memory-plan.md) and
[buffered merge record](lean-hardware-buffered-merge.md) give the proof
assumptions, replay commands, and synthesis evidence for these components.

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

The [standalone lane client](../../examples/independent-lanes/LaneClient.lean)
uses its own Lake package with Pinwheel as a local dependency. It applies one
banked trace theorem to any FIFO implementing the lane's queue contract. A
synchronous reset of all lanes establishes the model from arbitrary register
bits. Thereafter, lane resets, input offers and downstream stalls may vary
independently on every edge.

From the Pinwheel checkout, use the pinned Lean toolchain, Python 3.12 or newer,
and the [pinned CAD tools](../../scripts/install-hardware-tools.py). Run the
whole default matrix with a fresh tag.

```sh
python3 -B scripts/install-hardware-tools.py
python3 -B scripts/check-independent-lanes.py --tag lanes-local
```

The command builds the Lake client, simulates the typed circuit in Lean, emits
SystemVerilog through CIRCT, and replays the RTL in Icarus against an independent
integer FIFO and elastic-stage model. Each lane exercises stalls, full-queue
replacement, modular wraparound, and reset with work pending. Replay checks the
first reset edge's post-edge outputs and both observations on every later edge.
Lean checks every imported next-register and output equation for arbitrary inputs
and raw state, then lifts correspondence to arbitrary traces after the initial
reset. The certificate uses the restricted Yosys JSON interpretation.

The default configurations are three 17-bit lanes with two elastic stages and
two 8-bit lanes with three stages. Both run once per FIFO backend. Repeat
`--config LANES,WIDTH,EXTRA` to choose a different matrix. `EXTRA` counts
stages after the increment stage. The report at
`build/independent-lanes/<tag>/report.json` records coverage, commands and hashes.

The lane and 2×2 switch clients use `TypedModule` to bind a circuit to its
complete input, register and output interfaces. Calling `emit` returns both
MLIR and the readback descriptor from those interfaces. The shared validation
runner derives its typed bindings from the same Lean declaration and checks
every ordinal, width and label. It checks that both replay and correspondence
reject a same-width output swap on the shift variants with at least two lanes.
Clients supply their traffic and reset theorem. The lane simulator materializes
each register snapshot to avoid reevaluating prior edges.

The [FIFO substitution guide](lean-hardware-fifo-substitution.md) records the
shared transaction theorem and the 2×2 packet-switch replay and synthesis
comparison.

`TypedHierarchy` connects single-clock `TypedModule` instances. Each child
binds width-indexed pins to external ports or declared nets and binds its local
registers into the flat reference. The generated wrapper and physical register
paths use those same bindings. The [switch hierarchy](lean-hardware-switch.md#typed-switch-hierarchy)
shows how to check the actual flattened RTL against that reference.

See the [stream foundation](lean-stream-hardware.md),
[bundle/fork-join guide](lean-stream-graphs.md), and
[multiport switch record](lean-hardware-switch.md) for the corresponding
semantics, validation commands and current limitations. The
[roadmap](lean-hardware-roadmap.md) records the remaining integration gates.
