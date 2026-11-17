# Choosing the FIFO in an increment lane

The public stream library lets a caller choose the FIFO storage architecture
when constructing an increment lane. Both versions use the same proof of
ordering, including stalls and resets. The [Lean client](../../examples/FifoSubstitutionSketch.lean)
instantiates that proof for every payload width and every pipeline depth.

## The client

[IndependentLanes](../../examples/IndependentLanes.lean) chooses its FIFO inside
`Stream.Design.buffered`. To choose the implementation explicitly, use the
following definitions with `import Pinwheel.Hardware.Library`.

```lean
open Pinwheel.Hardware Stream BackendAPI

def withShift := bufferedMap (shift 17 3 (by decide)) (increment 17) 1
def withRing  := bufferedMap (CircularFifo3.backend 17) (increment 17) 1
```

Each result contains the circuit, a typed register interface, its refinement
proof and recovery from arbitrary register bits on a reset edge.
`buffered_transactions` gives both lanes the following observable guarantee.

## What the caller can observe

For every finite prefix since this lane’s last reset, including prefixes ending
in a stall, the client law is

```text
map (add one modulo 2^width) accepted = emitted ++ still pending in delivery order
```

Both histories count actual pre-edge handshakes. Reset discards the old pending
suffix. Downstream readiness is needed to conclude that the suffix eventually
drains. The example spells out this proposition as `LaneLaw` on the circuit
returned by `lane`. Its pending suffix comes from the existing queue and pipeline
specification.

For the first substitution, both FIFOs implement the **same cycle contract**.
At depth three, if the queue holds `[a,b,c]`, the receiver is ready and the sender
offers `d`, the edge transfers `a`, accepts `d` and leaves `[b,c,d]`. An empty
queue accepts a first word for a later edge. A circular implementation must
wrap at three. It can preserve inactive storage across reset and mask its data
output when invalid, as required by the existing physical pin encoding. A
synchronous-memory variant with different admission or latency would need a
separate transaction-level substitution law.

## Where the proofs live

- [Backend](../../Pinwheel/Hardware/Stream/Backend.lean) packages a circuit with
  a relation to a stream machine. The shift FIFO reuses its existing encoding
  proof. Any two backends for the same FIFO model have equal pre/post pin traces
  for all inputs following an initial reset edge.
- [Serial composition](../../Pinwheel/Hardware/Stream/BackendSerial.lean) proves
  the product of two backend relations is preserved by the existing acyclic
  ready/offer wiring. Each child receives the actual bound inputs and reset.
- [Buffered maps](../../Pinwheel/Hardware/Stream/BackendLane.lean) connect a
  replaceable FIFO to the existing mapped pipeline. The transaction proof
  works for any certified payload map.
- [CircularFifo3](../../Pinwheel/Hardware/Stream/CircularFifo3.lean) stores three
  stationary words, two wrapping pointers and an occupancy count. Its relation
  reads occupied words in circular order and allows arbitrary contents elsewhere.
  The proof covers all twelve reachable pointer/occupancy combinations, every
  input control combination and symbolic payload values of arbitrary width.
  Cold reset also covers malformed pointer and count combinations.

Recheck the source proof, example and focused simulation using the pinned Lean
toolchain.

```sh
lake build Pinwheel.Hardware.Library
lake env lean -DwarningAsError=true examples/FifoSubstitutionSketch.lean
lake env lean -DwarningAsError=true --run test/FifoSubstitution.lean
```

The simulation checks all six physical registers through wraparound, a blocked
write, full-rate replacement and reset with retained storage. It also runs both
composed lanes through cancellation, stalls, repeated payloads and modular
overflow. Emitted-RTL certificates and matched synthesis measurements for these
instances remain future work.
