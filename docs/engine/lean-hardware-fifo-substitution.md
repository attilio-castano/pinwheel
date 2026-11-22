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
overflow. The standalone client described in the [library guide](lean-hardware-library.md)
checks emitted lane RTL against the same contract.

## Replacing the input queues in a packet switch

The switch now takes a FIFO as an argument. For example, these definitions
build the same two-input, two-output switch with four-bit payloads. Each queue
stores a five-bit word consisting of a destination bit and the payload.

```lean
import Pinwheel.Hardware.Library
open Pinwheel.Hardware

def dest : Switch.Physical.DestinationEncoding 2 := ⟨1, by decide, by decide⟩
def switchWith (fifo : Stream.BackendAPI.Fifo 5 3) :=
  Switch.WithFifo.circuit (w := 4) dest fifo 1

def shiftSwitch := switchWith (Stream.BackendAPI.shift 5 3 (by decide))
def circularSwitch := switchWith (Stream.CircularFifo3.backend 5)
```

The existing round-robin arbiter, output holding registers and cursor update
logic use the FIFO's offered word and valid bit. The router reads those pins
with the probe inputs tied low, so computing a grant cannot depend on the
dequeue decision it is about to make. The real FIFO samples the resulting
dequeue decision together with the live reset and input offer. Its ready pin
determines admission, including full-queue replacement on a dequeue edge.

[WithFifo.interchangeable](../../Pinwheel/Hardware/Switch/Backend.lean) gives
equality of every pre-edge and post-edge output for every finite input history
following a synchronous reset, starting each implementation from arbitrary
register bits. It works for any two backends with the same depth and packed
width. Each refines the existing switch model, so routing, output stalls and
arbitration use the same specification for both layouts.

For the 2×2 instance, the readback campaign independently checks each emitted
SystemVerilog implementation against its typed Lean circuit. Each certificate
covers arbitrary input and register bits and composes with reset recovery to
prove the initialized trace theorem. The pinned Yosys import and the restricted
JSON interpretation are the external trust boundary. Both audits reported
only standard Lean axioms.

The same `TypedModule` API and validation runner serve the switch and
standalone lane examples. The switch replays traffic from the independent
packet-switch oracle against both emitted designs. On the shift version, the
runner also interchanges the two 4-bit payload drivers and checks that the
modified RTL fails both replay and kernel correspondence.

The runner compares the two layouts under the same CIRCT lowering and Yosys
generic synthesis. These counts describe this 2×2 switch with depth three and
four-bit payloads, using the arbitration circuit from the flat switch.

| Input FIFO | RTL next-register equations | RTL output equations | Generic flip-flops | Total generic cells |
| --- | ---: | ---: | ---: | ---: |
| Shift | 20 | 6 | 50 | 208 |
| Circular | 20 | 6 | 56 | 255 |

Run the matched comparison with a fresh tag. The report under
`build/switch-fifo-backends/<tag>/report.json` records the commands, endpoint
coverage, cell breakdown, source and tool hashes, and hashes of the generated
proofs and artifacts.

```sh
python3 scripts/check-switch-fifo-backends.py --tag switch-fifo-pair-01
```
