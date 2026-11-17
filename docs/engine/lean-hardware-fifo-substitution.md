# Choosing the FIFO in an increment lane

A caller should be able to change a lane’s FIFO by supplying a different
implementation at construction. The caller’s ordering proof should mention
accepted words, emitted words, and reset. Storage layout belongs in the FIFO
author’s proof. The [checked Lean sketch](../../examples/FifoSubstitutionSketch.lean)
uses the public library import and the existing shift FIFO.

## The client

[IndependentLanes](../../examples/IndependentLanes.lean) currently chooses its FIFO
inside `Stream.Design.buffered`. The proposed call moves that choice to the caller.
Here both forms describe a 17-bit lane with a depth-three FIFO and one extra
pipeline stage.

```lean
-- Existing client
(Stream.Design.buffered (Stream.increment 17) 3 (by decide) 1).flatten

-- Sketch client
FifoSubstitutionSketch.lane (FifoSubstitutionSketch.shift 17 3 (by decide)) 1
```

The second call builds the actual wired circuit. The proposed finished API would
also return its composition proof. A circular FIFO author would supply another
value of the same type, `Fifo 17 3`. Bank replication can follow once the
single-lane proof works.

## What the caller can observe

For every finite prefix since this lane’s last reset, including prefixes ending
in a stall, the client law is

```text
map (add one modulo 2^width) accepted = emitted ++ still pending in delivery order
```

Both histories count actual pre-edge handshakes. Reset discards the old pending
suffix. Downstream readiness is needed to conclude that the suffix eventually
drains. The sketch spells out this proposition as `LaneLaw` on the circuit
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

## Who proves what

| Owner | Obligation | Status in the sketch |
| --- | --- | --- |
| FIFO author | Relate every step and output on raw pins to the queue model. After a reset edge from arbitrary bits, establish the relation to the empty list. | Checked for the existing shift FIFO. A circular FIFO can choose a relation based on a state projection. |
| Library | Derive equal pre/post pin traces after reset for any two such FIFOs. Transport the model’s transaction law to histories collected on circuit pins. | Both theorems checked. The trace comparison starts after the reset edge. |
| Serial builder | Establish the product relation and reset recovery for the FIFO wired to the mapped pipeline. Use the existing acyclic offer/ready wiring and serial stream contract. | Circuit construction and the client law’s type check. The composed proof is the next implementation task. |
| Client | Choose a FIFO, width, depth and stage count, then apply the resulting lane theorem. | Shift-backed construction is checked. The two-backend demonstration awaits the circular FIFO and serial builder proof. |

The common interface uses the library’s existing `Timed.Refinement`. This lets
the shift FIFO reuse its canonical encoding proof and lets the circular FIFO
use `DecodedImplementation.refinement` with its own validity invariant. Only
the backend needs to know how pointers and occupied slots represent a list.

Recheck the sketch with the pinned Lean toolchain:

```sh
lake build Pinwheel.Hardware.Library
lake env lean -DwarningAsError=true examples/FifoSubstitutionSketch.lean
```

The next design review should inspect one concrete result: the *same* client
theorem applied to both implementations at a non-power-of-two depth. After
that, exercise the banked client, certify emitted instances, compare synthesis
under matching settings, and try the substitution in a packet-switch input.
