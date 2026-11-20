# Typed payloads and fork/join graphs

This extends the [serial stream milestone](lean-stream-hardware.md) with named
payload layouts and proved branching composition. Existing maps, elastic stages,
state encodings, simulation, flat emission and artifact proofs are reused.

```text
                        ┌─ increment → L elastic stages ─┐
input → atomic broadcast                                ordered join → output pair
                        └─ complement → R elastic stages┘
```

The example's first register performs each operation; `L` and `R` count all
register stages on the respective branch. They may differ. Each accepted `x`
produces `(x + 1, ~x)` in acceptance order, with modular W-bit arithmetic. The
incremented field occupies the high W bits of `out_data`; the complemented field
occupies the low W bits. Input width is W and output width is 2W.

## Admission and joining

The fork uses **atomic admission**: both branches accept an input on the same
edge, or neither accepts it. Each branch's input valid is gated by the other
branch's readiness. Branch readiness is independent of input valid/data, which
the existing `Machine` interface and the structural probe construction enforce.
There is consequently no readiness/valid combinational loop.

After admission, the branches advance independently. The join exposes a pair
only when both branches offer a result. It consumes both results together when
the downstream consumer is ready. A fast branch can stall while a slower branch
continues advancing. A stalled valid output retains both fields. Reset suppresses
transfers and clears both branch histories and storage on the edge.

This policy is conservative: outstanding transaction capacity is bounded by the
smaller branch capacity. Unequal depths can reduce throughput even when the final
consumer stays ready. The milestone does not claim one transfer per edge for
every unequal-depth graph. Branch-local buffering can increase skew capacity.
A future fork with separate per-branch acknowledgements would need additional
state and a proof of which branches have already consumed each input.

## Typed payload bundles

`Bundle` describes bitvector fields and nested pairs. It derives total width,
typed field identities, packing/unpacking, simulator bindings, and expression
wiring. Its codec proves both round trips for arbitrary layouts and widths.
The left subtree occupies the more significant bits.

```lean
import Pinwheel.Hardware.Stream.Bundle
open Pinwheel.Hardware Pinwheel.Hardware.Stream

def packet : Bundle :=
  .pair (.bits "tag" 3)
    (.pair (.bits "left_value" 8) (.bits "right_value" 17))

def packetInterface := packet.interface (by decide +kernel)
```

The interface contains three named ports with widths 3, 8 and 17; the packed
payload is 28 bits. Names must be unique. Concrete layouts can discharge that
finite obligation with kernel evaluation. `Bundle.packExpr` and
`Bundle.unpackExpr` wire fields without string-based lookup.
`test/StreamBundle.lean` checks codec and circuit identities and runs named-port
emission. The graph example writes its derived output layout to `payload.json`;
its external handshake retains the standard packed `in_data`/`out_data` ports.

## Composition and proofs

`Design.parallel a b` takes two designs with the same input width and produces
the concatenation of their output widths. It can be nested with `Design.serial`:

```lean
import Pinwheel.Hardware.Stream.Diamond
open Pinwheel.Hardware Pinwheel.Hardware.Stream

def branches : Design 8 16 :=
  .parallel (.pipeline (increment 8) 0) (.pipeline (complement 8) 2)

def combined : Design 8 8 :=
  .serial branches (.pipeline (adder 8) 0)
```

This is a structured series/parallel graph API. Shared wires, arbitrary feedback,
arbitration, and multiple clock domains are outside this milestone.

The new invariant records that the two ordered pending lists have equal length.
They may occupy different physical stages. `Parallel.contract` derives equal
branch acceptance, simultaneous result consumption, and conservation of the
zipped pending list from the two component contracts. Pairing is therefore by
transaction position, even if input or output values repeat.

`Certified.parallel` proves the structural circuit implements that model and
inherits cold reset from the components. It also inherits complete trace and
transaction proofs through the existing certificate interface.
`bounded_parallel` derives the minimum capacity bound; `stable_parallel` derives
stall stability from the branch properties. `diamond_transactions` states the
explicit `(x + 1, ~x)` accounting theorem for every width, branch depth and finite
input history, including backpressure and reset epochs.

`test/StreamGraph.lean` instantiates the properties with **arbitrary maps and
branch depths**. Replacing a map requires its local combinational correctness
proof, while transport and composition proofs stay unchanged. General progress
for arbitrary custom branches is not inferred from their safety contracts.
The example checks draining and empty/no-stall latency in simulation; the earlier
serial timing theorems are not presented as a new universal graph timing theorem.

## Structural export and checking

Flat export uses the proved `Parallel.circuit`. Hierarchical export emits two
child modules and explicit broadcast/join wiring, reusing the raw ready/offer
taps introduced for serial composition. The existing restricted RTL importer and
Lean equality reconstruction now accept an explicit design expression and derive
input/output widths from the interface descriptor.

Each artifact is checked at every next-state field and output field, then lifted
to transaction accounting and arbitrary-input traces after reset. Lean's kernel
checks these equalities; Z3 only proposes proof cuts. The boundary remains
two-state synchronous RTL with trusted Yosys frontend and JSON interpretation.
No synthesis-to-gates or physical qualification result is claimed.

## Reproduce

With the existing pinned Lean and CAD tools installed:

```sh
python3 scripts/check-stream-graph.py --tag graph-check
```

The default matrix is `W ∈ {1,8,17}`, `L ∈ {1,2,4}`, `R ∈ {1,3,4}`: 27
configurations and 54 flat/hierarchical artifact certificates. A smaller run is:

```sh
python3 scripts/check-stream-graph.py --tag graph-smoke --config 8,1,3 --config 8,4,1
```

The runner checks all physical register values against the encoded model and
compares pre/post-edge RTL observations with Lean. An independent Python
scoreboard checks arithmetic, pairing, ordering, loss, duplication, reset,
stall stability, draining, and the initial no-stall latency. Hierarchical traces
record each branch's readiness and offer separately; unequal-depth cases must
exercise one-sided blocking and unpaired offers. Traffic includes sustained
backpressure, bubbles, arithmetic wraparound, random traffic and reset during load.

Three deliberately incorrect hierarchical artifacts must fail the Lean proof
checks: removal of one branch's admission gate, premature consumption of a lone
left result, and swapping the joined fields. Portable tests exercise the
independent scoreboard's rejection paths and branch coverage counters.

Results, generated proofs, logs and source/tool/artifact hashes are retained
under `build/stream-graph/<tag>/report.json`. Tags must be fresh. The source-only
checks are:

```sh
lake build stream_graph stream_example
lake env lean --run test/StreamBundle.lean
lake env lean test/StreamForkJoin.lean
lake env lean --run test/StreamGraph.lean
lake env lean test/StreamAudit.lean
python3 -B -m unittest discover -s test -p test_stream_graph.py -v
```

The serial and branching executables share `Stream.Replay`, including state
materialization, cycle comparisons and transaction accounting.
