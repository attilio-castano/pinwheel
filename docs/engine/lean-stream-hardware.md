# Reusable Lean stream hardware: first milestone

This milestone adds a parameterized synchronous hardware library alongside
Pinwheel's protocol engine. The running example accepts packed pairs of W-bit
words, buffers them in a D-entry register FIFO, and passes their modular sum
through L elastic stages. The implementation is a typed circuit and a reusable
transaction contract, with a proof connecting the two.

Supported exported configurations have `W > 0`, `D > 0`, and `L > 0`. The Lean
builder takes `extra = L - 1`; its first stage applies the arithmetic operation
and its remaining stages apply identity. FIFO depth is independent of latency.

```text
ready/valid packed pair → FIFO(D) → mapped register → L−1 elastic registers → ready/valid result
```

## Interface and cycle semantics

| Pin | Width | Meaning |
| --- | ---: | --- |
| `clk` | 1 | Rising-edge clock |
| `reset` | 1 | Active-high synchronous reset |
| `in_valid`, `in_ready` | 1 each | Input offer and acceptance |
| `in_data` | 2W | Low W bits: a; high W bits: b |
| `out_valid`, `out_ready` | 1 each | Output offer and acceptance |
| `out_data` | W | `(a + b) mod 2^W` |

Transfers use the values immediately **before** the rising edge. Reset suppresses
both transfers, clears storage on that edge, and begins a new transaction-accounting
epoch. It deliberately discards pending work. From arbitrary digital register
bits, one reset edge establishes the implementation relation.

The FIFO has no combinational data bypass. Full dequeue/enqueue replacement is
supported on one edge. A stalled valid output retains both its valid bit and
payload until accepted, unless reset occurs. Invalid input payload bits may have
any value; the exported root normalizes them to zero before internal composition.

From empty state with continuously ready output, an input accepted at edge `t`
is emitted at edge `t + L + 1`. Bubbles shift in the same way. The design accepts
one input per edge in this regime. With arbitrary backpressure, safety is
unconditional; progress needs a readiness assumption. When input stops and
output stays ready, any reachable state drains within `D + L` edges.

## Reuse and new infrastructure

| Existing Pinwheel infrastructure | Use in this milestone |
| --- | --- |
| `Hardware/Circuit.lean`, `Expr.bind` | Width-indexed expressions, circuit evaluation, substitution for wiring |
| `Hardware/Interface.lean` | Complete typed port/register enumeration, labels, simulation comparisons |
| `Hardware/Timed.lean` | Same-edge refinement and finite pre/post-edge trace equality |
| `Hardware/Emit.lean` and netlist tools | Deterministic MLIR emission, lowered through CIRCT |
| `scripts/backend_readback.py` | Restricted Yosys JSON interpretation, cut suggestions, Lean equality reconstruction |
| `scripts/install-hardware-tools.py` | Existing checksum-pinned CIRCT, Yosys, Icarus and Z3 installation |

The new modules live in `Pinwheel/Hardware/Stream/`:

| Layer | Main files | Responsibility |
| --- | --- | --- |
| Logical contracts | `Contract`, `Machine`, `Queue`, `Pipeline` | Ordered pending lists, reset epochs, FIFO/stage behavior, serial composition |
| Typed interfaces | `Ports`, `Encoding`, `Registers` | One declarative port schema, logical encodings, parameterized register banks |
| Structural implementations | `FifoCircuit`, `ElasticCircuit`, `Compose` | FIFO and mapped-stage circuits, acyclic ready wiring |
| Reusable certificates | `Certified`, `CompositionProof`, `Design` | Encodings and local proofs packaged with circuits; typed hierarchy tree |
| Trace properties | `Artifact`, `Normalize`, `Properties`, `Timing` | Whole-state correspondence, arbitrary raw inputs, capacity, stability, latency and drain |
| Export | `Export` | Flat MLIR, hierarchical wrappers/leaf MLIR, machine-readable interface and state mapping |

The hierarchy's ready path goes backward; registered data goes forward.
`Machine` restricts offers to stored state and ready to downstream-ready plus
state. The serial builder therefore cannot introduce a combinational loop.
The hierarchical exporter exposes internal raw ready/offer taps so the wiring
implements the same probe construction used by the proved flat circuit.

## Replacing the arithmetic

`Map wi wo` contains a combinational expression, a function on bitvectors, and a
proof that evaluating the expression yields that function. `Design.buffered`
takes any such map. The transport proofs do not inspect its implementation.
For example:

```lean
import Pinwheel.Hardware.Stream.Timing
open Pinwheel.Hardware Pinwheel.Hardware.Stream

def complement (w : Nat) : Map w w where
  expression := .inv (.input .data)
  function := fun x => ~~~x
  correct := fun _ => rfl

def exampleDesign := Design.buffered (complement 17) 3 (by decide) 3
```

This builds a 17-bit complement stream with depth 3 and four elastic stages.
`test/StreamLaws.lean` checks this replacement at arbitrary widths, depths and
stage counts, reusing the capacity, stability, latency and drain theorems.
Custom stateful components implement `Certified`; they can then use the same
serial composition theorem. They need their own timing/progress contracts if
those guarantees are desired.

## Proofs and their boundary

The key conservation statement within each reset epoch is:

```text
map function acceptedInputs = emittedOutputs ++ pendingResults
```

`Contract.serial` proves this for a composition from the two local contracts.
`Certified.serial` proves that the structural wiring implements that composed
machine. `Certified.simulator_transactions` lifts accounting to the structural
simulator. `Delay.noStall_trace` compares the complete no-stall trace with a
literal shift-register model. `design_drains` proves the conditional drain bound.

For each exported RTL form, the check runner reimports the actual RTL and
generates proofs of **every next-state field and every output field**, for all
digital input and register values. These are assembled into whole-step and
whole-observation equality. The resulting artifact theorems include:

- `rtl_transactions`: the imported RTL obeys the transaction-accounting theorem.
- `rtl_initialized_trace`: after a cold-reset edge, its entire trace agrees with
  the model for arbitrary raw pin histories, including invalid payload bits.

Z3 and randomized signatures only propose equality cuts. Lean reconstructs and
checks each equality; a solver answer does not discharge a theorem. The audit
rejects axioms other than `propext`, `Classical.choice`, and `Quot.sound`, including
`sorryAx` and native-decision shortcuts.

The trust boundary includes Lean's kernel and the interpretation of emitted RTL
through Yosys and the restricted Python JSON adapter. The emitter and CIRCT are
not assumed to preserve semantics: the resulting artifact is checked. The JSON
adapter and Yosys frontend themselves have not been formally verified. This is
two-state synchronous digital reasoning, not a four-state HDL, analog timing,
metastability, synthesis-to-gates, or physical qualification result.

## Reproduce from source

Use the repository's pinned Lean toolchain. Install the existing pinned CAD tools
once, then run a fresh validation directory:

```sh
python3 scripts/install-hardware-tools.py
python3 scripts/check-stream-hardware.py --tag stream-milestone
```

The default matrix is `W ∈ {1,8,17}`, `D ∈ {1,3,8}`, `L ∈ {1,2,4}`. Each of the 27
configurations emits both flat and hierarchical RTL, replays directed and seeded
random traffic against Lean, checks an independent transaction scoreboard, and
kernel-checks both artifact certificates. Traffic includes reset during load,
bubbles, sustained stalls, full replacement, wraparound arithmetic and drain.
Three additional RTL mutations—incorrect output, ready, and state update—must
be rejected by the generated Lean proof checks. Portable tests also reject
changed clocks, malformed widths, missing or aliased state, unknown bits and
combinational cycles.

For a smaller run, use a fresh tag:

```sh
python3 scripts/check-stream-hardware.py --tag stream-smoke --config 8,3,2
```

For proof/API work without CAD:

```sh
lake build stream_example
lake env lean test/StreamAudit.lean
lake env lean test/StreamLaws.lean
python3 -B -m unittest discover -s test -p test_generic_stream.py -v
```

Results go under `build/stream-hardware/<tag>/`: emitted sources, stimuli,
pre/post-edge CSV traces, imported graphs, generated Lean proofs, audit logs and
`report.json`. The report records commands, durations, artifact hashes and
source/tool hashes, and rejects source changes during the run. Output directories
are never reused. A simulation mismatch triggers a VCD replay. Generated build
artifacts are local evidence and are not checked into source control.

## Scope of this first milestone

This is a reusable ready/valid hardware foundation, not yet a general Hardcaml
replacement. It supplies typed parameterization, serial hierarchy, shared
simulation/emission, and compositional proofs. The register FIFO uses a unary
valid prefix and shifting data; it is chosen for a small, proved implementation,
not an area or frequency claim. Large FIFOs need a separate RAM-backed refinement.

Further milestones can add richer interface combinators, fanout/arbitration,
RAM semantics and inference, graph optimization, multiple clock domains, and
more convenient elaboration syntax. Those additions must retain explicit
semantics and refinement boundaries. Existing protocol and physical-design
qualification evidence remains scoped to its original artifacts.
