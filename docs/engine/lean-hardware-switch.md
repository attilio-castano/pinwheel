# Buffered packet switch and reusable hardware interfaces

The switch composes the existing FIFO and elastic-register circuits with a
parameterized round-robin selector. Its logical state retains source provenance
for transaction proofs; its physical state stores destination/payload words,
output payloads, valid bits and one-hot cursors. There is no source tag in RTL.

## Semantics

Each input has a FIFO of positive depth. Each output has one holding register.
Only pre-edge FIFO heads request an output; a newly accepted packet cannot bypass
the FIFO. A full FIFO can dequeue and enqueue on the same edge. An output slot
can refill when empty or when downstream is ready. Its cursor advances only on
an actual input-to-slot transfer. Stalled outputs retain their entire packet.

The logical destination is `Fin outputs`. Physical destinations use a positive
binary width with a proof that all destinations fit. An asserted unused encoding
is refused: it neither enters the FIFO nor sees input ready. With valid low,
unused destination bits do not suppress ordinary input readiness. Reset masks
transfers, clears queues and slots, and selects input zero as each cursor.

The transaction theorem conserves the ordered accepted/emitted/pending history
of each source/destination flow within a reset epoch. Reset discards that epoch's
pending work. Different destinations can overtake one another, and different
sources can interleave. Head-of-line blocking is explicit. A persistent eligible
head is served within `inputs` output-refill opportunities; this is not an
unconditional cycle bound under downstream stalls.

## Reuse and new abstractions

| API | Purpose |
| --- | --- |
| `Interface`, `Expr.bind`, `Circuit` | Existing complete typed descriptors and structural substitution |
| `Stream.Fifo.circuit`, `Stream.Elastic.circuit` | Existing storage circuits and local refinement proofs |
| `Stream.mapInput`, `queue_map_*` | Reuse queue semantics across transaction encodings |
| `Bank.interface`, `Bank.circuit` | Replicate typed ports, registers or independent circuits with complete enumeration |
| `Implementation` | Relate any typed physical circuit to its specification; no single-channel restriction |
| `Implementation.Reset` | Separate recovery from arbitrary physical bits from initialized simulation |
| `Stream.Multiport.Contract` | Ordered accounting for independently handshaken input/output flows |
| `Arbitration.RoundRobin` | Selection, priority and conditional bounded service proofs |
| `Switch.Physical` | Raw pin codec, valid destination admission and complete interfaces |
| `Switch.PacketEncoding` | Pack destination/payload and reuse the existing FIFO representation |
| `Switch.Structural.implementation` | Parameterized whole-switch state and output refinement |
| `Artifact.Correspondence` | Transfer structural proofs to a checked imported RTL interpretation |

`Switch.Structural.step_eq` and `output_eq` quantify over arbitrary raw physical
inputs and every typed register/output, assuming the logical state invariant.
`reset_eq` has no valid-state assumption: it initializes arbitrary physical bits.
`initialized_trace` composes these obligations for every subsequent input trace.

## Validation commands

Use the repository's pinned Lean version. The CAD installer downloads the
checksum-pinned tools recorded in `tools/hardware-toolchain.json`:

```sh
python3 scripts/install-hardware-tools.py
lake build Pinwheel.Hardware.Switch.Certified
lake env lean test/SwitchContracts.lean
lake env lean --run test/SwitchInterface.lean
lake env lean --run test/SwitchPacketEncoding.lean
lake env lean --run test/SwitchCircuit.lean
python3 scripts/check-switch-model.py --tag switch-model-local
python3 scripts/check-switch-circuit.py --tag switch-circuit-local
python3 scripts/check-round-robin-circuit.py --tag selector-local
python3 scripts/check-round-robin-baseline.py --tag selector-baseline-local
python3 scripts/check-round-robin-masked.py --tag selector-masked-local
```

Tags create new directories and must not be reused. Reports record commands,
source hashes, artifacts and the scope of the check. Model replay is separate
from circuit simulation and from checking an actual RTL artifact.

Export an independently parameterized circuit:

```sh
lake env lean --run test/SwitchCircuitEmit.lean 3 5 3 17 build/my-switch
```

The result contains `switch.mlir` and `interface.json`. The descriptor enumerates
all ports and registers, their widths, role mappings, and reset values. Emission
does not insert a power-on initialization assumption; hardware must receive a
reset edge. The exporter requires positive dimensions and payload width, while
the structural proofs also cover zero-width logical payloads.

Replay raw pins, optionally starting from arbitrary register values:

```sh
lake env lean --run test/SwitchCircuitReplay.lean 3 5 3 17 stimulus.jsonl trace.jsonl startup.json
```

Each stimulus row has `reset`, input arrays `valid`, `destination`, `payload`,
and output array `ready`. `startup.json` is an array of register values in
descriptor order; when supplied, the first edge must assert reset. Replay checks
both observations around each edge and every post-edge register, including
unused data cells. The trace also retains model provenance for independent
occurrence accounting with repeated payload values.

## Evidence and remaining gates

Completed checks on 2026-11-16:

- Model campaign: 12,478 edges across 11 configurations, checked against an
  independent deque/rotating-list model and occurrence scoreboard.
- Packet codec/FIFO reuse: 224 raw codec cases and 5,184 state/output transitions.
- Whole structural circuit: 1,920 raw-input cycles across eight configurations
  and 32 resets from malformed physical state. The proof audit covers all
  imported switch declarations and rejects nonstandard axioms.
- Whole-switch RTL: 2,682 edges in both emitted and synthesized RTL, across
  1×1, 2×3, 3×1, 3×5 and 5×3 configurations. Every physical observation and every
  unsynthesized post-edge register matched the independent oracle. Thirteen
  actual RTL mutations and six trace corruptions were rejected.
- First selector: 2,242 legal request/cursor combinations at sizes 1, 2, 3, 5,
  and 8, both before and after generic synthesis; the Lean structural check
  additionally covers size 4, totaling 2,306 cases.

The independently written two-pass selector baseline exposes a resource gap:

| Requesters | First selector generic cells | Two-pass baseline generic cells |
| ---: | ---: | ---: |
| 1 | 1 | 0 |
| 2 | 8 | 5 |
| 3 | 21 | 18 |
| 5 | 53 | 35 |
| 8 | 133 | 59 |

Both were freshly synthesized under identical generic Yosys settings and checked
by exhaustive simulation and SAT equivalence on legal one-hot cursors. Invalid
cursor behavior may differ. These are generic cell counts, not physical area or
timing.

The smaller proved selector in `Arbitration.RoundRobinMasked` closes this gap.
It supports arbitrary typed value/fallback expressions as well as one-hot
grants. The fresh matched comparison records 0/5/18/34/58 generic cells for
sizes 1/2/3/5/8, versus 0/5/18/35/59 in the handwritten baseline. At size 8 this
reduces the initial implementation's generic cell count by 56.4%. Integration
into the switch is a separate change followed by fresh RTL validation.

The packet-switch campaign remains active. Complete artifact certificates over
a representative parameter matrix, hierarchical RTL,
matched whole-switch synthesis/timing baselines and a second integration user
remain campaign gates. Yosys and the restricted JSON adapter remain trusted
interpretation boundaries; kernel-checked equations do not certify these tools
or physical behavior.
