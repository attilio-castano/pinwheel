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
python3 scripts/check-switch-baseline.py --tag switch-baseline-local
python3 scripts/check-switch-hierarchy.py --tag switch-hierarchy-local
python3 scripts/check-switch-artifact.py --tag switch-artifact-local \
  --config 1,1,1,1 --config 2,3,2,8 --config 3,1,1,8 --config 3,5,3,17 --config 5,3,2,8
python3 scripts/check-switch-hierarchy-artifact.py --tag switch-hierarchy-artifact-local \
  --config 1,1,1,1 --config 2,3,2,8 --config 3,1,1,8 --config 3,5,3,17 --config 5,3,2,8
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
into the switch is complete (`e244b65`), with the full 2,682-edge RTL campaign
and all mutation controls rerun successfully. The 5×3 switch decreased from
1,488 to 1,208 generic cells.

The independent whole-switch baseline uses occupancy-counted FIFOs, binary
cursors, a two-pass priority scan and a selected one-hot payload mux. It shares
only dimensions and external role mappings with the Lean implementation. Both
implementations passed the independent traffic oracle before and after synthesis
under matching Yosys settings:

| Inputs × outputs / depth / width | Lean cells | Baseline cells | Lean / baseline logic depth |
| --- | ---: | ---: | ---: |
| 1×1 / 1 / 1 | 25 | 24 | 6 / 6 |
| 2×3 / 2 / 8 | 360 | 306 | 13 / 12 |
| 3×1 / 1 / 8 | 193 | 164 | 10 / 12 |
| 3×5 / 3 / 17 | 1,394 | 1,350 | 17 / 17 |
| 5×3 / 2 / 8 | 1,208 | 810 | 18 / 20 |

Evidence is retained in
`build/switch-baseline/conventional-full-20261116/report.json`. Logic depth is
the longest generic combinational path with unit cost per cell; it is not a
timing estimate. The 5×3 case has 49.1% more generic cells with the same 152
register bits. The independent baseline has simulation evidence, not a Lean
refinement theorem.

`Switch.SharedSelectionCandidate` reuses the register layout and FIFO grant
wiring while sharing the winner decoder across output payload and cursor
selection. Its parameterized implementation and arbitrary-state reset proofs
are complete. The matched three-implementation campaign at
`build/switch-shared-selection/candidate-20261116/report.json` passed all 2,682
edges per implementation/form and 26 actual RTL mutation controls. Generic
cell counts become 25/354/192/1,382/834 in the table's order. The largest gap
shrinks from 398 to 24 cells. Its imported RTL proof campaign now passes the
full matrix. This implementation remains an explicit alternative because the
technology mapping results below show different area/delay tradeoffs.

### Technology mapping comparison

The same checked original/shared/baseline RTL was mapped independently at the
checksum-pinned IHP CMOS5L typical and slow corners, using matching ABC drive,
10 fF output load and 10,000 ps target settings. All 30 mapped circuits replayed
successfully (16,092 total edges). Functional cell models came from those same
Liberty files; unsupported cells are rejected if the mapping uses them. ABC's
actual merged SCL inputs are generated in a fresh private cache retained and
hashed with the run. Receipt:
`build/switch-technology/mapped-matrix-02/report.json`.

| Configuration | Original/shared/baseline area sum, typical | Original/shared/baseline ABC delay, typical (ps) |
| --- | ---: | ---: |
| 1×1 / 1 / 1 | 430 / 430 / 432 | 630 / 630 / 638 |
| 2×3 / 2 / 8 | 7,291 / 7,175 / 6,720 | 1,579 / 1,596 / 1,792 |
| 3×1 / 1 / 8 | 3,573 / 3,537 / 3,518 | 1,091 / 1,273 / 1,305 |
| 3×5 / 3 / 17 | 28,579 / 28,260 / 26,645 | 2,023 / 1,863 / 2,058 |
| 5×3 / 2 / 8 | 17,395 / 15,296 / 14,924 | 1,981 / 1,704 / 2,036 |

Area sums use the Liberty library's area units; the pinned files do not declare
a physical area unit. ABC's estimate includes combinational mapping and sizing,
but not setup/clock-to-Q, clock trees, placement, routing or parasitics. It is
not an achievable clock-frequency or full-STA result. Both corners preserve
the material tradeoff: shared selection improves the 5×3 case, but increases
the 3×1 delay estimate by 15–17% for about 1% area savings. Keep both architectures
available instead of assuming a universal improvement from the generic counts.

```sh
python3 scripts/install-technology-library.py
python3 scripts/check-switch-shared-selection.py --tag shared-switch-local
python3 scripts/check-switch-technology.py --tag switch-technology-local \
  --positive-report build/switch-shared-selection/shared-switch-local/report.json
```

`Switch.Export` emits reusable FIFO and output-slot leaf modules plus a control
module. A complete typed state map binds each hierarchical register to the flat
circuit. `TypedHierarchy` derives the wrapper and state map from width-indexed
instance connections and register bindings. The decomposition adds no registers
or latency. To check the 2×2 switch and reject a swap of the two five-bit FIFO
payload connections, run:

```sh
python3 -B scripts/check-switch-hierarchy-artifact.py --tag typed-switch-local \
  --config 2,2,3,4 --miswire
```

The retained
`build/switch-hierarchy/agent-masked-hierarchy-1/report.json` checks every output
and next register on 2,048 exhaustive 1×1 and 512 sampled 2×3 arbitrary input/state
cases, including malformed cursors. This comparison is separate from the
imported-RTL proof campaign. All three complete artifact matrices now pass:

| RTL architecture | Receipt under `build/` | Local equalities | Typed register/output endpoints |
| --- | --- | ---: | ---: |
| Original flat | `switch-artifact/private-imports-full-01/report.json` | 1,698 | 160 |
| Original hierarchy | `switch-hierarchy-artifact/private-imports-full-01/report.json` | 1,711 | 160 |
| Shared selection | `switch-shared-artifact/private-imports-01/report.json` | 1,930 | 160 |

Each covers the same five configurations, arbitrary binary inputs/registers,
and the composed reset-initialized protocol trace theorem. The flat negative
receipt `build/switch-artifact-negatives/private-imports-01/report.json` rejects
two semantic RTL corruptions and two coordinated metadata faults. The shared
receipt `build/switch-shared-artifact-negatives/private-imports-01/report.json`
rejects active-output payload inversion and FIFO data-update corruption. Both
shared controls fail local semantic equalities and include kernel-checked
concrete witnesses with an active or retained packet. Parser errors and proof
timeouts do not count as successful negative controls.

The proof generator groups independent local equalities into bounded compilation
units. For small Boolean obligations hidden behind wide comparisons, it proves
a stronger lemma by `decide +kernel`, then instantiates the exact original
statement. Wide mux trees use finite payload labels; OR networks use sets of
payload labels. Lean checks both the label equality and the interpretation
that recovers the exact original wide expression. These strategies close the
previous 5×3 payload timeouts without restricting cursor states. Solver results
only guide proof search. No proof step admits native decision axioms. All
generated declarations are audited, and receipts bind the generator helpers.
Generated modules and mismatch witnesses set their private import path after
Lake initializes its environment, so cached modules cannot take precedence.
An isolated Lean regression exercises a real same-name cache collision and
checks that both production compilation paths use the private definition:
`python3 test/test_typed_artifact_runner.py`. Inspection found no current
shadowing in the older retained matrices; their historical ambient cache state
was not separately archived. The receipts above rerun the full matrices with
the corrected search order.

```sh
python3 scripts/check-switch-shared-artifact.py --tag shared-artifact-local
python3 scripts/check-switch-shared-artifact-negatives.py --tag shared-negatives-local \
  --positive-report build/switch-shared-artifact/shared-artifact-local/report.json
```

`Stream.BufferedMerge` is the second integration user under construction. Its
model directly composes the round-robin arbiter with one elastic output slot;
it has no input FIFOs or destination fields. A `Multiport.Contract` proves
per-source conservation/order, with capacity, stall stability, unique acceptance,
cursor update/hold rules and bounded fairness in eligible refill opportunities.
The independent integer/occurrence-ledger oracle passes 2,664 exhaustive edges,
10,000 protocol-respecting stress edges and 103 fairness cases, including equal
payloads from different sources. Its 123 declarations pass the standard-axiom
audit. Run `lake env lean -DwarningAsError=true --run test/BufferedMergeModel.lean`.
Hardware and RTL evidence for this second user remain open.

The packet-switch campaign remains active. The flat, hierarchical and shared
artifact matrices are complete. Physical timing baselines and completion of the
second integration user remain campaign gates. Yosys and the restricted JSON adapter remain trusted
interpretation boundaries; kernel-checked equations do not certify these tools
or physical behavior.
