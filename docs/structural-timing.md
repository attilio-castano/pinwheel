# Structural timing

This record owns a Lean-level structural model of combinational reach and depth,
its theorems, the executable report, and its comparison with evidence that earlier
studies obtained from emitted MLIR, technology mapping and place-and-route.
It starts no CAD tool. [Research status](research/status.md) owns allocation.

## Question

Six routed runs and several mapped screens kept rediscovering facts that are
properties of the netlist's structure: which launch points reach which
registers, how deep those cones are, which registers recirculate. Can those
facts be stated and computed in Lean, in seconds, and do they agree with what the
expensive experiments measured?

## Definitions and theorems

`Hardware/Structure.lean` is generic over every `Expr` and `Netlist`.

- `Cost` charges abstract **levels** per operation. `Cost.unit` charges one level
  per emitted operation; `Cost.gates` is a rough two-input-gate estimate (wiring
  free, multiplexer two, reductions and carries logarithmic in width).
- `Expr.arrival pick cost input register` is the arrival level at an expression's
  output, given which leaves launch a transition (`none` = not a launch point)
  and how two arrivals combine: `max` for the latest arrival, `min` for the
  earliest. `Netlist.arrivalNext` / `arrivalOutput` thread it through shared
  wires; `withArrivals` evaluates every wire once and is proved equal to them.
- **Composition law** (`Expr.arrival_bind`): substituting expressions for leaves
  adds the arrival of what is substituted. No path is created or lost.
- **Unreachable implies independent** (`Expr.eval_congr_of_arrival_none`,
  `Netlist.step_congr_of_arrival_none`, `observe_congr_of_arrival_none`): if no
  launch point is visible from an endpoint, its value is the same whatever the
  launch points carry. A syntactic check yields semantic non-interference.
- **Wrapper law** (`Netlist.arrivalNext_extend`, `arrivalOutput_extend`,
  `arrivalNext_extend_extra`): behind `Netlist.extend`, an inner register's
  arrival is the inner netlist's, with every inner input arriving when the
  expression wired into it does.
- **Pin isolation** (`PinSampler.no_path_from_pins`, `no_output_path_from_pins`,
  `pins_reach_first_stage`): for every inner netlist and every cost model, the pin
  port reaches the first pipeline stage through no logic and reaches no inner
  register or output at all. This is the structural reason the
  [pin sampler](pin-sampler-study.md) removed the `incoming` launch family.

All are kernel-checked with standard axioms. `test/StructuralTiming.lean` runs
hand-computed levels through a shared wire, latest versus earliest on a
recirculating register, the gate estimate, pin isolation, and a bypass mutation
that must show a path.

## Executable report

`structure_report` (`test/Structure.lean`) evaluates the three proved composed
backends and their sampled wrappers: arrival per launch family
(`incoming`, `command`, `data`, `init`/`reset`, loader cursor, all registers) and
endpoint class, the cached-word enable cone, the stages of the successor loop, and
each register's shortest path back to its own data input. All of it takes about
16 seconds compiled. `scripts/check-structure.py --tag NAME` retains a receipt and
compares it with tracked manifests.

## Agreement with retained evidence

Receipt `build/structure/validation-02/report.json`.

**1. Exact: operation depth on the emitted graph.** The
[bank-selection](bank-selection-study.md) and [cache-enable](cache-enable-study.md)
studies measured, in Python on emitted MLIR, the depth from the loader cursor to
named stages. Lean's `Cost.unit` arrival reproduces all 13 recorded values:

| Depth from the loader cursor | Recorded from MLIR | Lean |
| --- | ---: | ---: |
| Command split: selection / index value / successor / next address | 5 / 14 / 26 / 46 | 5 / 14 / 26 / 46 |
| Late bank: successor / next address | 6 / 26 | 6 / 26 |
| Cache enable, control: complete / successor abstracted | 51 / 23 | 51 / 23 |
| Cache enable, candidate: complete / successor abstracted | 46 / unreachable | 46 / unreachable |
| Read address (both variants) | unreachable | unreachable |

**2. Ordinal: technology-mapped logic depth into the cached word.** Twelve points
(three variants, four launch families) against the mapped-cone reports:
Pearson r = **0.954**; all eight candidate changes move in the same direction;
loader data reaches the cached word in neither.

| Launch family | Mapped depth: control → late bank → enable split | Lean gate levels |
| --- | ---: | ---: |
| Loader cursor | 32 → 25 → 28 | 90 → 62 → 82 |
| `incoming` | 35 → 38 → 32 | 99 → 101 → 91 |
| `command` | 32 → 25 → 29 | 87 → 59 → 79 |
| `init`/`reset` | 32 → 25 → 28 | 87 → 59 → 79 |

The late-bank conclusion — large gains on the loader families, a small loss on the
protocol family, hence no slow-corner gain — is visible before mapping.

**3. Ordinal: extracted slack in the routed control.** Port families carry equal
external budgets, so deeper should mean less slack. Deepest Lean levels
(`incoming` 99, `command` 87, `init`/`reset` 87, `data` 41) rank exactly as
extracted worst slack does (−0.797, +0.019, +0.200, +3.380 ns). The deepest
register-launched endpoint is the cached word (101), the limiting endpoint of
every routed run. In the sampled wrapper the `incoming` family reaches only the
pin stages; extraction measured +14.35 ns for it.

**4. Recirculation and hold.** 6,172 of 6,233 register bits return to their own
data input through at most one multiplexer (every dictionary, index, idle/last
and cached-word bit; the 61 loader-control and core-state bits take four to six
levels). Post-CTS hold repair found 6,192–6,208 violating endpoints in the three
ungated calibrated runs. With width-8 clock gating the recirculating count falls
to 2,572; the flow still found 4,392, because gated dictionary flip-flops are then
fed from the `data` port through no logic at all. The count explains the
hold-cell area; it does not predict it exactly.

## What the levels show

Stages of the successor loop, gate levels from register outputs, command split:

| Stage | Arrival | Added |
| --- | ---: | ---: |
| Read address | 22 | 22 |
| Successor word (index and dictionary lookup, expansion) | 50 | 28 |
| Next address (decode the fetched word, choose entry, fault or halt) | 91 | **41** |
| Cached-word enable (next address differs from current) | 99 | 8 |
| Cached word | 101 | 2 |

- **The largest stage is after the lookup, not in it.** The storage read that
  the late-index, late-record and bank-selection candidates restructured is 28
  of 101 levels. Decoding the fetched word into the next address is 41.
- **The cached word's data arrives at 50; its enable at 99.** The register is
  limited entirely by when it learns *whether* to load. That is why gating it
  moved the design's critical endpoint onto a clock gate
  ([combined run](pin-sampler-study.md#combined-with-clock-gating)), and why the
  cache-enable variant (enable 91, in parallel with the next address) matters more
  under gating than its mapped screen suggested.
- **Late bank** cuts the successor word from 36 to 8 levels for `command` and
  from 39 to 11 for the cursor, and leaves the register and `incoming` families
  at 50–52: it optimizes families that were never limiting.
- Core state registers sit at 91, ten levels behind the cached word. An early
  cache enable would make them, and the 41-level decode, the next limit.
- The [decoupled prefetch machine](memory-abstraction.md#structural-levels)
  reorders this loop: the fetched words become registers, the branch selection
  moves after them, and the next addresses come from the dispatch decision. Its
  deepest register endpoint is 63 levels, the cached word 38. The
  [one-port backend](memory-abstraction.md#the-one-port-backend) keeps that
  shape with a single read: 65 levels, the port's address at 35. Levels did not
  see what decided between them — area: the three-port backend did not fit the
  floorplan, and the mapped screen, not the level model, is the area oracle.

## Boundary and use

Levels are ordinal. About a third of the routed critical path is buffering and
wire; equivalent RTLs differ by 0.6–2 ns after place-and-route; neither fanout
nor placement is modeled. The model ranks and explains; it does not sign off.
Suggested order for a structural question: Lean levels (seconds), then the mapped
screen (minutes), then one confirming routed run with a matched control and
`check-targeted-timing.py --design`.

The same experiments suggested three further abstractions, all now built:
register enables are [certified in Lean](register-enables.md), so that
recirculation, gating groups and enable cones are explicit and provable instead
of left to a synthesis width threshold; [input latency](input-latency.md) is a
parameter of the pin-level protocol contracts; and the
[memory abstraction](memory-abstraction.md) gives storage a contract with
interchangeable implementations and a machine proved against a latency. A
fanout-aware cost is the natural refinement of this model.

## Reproduction

```sh
lake build Pinwheel structure_report
lake env lean -DwarningAsError=true --run test/StructuralTiming.lean
python3 scripts/check-structure.py --tag NAME
```
