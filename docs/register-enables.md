# Register enables

This record owns register enables as certified structure in Lean, the gating
plans derived from them, and the flow step that applies a plan to unchanged RTL.
It starts no placement or routing. [Structural timing](structural-timing.md)
owns the level model it extends; [research status](research/status.md) owns
allocation.

## Question

Three findings pointed at the same missing notion. Hold repair costs about one
delay cell per flip-flop because 6,172 of 6,233 bits recirculate through a
multiplexer. Clock gating recovers 18.7% of cell area, but the pinned flow can
only choose gating groups by a width threshold; that gated the cached word, whose
enable closes the design's critical loop, and the
[combined run](pin-sampler-study.md#combined-with-clock-gating) lost 2 ns. And
the gated structure sat outside every proof. Can the enable of a register be a
first-class, certified object in Lean, so that which registers stop their clock
is decided and justified there?

## Construction

`Hardware/Enable.lean` is generic.

- `Update` splits a register's behaviour into `enable` and `data`. `Update.next`
  is its recirculating encoding, `mux enable data hold`.
- `Update.Describes r next` states that an emitted next-state expression means
  exactly "load `data` on edges where `enable` holds, otherwise keep `r`" — the
  contract an enable flip-flop or a clock gate implements. `describes_mux`
  certifies the plain shape; `describes_slice_mux` certifies a narrow physical
  register that stores a field of a wider logical value, given that the sliced
  hold branch is still the register.
- `Expr.updateShape` reads `(enable, data)` off those two shapes.
  `Circuit.Enables` packages views with their proofs, and `Enables.step` is the
  resulting statement about the circuit's own step function.

**Nothing is re-encoded.** `Hardware/Storage/EnabledBackend.lean` shows by
definitional unfolding (`rfl`) that every dictionary word, idle profile,
last-address register and the cached word of `BankSelect.body` and
`CacheEnable.body` already *is* `mux enable data (reg r)`, and every index entry
is `slice 0 5 (mux enable data (0 ++ reg r))`. The views are read off the proved
expressions, so emitted MLIR, RTL and every read-back proof are untouched
(the RTL used below is the read-back-proved command-split control,
SHA-256 `31893069…c6c6f764`). Loader-control and core-state registers are
deliberately not viewed: their top-level multiplexers select among behaviours
and do not hold the register.

`Enabled.Policy` names what a flow may gate, and two theorems bound it:
`gated_has_update` (a policy gates only registers with a certified update) and
`cached_word_never_gated`.

| Policy | Clock gates | Gated bits | Bits still recirculating |
| --- | ---: | ---: | ---: |
| `none` | 0 | 0 | 6,172 |
| `dictionary` (64 words, two last-address registers) | 66 | 3,536 | 2,636 |
| `storage` (also 512 index entries and two idle profiles) | 580 | 6,108 | 64 |

The standard-axiom audit covers all of it; `test/Enables.lean` executes the
slice-mux view against a reference, checks that both bodies yield views for
exactly the 581 storing registers, and pins the three plans.

## What the enable and data cones show

`structure_report` now evaluates each certified cone separately
(gate levels, latest arrival, command-split):

| Register class | Enable from registers | Enable from `data` port | Data from `data` port |
| --- | ---: | ---: | ---: |
| Dictionary words | 23 | 29 | 4 |
| Index entries, idle and last | 23 | 29 | 0 |
| Cached word | **99** (91 in the cache-enable variant) | unreachable | unreachable |

Cached-word data arrives from registers at level 50. Storage enables are early —
a quarter of the critical loop's depth — so a clock gate's earlier deadline costs
them nothing; this matches every routed gated run, where no storage gate was a
violating endpoint. The cached word is the opposite case, which is why the
policy excludes it. Their dependence on the `data` port comes from push
validation, which the command split deliberately retained.

## Applying a plan

`structure_report` writes `plan-<policy>.tsv` (register name and width).
`scripts/gate-clocks.py --rtl RTL --plan PLAN --testbench DIR --tag NAME` then:

1. lets Yosys infer every enable, folds the enables of **unplanned** registers
   back into multiplexers (`dffunmap -ce-only`), and converts the remainder to
   `sg13cmos5l_lgcp_1` gates; a selection argument to `clockgate` itself converts
   nothing in the pinned Yosys, hence the complement;
2. checks the netlist against the plan bit by bit: each planned register sits
   behind exactly one gate with no residual enable, and every other register is
   on the root clock;
3. runs the independent oracle on the gated netlist with **every storage register
   observed by name** (register names survive this generic netlist), using the
   vectors that fill and execute every dictionary word;
4. ties each gate's enable to 0 and to 1 and requires every mutant to be rejected;
5. maps both corners with the project's recipe for an area screen.

| Result on the proved command-split RTL | `none-02` | `dictionary-01` | `storage-01` |
| --- | ---: | ---: | ---: |
| Gates in netlist / in plan | 0 / 0 | 66 / 66 | 580 / 580 |
| Oracle regression | 29,062 edges, 18,079,584 storage observations | same | same |
| Stuck-enable mutants rejected | — | 132 / 132 | **1,160 / 1,160** |
| Typical mapped area (µm²) | 546,149 | 497,263 (−9.0%) | **457,577 (−16.2%)** |
| Mapped cells / `mux2` | 26,924 / 4,117 | 21,896 / 3,469 | 18,837 / 685 |
| Slow ABC delay (ns) | 9.964 | 9.974 | 9.970 |
| Elapsed | 23 s | 26 s | 91 s |

Receipts: `build/gated/<tag>/report.json`. Plans are identical in
`build/structure/validation-03/` (SHA-256 `254d768d…`, `c4cccf8b…`).
Mapped delay does not move, as expected: the critical loop's register is left
alone. Mapped area excludes clock trees and hold repair. In the routed ungated
runs timing-repair buffers were a further 19% of functional area, mostly one
hold cell per recirculating bit; under the `storage` plan 64 such bits remain.
That larger saving is a prediction from structure, not a measurement.

## Boundary

- The certified statement is about the enable abstraction: the emitted
  next-state equals "load when enabled, else hold". That an integrated clock
  gate implements that contract is trusted technology mapping, checked here by
  simulation and mutation, not proved. Equivalence across gating and technology
  mapping remains open.
- Gated dictionary flip-flops take their data from the `data` port through four
  levels, and index entries through none; with gating these become the design's
  shortest paths, so hold must be fixed at their source. In the final chip that
  source is the loader's register, not a port.
- 580 gated clock branches will stress clock-tree synthesis, and routed gated
  designs already needed two to three times the detailed-routing effort of
  ungated ones. Whether the `storage` plan routes, and what it does to hold and
  skew, needs one physical run with its own allocation; feeding `gated.v` to the
  flow also means disabling its own gating and its RTL linter for that input.
- The representation of registers in `Circuit` is unchanged. Emitting explicit
  enable registers would be a new RTL artifact with its own read-back; nothing
  measured so far requires it.

## Reproduction

```sh
lake build Pinwheel structure_report
lake env lean -DwarningAsError=true --run test/Enables.lean
python3 scripts/check-structure.py --tag NAME          # also writes the plans
python3 scripts/gate-clocks.py --rtl RTL --plan build/structure/NAME/plan-storage.tsv \
  --testbench MEASURED_DIR --tag NAME
```

`MEASURED_DIR` is a completed `measure-storage-variant.py` output for RTL with the
same interface; it supplies the testbench, vectors and storage observation.
