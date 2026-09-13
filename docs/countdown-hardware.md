# Countdown hardware: first complete slice

Verified **2026-09-13**, Apple Silicon macOS. Implementation commit: `489a515`. This completes the first encoding/circuit batch in the [processor plan](processor-verification.md). The [hardware baseline](hardware-baseline.md) records the instruction format and selected contract for the future complete core.

## What now exists

`Hardware/Circuit.lean` defines width-indexed constants, inputs, register reads, inversion, AND, subtraction, zero comparison, and multiplexers. Finite expression trees prevent combinational cycles. Register feedback refers to pre-edge values; `Circuit.step` evaluates every next-register expression from the same input/state snapshot. The types preserve signal widths, and `byte_decrement_wrap` explicitly checks eight-bit underflow. Reset and register enables are ordinary next-state multiplexers, with priority visible in the circuit structure.

`Hardware/Countdown.lean` describes two registers: eight remaining-duration bits and one active bit. `Emit.lean` traverses these same expression trees to generate hardware MLIR. The module adapter declares the fixed ports and registers; it does not independently spell out the countdown logic. The representation currently contains exactly the primitives used by this slice. Structural bit selection/concatenation and memory ports will be added with the core decoder/store, where their semantics and lowering can be exercised.

```text
Countdown.circuit ── Expr.eval ── Lean proofs and execution
        │
        └── Emit.expression ── HW/Comb/Seq MLIR ── CIRCT ── SystemVerilog
                                                           │
                                               Icarus simulation + Yosys synthesis
```

## Timing contract

The ports are `clk`, active-high `reset`, `load`, eight-bit `duration` (duration minus one), and outputs `remaining`, `active`, `boundary`. This is a synchronous core slice, not a package pin assignment.

- Reset wins over load and clears both registers on the rising edge.
- Otherwise load sets `remaining = duration`, `active = 1`, even if already active. The future core must issue load only at accepted action entries; a slice load is not a host program commit.
- Without reset/load, an active nonzero timer decrements; an active zero timer stops. Idle retains the remaining bits. Reachable idle states after reset/completion have zero remaining bits.
- `boundary = !reset && active && remaining == 0` is a combinational **edge strobe** evaluated from pre-edge state. It identifies the edge that finishes the old action. It may remain high across consecutive duration-one actions; consumers must sample it at every clock, not detect only its rising transition.

An action loaded on edge 0 with duration `D` has `remaining = D - 1` immediately afterward. The final interval begins after edge `D - 1`; the boundary strobe is consumed on edge `D`. Loading the next action on that edge preserves continuous execution. The slice does not fetch instructions, update protocol pins, or capture receive bits yet.

`tick_refines` proves every reset/load/countdown step agrees with a bounded reference state. `boundary_refines`, `countdown`, `boundary_exact`, and `completed_exact` establish exact duration for every `Fin 256` value, including one and 256 cycles. `engine_countdown` connects the slice directly to the existing `Engine.run` countdown until the next instruction entry. Whole-core correspondence, including behavior at that entry, remains milestone 3.

## Measured checks

- `test/Encoding.lean`: all 65,536 raw instruction words classified, 18,433 accepted and 47,103 rejected; every typed action round-tripped; malformed words faulted without capture/result; oversized host integers were rejected.
- `test/Hardware.lean`: 38,026 structural-circuit edges checked against an independently expressed absolute-deadline oracle. It covers all 256 durations, idle intervals, continuous 1/4/256/1 actions, preemptive loads, and reset/load interruptions.
- `test/countdown_tb.sv`: the generated RTL passed an independently written integer-deadline testbench with the same workload. All 38,026 CSV rows matched Lean byte-for-byte. Boundary is recorded before the edge; register observations are after it.
- Three intentionally faulty RTL variants compiled successfully and failed the expected assertion: subtracting two, expiration one cycle early, and load overriding reset. These establish specific checker sensitivity, not complete translation validation.
- The original UART, SPI, and shared-engine regression suites also passed.
- The checked theorem audit reports only `propext`, `Classical.choice`, and `Quot.sound`, with no unfinished-proof, native-checker, or project-defined axioms. Two early `bv_decide` proofs introduced native-checker assumptions; the audit caught them and they were replaced by direct bit-level proofs before commit.
- Yosys `synth` and `check -assert` completed with **38 generic cells**, including **nine register bits**: eight synchronous-reset/enable flip-flops and one ordinary flip-flop. The remaining 29 cells are generic logic/multiplexers. This is not technology area, tile fit, or timing evidence.

The RTL test starts with uninitialized registers and establishes state with a clocked reset. Lean starts with deliberately dirty register values before that same reset. Agreement is required at the defined observations after initialization; the Lean model has no RTL `X` or analog metastability semantics. The testbench's simulated clock period is stimulus timing, not a supported operating frequency.

## Reproduction and artifact identity

With the pinned Lean toolchain available:

```sh
python3 scripts/install-hardware-tools.py
python3 scripts/check-hardware.py
```

The installer requires Python 3.12+ and currently pins **darwin-arm64 only**. It verifies SHA-256 before extracting official archives under ignored `build/tools/`, without changing global PATH or shell configuration. Cached archives are reverified on subsequent installs. Other hosts need separately reviewed archive pins.

The checked tools are CIRCT **firtool-1.159.0** (LLVM 24.0.0git), OSS CAD Suite **2026-09-13**, Yosys **0.69+24** (`d0e71cfb7-dirty` as distributed), and Icarus **14.0 devel** (`s20260301-436-gd254ea49e-dirty` as distributed). Package URLs and full archive checksums are pinned in [hardware-toolchain.json](../tools/hardware-toolchain.json). The installer was exercised against both cached, checksum-verified archives.

The runner builds Lean, runs encoding/circuit checks, audits theorem dependencies, emits/lowers the circuit, simulates positive and negative RTL, compares traces, and synthesizes. It writes versions, source/artifact hashes, cell counts, logs, and a complete receipt to `build/hardware/report.json`. It removes an old receipt before checking, so failure cannot leave a previous report looking current. Generated tools, traces, RTL, mutants, and netlists stay out of Git.

The pinned CIRCT uses `circt-opt --export-verilog`, which emits Verilog to stdout. An initial attempt with `circt-translate --export-verilog` was rejected because that option is absent in this release; the committed runner uses the verified `circt-opt` route. `-o /dev/null` suppresses its separate MLIR output.

Recorded generated artifact SHA-256 values (full source and artifact list in the receipt):

| Artifact | SHA-256 |
| --- | --- |
| `countdown.mlir` | `14f73983f917cb14a659bd51f0360b4dab1e8b3f02cb32dbd3a11599f5bb41e6` |
| `countdown.sv` | `4dcecc55c06dfce68eb3a0549433299a0864fe1c4af52e042bcd74fe2d95a27a` |
| `countdown-lean.csv` | `72b276175ad8f5b19bd99a45b62e9b2d158631e2f1945b6e6dee48c735f36c0f` |
| `countdown-netlist.json` | `1c0ad7ed6c0371b5cbcdaa3a748e2765222a6e6f3899b0c70a4135b5a54b638d` |

## Remaining proof boundary and next step

The Lean theorems cover `Countdown.circuit` under `Expr.eval`. The lowering maps constants to `hw.constant`, AND/subtraction/mux/zero-test to `comb` operations, inversion to XOR with all ones, and registers to `seq.compreg` on a converted rising-edge clock. Reset remains explicit mux logic. CIRCT and the emitter are tested translation tools; their semantics preservation has not been proved.

No emitted-RTL equivalence proof, gate equivalence check, technology mapping, routing, area, or timing result is claimed. The next bounded implementation should construct the decoder/read path and scheduler around this timer, test consecutive one-cycle actions and slot-31 exhaustion first, and then prove whole-core refinement before extending the instruction set or implementing physical loading. The complete staging/commit transport remains milestone 5.

Primary tool references: [CIRCT sequential operations](https://circt.llvm.org/docs/Dialects/Seq/), [CIRCT combinational operations](https://circt.llvm.org/docs/Dialects/Comb/), and [OSS CAD Suite installation](https://github.com/YosysHQ/oss-cad-suite-build#installation). The archive pins and actual command results above determine this experiment's tool versions.
