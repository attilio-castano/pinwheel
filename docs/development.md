# Development setup

Setup record: **2026-09-13**, macOS on Apple Silicon (`arm64`).

The package includes the original bitvector setup check, [UART transmitter](uart-model.md), [SPI controller](spi-model.md), and [shared engine with both protocol compilers](engine-model.md), with specifications and proofs. The [countdown slice](countdown-hardware.md) and [complete execution core](core-hardware.md) include structural proofs, generation, RTL simulation, and generic synthesis; physical loading and implementation remain future work. No editor extension is required for this terminal-based workflow.

## Toolchain

The project pins **Lean 4.33.1** using `leanprover/lean4:v4.33.1` in `lean-toolchain`. This was the latest non-prerelease reported by the official release API during setup. Lake is included with the Lean toolchain. Elan manages installation and chooses the pinned version when commands run in the repository.

The machine installation uses Elan **4.2.4** in `~/.elan`, Lean **4.33.1** (commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), and Lake **5.0.0-src+819816b**. The existing user-local `~/.local/bin/env` hook contains a guarded addition of `~/.elan/bin` to PATH; the machine's zsh configuration already sources that hook. This machine-level change is outside the repository. No global default Lean toolchain is selected; the repository pin selects its version.

## Install on another machine

Use the [official Elan installer](https://github.com/leanprover/elan), then install the pinned release:

```sh
curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
sh /tmp/elan-init.sh -y --default-toolchain none --no-modify-path
. "$HOME/.elan/env"
elan toolchain install leanprover/lean4:v4.33.1
```

The installer command above deliberately leaves shell startup files unchanged. To make the commands available in future sessions, source `~/.elan/env` from an appropriate shell startup hook. Agents with a restricted or non-zsh environment can explicitly source that file before invoking Lean. Do not create a machine-specific toolchain override for this project.

On this host, Elan's proxies require write access to `~/.elan/settings.toml` even when launching an installed toolchain. The first sandboxed version/build commands failed with `Operation not permitted`; rerunning with the approved user-directory access succeeded. Restricted agent sessions need that access in addition to write access for repository build artifacts.

The Lean archive contains prebuilt tools; building Lean itself from source is not part of this setup. The checked machine already had Xcode configured. The example imports only bundled `Std`; Mathlib and other external Lean packages are not needed.

## Build

Run these commands from the repository root:

```sh
elan --version
elan show
lean --version
lake --version
lake build
```

`lakefile.toml` declares the `Pinwheel` library as the default build target and treats Lean warnings as errors. `Pinwheel.lean` imports the protocol models, engine, compilers, and structural hardware proofs, and retains the setup definition `Pinwheel.Setup.invertByte` and its proof. Thus `lake build` checks all proofs as well as the original toolchain example. Run the executable model checks with:

```sh
lake env lean -DwarningAsError=true --run test/UART.lean
lake env lean -DwarningAsError=true --run test/SPI.lean
lake env lean -DwarningAsError=true --run test/Engine.lean
lake env lean -DwarningAsError=true --run test/I2C.lean
lake env lean -DwarningAsError=true --run test/Reactive.lean
lake env lean -DwarningAsError=true --run test/Control.lean
lake env lean -DwarningAsError=true --run test/CompiledI2C.lean
```

Commit `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, and Lean sources. Lake generates the dependency manifest; this package has no external dependencies. `.lake/` and `build/` are ignored generated artifacts. A successful incremental `lake build` may reuse already checked artifacts.

## Inspect the proof

After building, inspect the theorem's dependencies using an ignored scratch file:

```sh
mkdir -p build/setup
cat > build/setup/Axioms.lean <<'LEAN'
import Pinwheel
#print axioms Pinwheel.Setup.invertByte_involutive
#eval Pinwheel.Setup.invertByte (0x0f : BitVec 8)
LEAN
lake env lean -DwarningAsError=true build/setup/Axioms.lean
```

Review the reported axioms, not just the build exit code. Accepted proofs must have no unfinished placeholders or undocumented assumptions. `lake env lean` is a direct compiler invocation; pass `-DwarningAsError=true` explicitly to retain the build's warning policy.

## Negative setup check

This intentionally false scratch example checks rejection. It is not part of the library:

```sh
mkdir -p build/setup
cat > build/setup/Reject.lean <<'LEAN'
import Pinwheel
example : (0 : BitVec 8) = 1 := by
  decide
LEAN
lake env lean -DwarningAsError=true build/setup/Reject.lean
```

Expected: a nonzero exit status and a diagnostic that the proposition is false. A missing tool, missing import, or unrelated syntax error would not satisfy this check. Keep the rejected claim out of the default build target.

## Setup evidence

Verified on the setup date:

- Elan resolves in login and non-login zsh sessions. `elan show` selects the toolchain from this worktree's `lean-toolchain` file.
- `lean --version` reports Lean 4.33.1 for `arm64-apple-darwin24.6.0`; `lake --version` reports Lake 5.0.0-src+819816b.
- The first `lake build` generated `lake-manifest.json` with an empty package list and completed successfully with no warnings (3 jobs).
- The axiom inspection reports `[propext, Classical.choice, Quot.sound]`, the standard Lean axioms used by this proof's dependencies. It reports no `sorryAx` or project-defined axioms.
- Evaluation of the complemented byte reports `0xf0#8`.
- The negative check exits with status 1 and reports that `decide` proved `0 = 1` is false. Its import succeeded; rejection is due to the claim itself.
- The library source has no `sorry`, `admit`, or custom axiom declarations. Generated build and scratch files remain ignored.

These results establish the setup example's proof and executable behavior in Lean. They do not establish any UART, RTL, or physical hardware behavior.

## UART milestone

The pure Lean portion of the [UART plan](uart-experiment.md) is implemented; see the [model record](uart-model.md) for its contract and verification. The UART-only milestone did not install hardware tools. The later authorized hardware batch installed the pinned local tools documented below.

## SPI milestone

The [SPI model record](spi-model.md) documents the implemented mode-0 controller, proofs, 1,792 passing executable transfers, independent CSV check, and rejected early-completion claim. No additional dependency was needed. `lake build` completed with seven jobs, including both protocol libraries. The existing UART regression also passed.

To reproduce the main SPI axiom checks, place these commands in an ignored scratch `.lean` file after `import Pinwheel`, then compile it with `lake env lean -DwarningAsError=true`:

```lean
#print axioms Pinwheel.SPI.waveform_correct
#print axioms Pinwheel.SPI.run_samples
#print axioms Pinwheel.SPI.result_exact
#print axioms Pinwheel.SPI.mosi_stable_pair
```

All four reported `[propext, Classical.choice, Quot.sound]`, with no unfinished-proof or project-defined axioms.

## Shared engine milestone

The later [I²C reference experiment](i2c-model.md) remains separate from this engine; it motivates the next abstract-machine extension.

The [engine model record](engine-model.md) documents the implemented 32-slot machine, atomic loading, typed compilers, and proof coverage. The full `lake build` completed with 12 jobs. No dependency was added.

The engine suite passed 2,560 compiled protocol transfers plus mixed-duration, entry-capture, overwrite, halt/fault, reset/restart, busy loading, and UART → SPI → UART cases. The fixed UART and SPI suites also passed. Independent CSV comparison matched the engine's UART trace to all 42 reference rows and its SPI trace to every common field in all 70 reference rows.

To inspect the new main proofs, add these commands to an ignored scratch `.lean` file after `import Pinwheel`, then compile with `lake env lean -DwarningAsError=true`:

```lean
#print axioms Pinwheel.Engine.countdown
#print axioms Pinwheel.Engine.action_boundary
#print axioms Pinwheel.Engine.two_action_boundary
#print axioms Pinwheel.Engine.load_busy
#print axioms Pinwheel.Engine.load_stopped
#print axioms Pinwheel.Compile.UART.run_simulation
#print axioms Pinwheel.Compile.UART.waveform_correct
#print axioms Pinwheel.Compile.SPI.run_simulation
#print axioms Pinwheel.Compile.SPI.waveform_correct
#print axioms Pinwheel.Compile.SPI.received_correct
```

The general duration/composition proofs reported `[propext, Quot.sound]`; loading proofs reported `[propext]`; the main compiler proofs reported `[propext, Classical.choice, Quot.sound]`. No unfinished-proof or custom axioms were reported. A false early-completion claim for two consecutive duration-one actions was rejected by `decide` because the proposition is false.

Binary instruction encoding and the countdown RTL slice were added after this engine milestone. The complete execution core was subsequently implemented. Payload registers, a physical loading transport, and reactive control flow remain future work.

## Hardware milestones 1 and 2

The [processor verification plan](processor-verification.md)'s first batch is implemented. The [hardware baseline](hardware-baseline.md) records the binary format and core contract; the [countdown record](countdown-hardware.md) records circuit proofs, artifact identities, and the remaining translation/physical boundaries.

On Apple Silicon macOS with Python 3.12+:

```sh
python3 scripts/install-hardware-tools.py
python3 scripts/check-hardware.py
```

The installer verifies the official archive checksums in `tools/hardware-toolchain.json` and extracts under ignored `build/tools/`. It does not modify shell configuration or install global commands. Both cached archives and extracted tools currently occupy about 3.2 GB. Only `darwin-arm64` archives are pinned; other platforms need separate reviewed pins.

Verified tools: CIRCT `firtool-1.159.0` with its bundled LLVM 24.0.0git, OSS CAD Suite `2026-09-13`, Yosys `0.69+24` (`d0e71cfb7-dirty` as distributed), and Icarus Verilog `14.0 devel` (`s20260301-436-gd254ea49e-dirty` as distributed). The runner invokes their local binaries directly. The exact versions, archive identities, commands, logs, generated RTL/netlists, traces, axiom audit, and machine-readable report are under `build/hardware/`.

The complete library build passed with 17 jobs. Encoding checks cover all 65,536 words. Lean and RTL each passed 38,026 edges with identical CSV output, three faulty RTL variants were rejected for the expected assertion, and generic synthesis passed `check -assert` with 38 cells including nine register bits. The axiom audit accepts only the project's standard Lean axioms. The original UART (768 transfers), SPI (1,792 transfers), and shared-engine (2,560 transfers plus boundary/reload cases) regressions also passed; they remain separate checks using the commands above.

For only the Lean portions, without installing hardware tools:

```sh
lake build
lake env lean -DwarningAsError=true --run test/Encoding.lean
lake env lean -DwarningAsError=true --run test/Hardware.lean
```

The hardware Lean suite emits `build/hardware/countdown.mlir` and `countdown-lean.csv`. The full runner lowers with `circt-opt --canonicalize --lower-seq-to-sv --lower-hw-to-sv --export-verilog -o /dev/null`, capturing Verilog from stdout; this release does not offer that translation through `circt-translate`. Icarus consumes the emitted SystemVerilog. Yosys uses the generated `synthesis.ys` script for generic synthesis; no technology library or clock target is supplied.

For restricted sessions on this checked host, invoking the installed toolchain binaries directly avoids the Elan proxy's settings write:

```sh
PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.33.1/bin:$PATH" python3 scripts/check-hardware.py
```

This is a process-local PATH change, with no shell startup edit. The default reproduction command remains sufficient in an unrestricted terminal.

Primary references: [Lean 4.33.1 release](https://github.com/leanprover/lean4/releases/tag/v4.33.1), [Elan toolchain management](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Managing-Toolchains-with-Elan/), and [Lake documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).

## Hardware milestone 3: complete execution core

Run the full core experiment with the same installed tools:

```sh
python3 scripts/check-core.py
```

It builds the 24-job library, audits 16 selected theorem dependencies, exports the actual compiled images, checks every raw decoder word, compares 71,703 independent expected edges in Lean and RTL, rejects three faulty RTL variants, and synthesizes the full core. The [core record](core-hardware.md) documents the 1,032-transfer coverage matrix, 1,907 generic cells, 543 flip-flop bits, and remaining proof boundaries. Full reports and hashes are under `build/core/`; this remains separate from the timer's `build/hardware/` receipt.

The generic emitter sets CIRCT's supported-output options and the runner adds `--hw-legalize-modules` before `--export-verilog`. That required pass removes packed-array constructs unsupported by the selected tools. The earlier timer uses no such array read path. Common-expression sharing changed the timer's emitted formatting; its reset-priority mutation fixture was updated and the timer suite rerun. Its original published hashes identify the earlier implementation, not newly generated files.

## I²C reference milestone

The [I²C model record](i2c-model.md) documents single-controller address-plus-byte writes, ACK/NACK, open-drain bus resolution, clock stretching, and abort behavior. No Lean dependency or hardware tool is added. Reproduce its build, 19-theorem axiom audit, bus tests, and negative cases with:

```sh
python3 scripts/check-i2c.py
```

For restricted sessions on this host, use the process-local installed-toolchain PATH described above. The runner writes logs, a stretched example CSV, coverage, and source/artifact hashes to ignored `build/i2c/`; it removes an old `report.json` before starting and publishes a new one only after all checks pass.

The library build passed with 28 jobs. The suite passed 4,224 transactions across 822,896 observed cycles, all 256 wait budgets and high durations, and three deliberate faulty-transition checks. The 19 audited theorems depend only on standard Lean axioms or none. The existing 2,560-transfer engine regression and boundary/reload cases also passed. This batch did not change or rerun the structural RTL; the prior hardware records retain their own artifact identities. I²C compilation, full-transaction refinement, and hardware integration remain future work.

## Candidate reactive-engine milestone

The [candidate-engine record](reactive-engine.md) documents drive enables, two observed inputs, selected capture, and observation-anchored timed continuation. The old engine and structural hardware remain intact. Reproduce using the existing Lean toolchain and Python:

```sh
python3 scripts/check-reactive.py
```

The 32-job library build and all 30 named theorem audits passed. The executable suite passed 1,024 pulses across 528,384 observations, all wait budgets and durations with both input selectors/polarities, 1,024 UART/SPI compatibility transfers, mixed UART → SPI → pulse → UART reload, and three rejected faulty transitions. The suite checks legacy protocols against their independent waveform/sample contracts as well as original engine execution. Logs, trace, coverage, and source/artifact hashes are under ignored `build/reactive/`. This receipt covers typed Lean semantics and executable checks, with no new hardware encoding, RTL, or synthesis result.

## Compiled I²C milestone

The later [compiled-I²C record](compiled-i2c.md) adds masked guards, terminal capture/branching, qualification, and a 79-instruction write program. The candidate now uses 128 slots with per-program execution limits; the old encoded core remains unchanged. Reproduce:

```sh
python3 scripts/check-compiled-i2c.py
python3 scripts/check-reactive.py
```

The full build passes with 36 jobs. The compiler audit checks 29 theorems, including arbitrary-input run correspondence and pin/busy/result corollaries. The generic reactive audit now checks 38 theorems and also runs `test/Control.lean`. Both audits allow only standard Lean axioms or none.

Compiled execution passes 4,224 transactions across 822,896 cycles, matches the reference cycle by cycle, and passes an independent wire monitor, sampled error-path forks, three rejected corrupted programs, and UART → SPI → I²C → UART reload. Generic pulse, UART/SPI, guard/branch, qualification, and interface regressions also pass. The compiled receipt, source hashes, logs, and trace are under `build/compiled-i2c/`; generic evidence remains under `build/reactive/`. The full-run compiler theorem excludes reset during execution; engine reset clears status and releases lines, while the reference exposes `resetAbort`. No RTL/synthesis flow was rerun for this Lean-only extension.

The Lean-only portion can be reproduced without hardware tools:

```sh
lake build
lake env lean -DwarningAsError=true test/CoreAxioms.lean
lake env lean -DwarningAsError=true --run test/Core.lean
python3 scripts/core-vectors.py
lake env lean -DwarningAsError=true --run test/Core.lean check
```

The first Core invocation emits circuits and protocol images; the Python step derives independent vectors and adds deterministic raw memory cases; the final invocation checks structural circuit execution. The full runner performs these in order. On this host, a restricted session can use the same process-local toolchain PATH prefix shown above with `scripts/check-core.py`.

## Counted byte-loop comparison

The [loop comparison](looped-i2c.md) adds a bounded instruction-store frontend that reuses 15 templates for the explicit image's 79 execution addresses. The two byte values are separate data. The format permits two nested loops, at most eight iterations each, 128 execution slots, and 64 syntax nodes. This write uses 31 nodes in total. No new tool or dependency is required.

```sh
python3 scripts/check-compiled-i2c.py --looped
python3 scripts/check-compiled-i2c.py
python3 scripts/check-reactive.py
```

The loop runner uses the same wire target and monitor as the explicit runner and compares full engine states each cycle. It passes 4,224 transactions / 822,896 observed cycles with identical example timings; 6,144 generic serial loops, error forks, five loop-specific negative variants, and mixed program replacement supply additional checks. The original three capture/branch corruptions are also retained. Logs, trace, coverage, 16-theorem dependency audit, and source/artifact hashes are under `build/looped-i2c/`; the current library build has 42 jobs.

The universal fetch/state proofs cover every configuration, request, and input history. One-step loop-to-explicit equality includes reset/start; the inherited full-run reference claims still exclude reset/reload. The original reference-reset distinction remains. Instruction-template counts exclude descriptor metadata and data; no binary storage size, circuit timing, area, or new hardware result is claimed. The following V0 milestone now defines a load-image representation; structural store comparison remains ahead.

## PWL V0 binary-image milestone

The [binary-image record](binary-images.md) specifies byte-aligned headers, fields, instruction records, and preorder layouts. Universal prefix/whole-image/native-byte round trips compose with decoded execution and abstract loading. No new dependency is required.

```sh
python3 scripts/check-binary.py
python3 scripts/check-reactive.py
```

The 53-job build and all 37 binary theorem audits pass. Validation includes 1,280 image round trips with every fetched address checked, 920 rejected truncations, malformed fields/bounds/trailing data, independent golden bytes, file-backed mixed execution, and an independent Python reader matching 512 fetched instructions across four files. Each decoded I²C backend passes 4,224 transactions / 822,896 cycles with identical examples and error forks. The generic engine suite also retains its passing 38-theorem audit and protocol/boundary checks.

`build/binary/` contains native `.pwl` files, exact `storage.csv`, fetch CSVs, audit/logs, and the reproducible success receipt. The I²C images are 715 bytes explicit and 205 bytes counted, including metadata and explicit padding. The two wire backends write traces and coverage under `build/binary-explicit/` and `build/binary-looped/`. Python import caches are ignored alongside generated build artifacts.

The decoder reconstructs typed programs before execution. It does not yet define raw-byte cycle timing, physical memory widths, circuit decoding, or upload hardware. Serialized-image savings are distinct from allocated chip memory and area; no RTL/synthesis flow was rerun for this milestone.
