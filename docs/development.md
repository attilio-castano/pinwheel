# Development setup

Setup record: **2026-09-13**, macOS on Apple Silicon (`arm64`).

The package includes the original bitvector setup check, [UART transmitter](uart-model.md), [SPI controller](spi-model.md), and [shared engine with both protocol compilers](engine-model.md), with specifications and proofs. The [countdown hardware slice](countdown-hardware.md) now includes generation, RTL simulation, and generic synthesis; the complete processor remains future work. No editor extension is required for this terminal-based workflow.

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

`lakefile.toml` declares the `Pinwheel` library as the default build target and treats Lean warnings as errors. `Pinwheel.lean` imports the fixed protocol models, engine, and compilers, and retains the setup definition `Pinwheel.Setup.invertByte` and its proof. Thus `lake build` checks all proofs as well as the original toolchain example. Run the executable model checks with:

```sh
lake env lean -DwarningAsError=true --run test/UART.lean
lake env lean -DwarningAsError=true --run test/SPI.lean
lake env lean -DwarningAsError=true --run test/Engine.lean
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

Binary instruction encoding and the countdown RTL slice were added after this engine milestone. Payload registers, a hardware loading transport, reactive control flow, and the complete processor remain future work.

## Hardware milestones 1 and 2

The [processor verification plan](processor-verification.md)'s first batch is implemented. The [hardware baseline](hardware-baseline.md) records the binary format and next-core contract; the [countdown record](countdown-hardware.md) records circuit proofs, artifact identities, and the remaining translation/physical boundaries.

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
