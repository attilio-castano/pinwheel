# Development setup

Setup record: **2026-09-13**, macOS on Apple Silicon (`arm64`).

The package includes the original bitvector setup check, [pure Lean UART transmitter](uart-model.md), and [pure Lean SPI controller](spi-model.md), with specifications and proofs. Hardware generation, RTL simulation, and synthesis remain future milestones. No editor extension is required for this terminal-based workflow.

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

`lakefile.toml` declares the `Pinwheel` library as the default build target and treats Lean warnings as errors. `Pinwheel.lean` imports the UART and SPI modules and retains the setup definition `Pinwheel.Setup.invertByte` and its proof. Thus `lake build` checks both protocol proofs as well as the original toolchain example. Run the executable model checks with:

```sh
lake env lean -DwarningAsError=true --run test/UART.lean
lake env lean -DwarningAsError=true --run test/SPI.lean
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

The pure Lean portion of the [UART plan](uart-experiment.md) is implemented; see the [model record](uart-model.md) for its contract and verification. CIRCT, an RTL simulator, and synthesis tools have not been installed as part of this work. Add them only when the hardware integration milestone is authorized.

## SPI milestone

The [SPI model record](spi-model.md) documents the implemented mode-0 controller, proofs, 1,792 passing executable transfers, independent CSV check, and rejected early-completion claim. No additional dependency was needed. `lake build` completed with seven jobs, including both protocol libraries. The existing UART regression also passed.

To reproduce the main SPI axiom checks, place these commands in an ignored scratch `.lean` file after `import Pinwheel`, then compile it with `lake env lean -DwarningAsError=true`:

```lean
#print axioms Pinwheel.SPI.waveform_correct
#print axioms Pinwheel.SPI.run_samples
#print axioms Pinwheel.SPI.result_exact
#print axioms Pinwheel.SPI.mosi_stable_pair
```

All four reported `[propext, Classical.choice, Quot.sound]`, with no unfinished-proof or project-defined axioms. The [shared-engine proposal](shared-engine.md) is the next design plan; its implementation has not begun.

Primary references: [Lean 4.33.1 release](https://github.com/leanprover/lean4/releases/tag/v4.33.1), [Elan toolchain management](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Managing-Toolchains-with-Elan/), and [Lake documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).
