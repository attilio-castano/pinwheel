# Architecture: Lean as the foundation

This document owns the design layers, implementation boundaries, and module map.
[Research status](research/status.md) owns the active question; [results](research/results.md)
and the [journal](research/journal.md) own conclusions and history. The original
architecture plan dates to 2026-09-12; this consolidation removes its accumulated
progress updates and speculative file inventory.

## Design objective

Build a programmable protocol engine whose instruction semantics make precise pin
timing explicit. Lean specifies behavior, executes reference models, and proves
properties that constrain circuit design. The [competition brief](competition.md)
owns external requirements; [processor verification](processor-verification.md)
owns the evidence needed across the implementation boundaries.

Hardware generation produces the circuit that would be fabricated. Protocol
compilation produces reloadable instructions for that circuit. Replacing a
protocol program must not require regenerating RTL. The fixed protocol controllers
provide independent behavioral references for the shared engine.

## Three connected layers

| Layer | Responsibility | Evidence |
| --- | --- | --- |
| Protocol specification | Define observable pins, timing, and sampled-input assumptions independently of implementation transitions. | Executable contracts and controller proofs for the supported UART, SPI, and I²C subsets. |
| Machine and program compiler | Define instruction semantics, bounded state, loading, and execution on each edge; compile supported protocols into programs. | Invariants and correspondence between compiled execution and protocol behavior under stated assumptions. |
| Circuit implementation | Realize the machine with encoded registers, combinational logic, memory ports, and loading control. | Circuit-to-engine refinement, separate generated-artifact validation, and mapping/physical measurements. |

The [original engine design](shared-engine.md) explains the UART/SPI-derived timed
Action/Halt model. The [reactive engine](reactive-engine.md) adds drive/release,
observed-input waits, guarded timing, and conditional control needed by I²C.
These have distinct capacity and encoding contracts; a later backend does not
silently redefine the original baseline.

The [timed component contract](timed-components.md) defines input-dependent
observations before and after each edge and composable refinement between
implementations. Checked signal interfaces give typed identities and complete
named observations. These abstractions describe digital behavior; they do not
model propagation delay or establish a memory macro's availability schedule.

## Let timing obligations inform hardware

An action that drives a level for N cycles must specify its entry and exit edges.
Adjacent actions have no implicit fetch interval. Conditional execution must
preserve terminal capture, branch selection, and successor entry capture in their
defined order, including uninterrupted one-cycle branches and self branches.

The implementation must supply each instruction by that edge. Register-backed
combinational reads and synchronous memories have different contracts; SRAM
replacement needs a proved availability/buffering schedule. See [fetch contracts](timed-components.md)
and [storage primitives](storage-primitives.md) for those obligations.

The [atomic loader](atomic-loader.md) owns staging, validation, bank selection,
commit, and busy-write rejection. Account for the old and staged images together.
Reset behavior, invalid programs, initialization, and public observations belong
to the contract. Serialized transport, synchronization, and package pins require
an explicit relationship to these synchronous core semantics.

## Hardware and program paths

```text
Circuit:
Lean structural circuit -> hardware MLIR -> CIRCT -> SystemVerilog
                                                -> simulation / synthesis / physical flow

Program:
Lean protocol compiler -> load image / execution records -> writable engine memory
```

The circuit path uses a restricted width-indexed language with explicit register
and combinational semantics; it does not synthesize arbitrary Lean functions.
Emitters write ordinary CIRCT hardware dialects. [PWL images](binary-images.md)
represent serialized programs, while [E64 records](execution-records.md) describe
literal execution words. Counted load images can be expanded before execution;
the [bounded repetition prototype](storage-study.md#bounded-runtime-repetition)
separately investigates reconstruction at runtime. Load-image byte counts and
allocated hardware storage are different measurements.

## Proof and validation boundaries

[Processor verification](processor-verification.md#the-chain-of-evidence) defines
the state relation and acceptance gates. Its central requirement is exact modeled
observation preservation for the supported programs, input histories, and initial
states. Proofs must disclose assumptions and contain no unfinished proof placeholders.

A proof of Lean circuit semantics does not prove the emitter, CIRCT transformations,
or mapped gates. Independent RTL checks, translation/equivalence work, and physical
checks supply different evidence. Likewise, exact cycle counts do not establish
nanosecond timing or external electrical compliance. Use the [research workflow](research/README.md#evidence-standards-for-hardware)
when reporting those claims and artifact identities.

<a id="proposed-repository-structure"></a>

## Repository structure

This map describes existing owners rather than promising individual future files.
The legacy section anchor above preserves links from the original experiment plan.
Proofs remain beside the definitions they establish; emitters depend on semantic
modules rather than defining their contracts.

| Path | Responsibility |
| --- | --- |
| `Pinwheel/UART/`, `Pinwheel/SPI/`, `Pinwheel/I2C/` | Independent protocol specifications, reference controllers, and proofs. |
| `Pinwheel/Engine/` | Original and reactive instruction semantics, loading/execution, compatibility, functional fetch, and counted programs. |
| `Pinwheel/Compile/` | Protocol compilers and correspondence, including explicit and looped I²C programs. |
| `Pinwheel/Binary/` | PWL codecs, layout, round trips, decoded execution, and serialized-size accounting. |
| `Pinwheel/Hardware/Circuit.lean` | Width-indexed expressions, register updates, and their digital semantics. |
| `Pinwheel/Hardware/Timed.lean`, `Pinwheel/Hardware/Interface.lean` | Exact-edge component refinement and checked signal interfaces; the latter is not a physical loading interface. |
| `Pinwheel/Hardware/Encoding.lean`, `Core*.lean`, `Refinement.lean`, `Protocols.lean` | Original encoded UART/SPI core and compiler-proof composition. |
| `Pinwheel/Hardware/Execution/` | E64 encoding/lowering, decoder, direct/indexed storage, and proofs. |
| `Pinwheel/Hardware/Reactive/` | Structural reactive scheduler, capture/fetch order, interfaces, and integrated core refinement. |
| `Pinwheel/Hardware/Loader/` | Atomic two-bank image loading, validation, machine composition, and proofs. |
| `Pinwheel/Hardware/Storage/` | Capacity-limited, cached, dense, and repetition variants; fetch-choice and command-split experiments. |
| `Pinwheel/Hardware/Emit.lean` and subsystem emission modules | Structural-to-MLIR serialization and concrete wiring adapters. |
| `test/`, `scripts/` | Executable Lean checks, independent oracles, RTL testbenches, audits, and measurement runners. |
| `tools/`, `physical/` | Tool/library pins, physical constraints, controlled experiment configuration, and selected result manifests. |
| `docs/`, `docs/research/` | Technical owners and the central research workflow/status/results/journal. |
| `build/`, `.lake/` | Ignored generated evidence and Lean build artifacts respectively. |

`Pinwheel.lean` and `lakefile.toml` define the library entry point and build targets.
Tool installation and reproduction commands belong in [development](development.md),
and [the technical catalog](README.md) routes subsystem records. Add abstractions
or entry points when an implemented need establishes their contract; no standalone
`Trace.lean`, general generation CLI, or empty example tree is promised here.

Tiny Tapeout integration must reconcile its conventional `src/`, `test/`, and
`info.yaml` paths with existing test ownership, generated RTL staging, explicit
source lists, and the pinned upstream template. Lean sources remain under `Pinwheel/`.

## Toolchain decisions

The repository pins Lean through `lean-toolchain` and uses Lake. Bundled Lean
libraries supply the current package; Mathlib is not a dependency. [Development setup](development.md)
owns verified versions, installation details, and commands.

[Hardware tool pins](../tools/hardware-toolchain.json),
[technology-library pins](../tools/technology-library.json), and
[physical toolchain pins](../tools/physical-toolchain.json) identify the distinct
measurement environments. Reproduction must use the versions and constraints
recorded for that experiment, not assume every historical run used today's tools.

## Primary technical sources

- [Lean bitvectors](https://lean-lang.org/doc/reference/latest/Basic-Types/Bitvectors/): fixed-width values and bitvector proof automation.
- [Lean Lake documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/): package configuration, builds, and dependency management.
- [CIRCT hardware representation](https://circt.llvm.org/docs/Dialects/HW/RationaleHW/): modules, ports, and hardware dialects.
- [CIRCT sequential operations](https://circt.llvm.org/docs/Dialects/Seq/): clocked state and registers.
- [CIRCT Verilog generation](https://circt.llvm.org/docs/VerilogGeneration/): RTL export.
- [CIRCT setup](https://circt.llvm.org/docs/GettingStarted/): toolchain setup and LLVM/MLIR revisions.

These links are live documentation, not immutable snapshots. Verify compatibility against selected revisions during setup.
