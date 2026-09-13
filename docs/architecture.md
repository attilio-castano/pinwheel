# Architecture plan: Lean as the foundation

Planning record: **2026-09-12**.

Setup update: **2026-09-13**. The minimal Lean package and toolchain setup are authorized. The package contains a bitvector setup example; protocol and hardware implementation remain on hold. No UART model, circuit generator, protocol proofs, simulation results, or synthesis results exist yet. See [development setup](development.md) for the installed toolchain and validation evidence.

## Design objective

Build a programmable protocol engine whose instruction semantics make precise pin timing explicit. Use Lean to specify behavior, execute reference models, and prove properties that inform the circuit design. The [competition brief](competition.md) owns external requirements; the [UART experiment](uart-experiment.md) owns the first milestones.

Lean replaces Mojo's proposed roles in hardware generation, program assembly, and reference checking, and adds specifications and proofs. The prior Python packaging scaffold has been removed. This decision does not establish a working Lean-to-hardware compiler.

## Three connected layers

| Layer | Responsibility | Intended evidence |
| --- | --- | --- |
| Protocol specification | Describe observable pin behavior and timing independently of an implementation. | An executable contract; for UART transmission, a cycle-indexed output trace. |
| Machine and program compiler | Define finite state, instruction encoding, storage, and execution on each clock cycle; translate supported protocols into programs. | Invariants and proofs that executing a compiled program produces the specified observations under explicit assumptions. |
| Circuit implementation | Realize the machine with bounded registers, combinational logic, and memory. | RTL checks against the contract, a separate model-to-implementation correspondence obligation, and synthesis/physical-flow evidence. |

The first trace abstraction covers a single UART output. Interactive protocols will require behavior dependent on input histories, including sampling and synchronization assumptions. Add those abstractions when a concrete protocol requires them.

Hardware generation produces the circuit that would be fabricated. Protocol compilation produces reloadable instructions for that circuit. Updating a protocol program must not require regenerating RTL. The fixed UART transmitter is an initial milestone toward that engine.

## Let timing obligations inform hardware

An action meaning "drive a level for N cycles" must define which edges begin and end the interval. Consecutive actions must account for instruction fetch and decode, including whether consecutive one-cycle actions are implementable. Counter bounds, program capacity, invalid encodings, reset, and loading while halted are part of the machine contract.

Use these obligations to evaluate instruction encoding, counters, and possible prefetching. Prove timing claims for the supported finite ranges; measure hardware cost through synthesis before expanding the instruction set. Exact storage sizes, clock frequency, and microarchitecture remain open.

## Proposed hardware path

```text
Circuit:
Lean circuit description -> hardware MLIR text -> CIRCT -> Verilog
                                                        -> simulation / synthesis

Program:
Lean protocol compiler -> encoded instructions -> writable engine memory
```

Lean would construct a restricted circuit representation and emit ordinary MLIR text using existing CIRCT hardware dialects. This is a proposed custom emitter, not automatic synthesis of arbitrary Lean functions. A minimal circuit accepted by CIRCT and the RTL simulator is the first backend integration gate.

CIRCT remains a candidate backend pending that gate. No custom MLIR dialect or general-purpose hardware compiler is needed for the first experiment.

## Proof and validation boundaries

- State protocol behavior independently of implementation transitions. A checker may use the protocol contract, but must not reuse the generator's transition or frame-assembly logic as its oracle.
- Keep proofs beside the definitions they establish. Accepted claims must contain no unfinished proof placeholders (`sorry`/`admit`) and must disclose assumptions and axiom dependencies; do not add an axiom to assume the desired result.
- Prove the fixed transmitter's observations satisfy the UART contract, then prove the UART program compiler against the engine semantics. State supported parameter ranges and initial-state, reset, and loading assumptions.
- A Lean theorem about a model does not verify the circuit emitter, CIRCT transformations, or emitted RTL. Establish implementation correspondence separately; report simulation as simulation until a proof or equivalence check covers the stated boundary.
- Clock-cycle proofs assume a digital clock and defined sampling behavior. Synthesis, mapped area, routed timing, and electrical constraints require their own checks. No first-stage result establishes physical pin behavior or tapeout readiness.

Record exactly which artifacts each result covers, along with tool versions, configurations, program contents, and RTL identity. Preserve failed checks and unresolved assumptions alongside successful evidence.

## Proposed repository structure

The root Lean configuration and `Pinwheel.lean` now exist for setup validation. The domain modules, CLI, tests, and examples below remain a plan; create them only when their milestone begins. Keep this document as the single source for the proposed layout.

```text
README.md
.gitignore
lean-toolchain                   # Pinned Lean version
lakefile.toml                    # Lean library and executable targets
lake-manifest.json               # Lake-managed dependency resolution
Pinwheel.lean                    # Setup example now; public imports as modules arrive
Pinwheel/
  Trace.lean                     # Cycle-indexed pin observations
  UART/
    Spec.lean                    # Independent 8N1 behavior
    Tx.lean                      # Finite-state transmitter and proofs
  Engine/
    ISA.lean                     # Instructions, encoding, validity
    Step.lean                    # Cycle semantics and invariants
  Compile/
    UART.lean                    # UART -> engine program, correctness
  Hardware/
    Circuit.lean                 # Restricted circuit representation
    Emit.lean                    # Proposed hardware MLIR emission
Main.lean                        # Generation / model execution CLI
test/                            # RTL stimulus and independent checks
examples/                        # Small protocol programs
docs/
  competition.md                 # External rules and sources
  architecture.md                # Design layers and proof boundaries
  uart-experiment.md             # Milestones and acceptance criteria
  development.md                 # Toolchain setup and verification commands
build/                           # Ignored generated RTL, traces, reports
.lake/                           # Ignored Lean build/dependency cache
```

The initial package contains only a bitvector setup example. Add domain modules when the fixed UART milestone begins, and `Engine/` and `Compile/` for programmability. Expand the backend's circuit representation only for operations the implementation uses.

When adopting Tiny Tapeout, reserve its conventional `src/`, `test/`, and `info.yaml` paths for the hardware flow, with Lean sources under `Pinwheel/`. Reconcile generated RTL staging, explicit source lists, test commands, and the upstream template revision then. The template is not adopted yet.

## Toolchain decisions

The package pins `leanprover/lean4:v4.33.1` in `lean-toolchain` and uses Lake for builds. Its generated dependency manifest contains no external packages. Bundled Lean libraries are sufficient for the setup example; Mathlib is not a dependency. See [development setup](development.md) for verified versions and commands.

Select a compatible CIRCT distribution/revision, RTL simulator, and synthesis tool when hardware implementation is authorized. Use CIRCT's compatible MLIR version and extend `development.md` with verified commands then.

## Primary technical sources

- [Lean bitvectors](https://lean-lang.org/doc/reference/latest/Basic-Types/Bitvectors/): fixed-width values and bitvector proof automation.
- [Lean Lake documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/): package configuration, builds, and dependency management.
- [CIRCT hardware representation](https://circt.llvm.org/docs/Dialects/HW/RationaleHW/): modules, ports, and hardware dialects.
- [CIRCT sequential operations](https://circt.llvm.org/docs/Dialects/Seq/): clocked state and registers.
- [CIRCT Verilog generation](https://circt.llvm.org/docs/VerilogGeneration/): RTL export.
- [CIRCT setup](https://circt.llvm.org/docs/GettingStarted/): toolchain setup and LLVM/MLIR revisions.

These links are live documentation, not immutable snapshots. Verify compatibility against selected revisions during setup.
