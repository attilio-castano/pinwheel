# Architecture plan: Lean as the foundation

Planning record: **2026-09-12**.

Implementation update: **2026-09-13**. The pure Lean [UART transmitter](uart-model.md), [mode-0 SPI controller](spi-model.md), and [shared programmable engine with both compilers](engine-model.md) are implemented with correctness proofs. See [development setup](development.md) for the toolchain and [shared-engine design](shared-engine.md) for the rationale. Binary encoding, circuit generation, RTL simulation, synthesis, and reactive protocol control flow remain unimplemented.

## Design objective

Build a programmable protocol engine whose instruction semantics make precise pin timing explicit. Use Lean to specify behavior, execute reference models, and prove properties that inform the circuit design. The [competition brief](competition.md) owns external requirements; the [UART experiment](uart-experiment.md) owns the first milestones.

The [processor verification plan](processor-verification.md) owns the next hardware milestones: encoded instructions, a circuit description with Lean semantics, a proof that the concrete processor implements the current engine, generated-RTL validation, and physical-flow checks. The goal includes correctness of the register/logic implementation itself. Producing Verilog is one step in establishing and realizing that design.

Lean replaces Mojo's proposed roles in hardware generation, program assembly, and reference checking, and adds specifications and proofs. The prior Python packaging scaffold has been removed. This decision does not establish a working Lean-to-hardware compiler.

## Three connected layers

| Layer | Responsibility | Intended evidence |
| --- | --- | --- |
| Protocol specification | Describe observable pin behavior and timing independently of an implementation. | An executable contract; for UART transmission, a cycle-indexed output trace. |
| Machine and program compiler | Define finite state, instruction encoding, storage, and execution on each clock cycle; translate supported protocols into programs. | Invariants and proofs that executing a compiled program produces the specified observations under explicit assumptions. |
| Circuit implementation | Realize the machine with explicitly encoded registers, combinational logic, and memory ports. | A concrete-to-engine refinement proof, separate translation/equivalence evidence for generated artifacts, and synthesis/physical-flow checks. |

The UART contract covers a single output. SPI adds a three-pin output vector and receive behavior defined over arbitrary edge-indexed input histories. Its eight bounded receive slots make input sampling explicit. The shared engine implements timed actions with optional entry-edge capture. General countdown and composition theorems establish exact action timing; compiler simulation proofs connect execution to the independent protocol contracts. A general trace framework is still deferred.

Hardware generation produces the circuit that would be fabricated. Protocol compilation produces reloadable instructions for that circuit. Updating a protocol program must not require regenerating RTL. The fixed UART and SPI controllers are reference milestones toward that engine.

## Let timing obligations inform hardware

An action meaning "drive a level for N cycles" must define which edges begin and end the interval. Consecutive actions must account for instruction fetch and decode, including whether consecutive one-cycle actions are implementable. Counter bounds, program capacity, invalid encodings, reset, and loading while halted are part of the machine contract.

Use these obligations to evaluate instruction encoding, counters, and possible prefetching. Prove timing claims for the supported finite ranges; measure hardware cost through synthesis before expanding the instruction set. Exact storage sizes, clock frequency, and microarchitecture remain open.

The first physical core will target the existing 32-slot logical engine. Its word encoding and memory implementation remain design decisions. A small register-backed store with combinational read is the first candidate to evaluate; synchronous memory would require explicit fetch-latency and buffering arguments. The current atomic load operation also needs a separate refinement to a concrete write/commit interface, including all staging storage and behavior during interrupted uploads.

## Proposed hardware path

```text
Circuit:
Lean circuit description -> hardware MLIR text -> CIRCT -> Verilog
                                                        -> simulation / synthesis

Program:
Lean protocol compiler -> encoded instructions -> writable engine memory
```

Lean would construct a restricted circuit representation with explicit digital semantics and emit ordinary MLIR text using existing CIRCT hardware dialects. Prove that the represented circuit implements the engine before claiming processor-model correctness. This is a proposed custom emitter, not automatic synthesis of arbitrary Lean functions. A countdown circuit with a checked state correspondence, generated RTL simulation, and initial synthesis is the first complete backend integration gate; see the [processor plan](processor-verification.md#milestone-2-a-small-circuit-language-and-a-complete-vertical-slice).

CIRCT remains a candidate backend pending that gate. No custom MLIR dialect or general-purpose hardware compiler is needed for the first experiment.

## Proof and validation boundaries

- State protocol behavior independently of implementation transitions. A checker may use the protocol contract, but must not reuse the generator's transition or frame-assembly logic as its oracle.
- Keep proofs beside the definitions they establish. Accepted claims must contain no unfinished proof placeholders (`sorry`/`admit`) and must disclose assumptions and axiom dependencies; do not add an axiom to assume the desired result.
- Prove the fixed transmitter's observations satisfy the UART contract, then prove the UART program compiler against the engine semantics. State supported parameter ranges and initial-state, reset, and loading assumptions.
- A Lean theorem about a model does not verify the circuit emitter, CIRCT transformations, or emitted RTL. Establish implementation correspondence separately; report simulation as simulation until a proof or equivalence check covers the stated boundary.
- The circuit-refinement proof must include actual instruction decoding, memory access semantics, register encodings, and execution-edge timing. A host upload may span several clocks; relate accepted commits to atomic abstract loads without allowing extra execution cycles. Document reset/initialization, malformed encodings, unknown-state treatment, and any black-boxed components.
- Clock-cycle proofs assume a digital clock and defined sampling behavior. Synthesis, mapped area, routed timing, and electrical constraints require their own checks. No first-stage result establishes physical pin behavior or tapeout readiness.

Record exactly which artifacts each result covers, along with tool versions, configurations, program contents, and RTL identity. Preserve failed checks and unresolved assumptions alongside successful evidence.

## Proposed repository structure

The root Lean configuration, `Pinwheel.lean`, `UART/`, `SPI/`, `Engine/`, `Compile/`, and the UART/SPI/Engine test files below now exist. `Trace.lean`, `Hardware/`, `test/Hardware.lean`, the CLI, and examples remain a plan; create them only when their milestone begins. Keep this document as the single source for the proposed layout.

```text
README.md
.gitignore
lean-toolchain                   # Pinned Lean version
lakefile.toml                    # Lean library and executable targets
lake-manifest.json               # Lake-managed dependency resolution
Pinwheel.lean                    # Protocol/engine/compiler imports and setup example
Pinwheel/
  Trace.lean                     # Cycle-indexed pin observations
  UART/
    Spec.lean                    # Independent 8N1 behavior
    Tx.lean                      # Finite-state transmitter and proofs
  SPI/
    Spec.lean                    # Mode-0 pins, sample times, receive contract
    Controller.lean              # Finite full-duplex controller and proofs
  Engine/
    ISA.lean                     # Typed actions and bounded program storage
    Step.lean                    # Cycle semantics, state, and atomic loading
    Proofs.lean                  # General duration, composition, interface proofs
  Compile/
    UART.lean                    # UART -> engine program, correctness
    SPI.lean                     # SPI -> engine program, correctness
  Hardware/
    Encoding.lean                # Planned raw instruction encoding/decoding proofs
    Circuit.lean                 # Planned restricted circuit structures
    Semantics.lean               # Planned meaning of logic/register/memory operations
    Core.lean                    # Planned concrete processor circuit
    Refinement.lean              # Planned concrete-to-engine state/trace proofs
    Interface.lean               # Planned host loading ports and commit semantics
    Emit.lean                    # Planned hardware MLIR emission
Main.lean                        # Generation / model execution CLI
test/
  UART.lean                      # Executable model checks and CSV trace
  SPI.lean                       # Receive/timing/interface checks and CSV trace
  Engine.lean                    # Compiled protocols, reloadability, machine checks
  Hardware.lean                  # Planned circuit/encoding checks and trace fixtures
                                 # RTL stimulus/checks will be added later
examples/                        # Small protocol programs
docs/
  competition.md                 # External rules and sources
  architecture.md                # Design layers and proof boundaries
  uart-experiment.md             # Milestones and acceptance criteria
  uart-model.md                  # Implemented pure Lean contract and proof coverage
  spi-model.md                   # Implemented SPI contract and proof coverage
  shared-engine.md               # Derived requirements and implementation rationale
  engine-model.md                # Implemented engine contract and proof/test evidence
  processor-verification.md      # Staged concrete-processor proof and hardware plan
  development.md                 # Toolchain setup and verification commands
build/                           # Ignored generated RTL, traces, reports
.lake/                           # Ignored Lean build/dependency cache
```

The UART model uses bounded symbol and cycle counters. SPI uses bounded phase and cycle counters plus eight receive registers. The shared engine uses 32 instruction slots, a bounded program index, a remaining-duration counter, output registers, and eight receive slots. A standalone `Trace.lean` abstraction remains deferred until shared definitions help further proofs. Expand the backend's circuit representation only for operations the implementation uses.

When adopting Tiny Tapeout, reserve its conventional `src/`, `test/`, and `info.yaml` paths for the hardware flow, with Lean sources under `Pinwheel/`. Reconcile generated RTL staging, explicit source lists, test commands, and the upstream template revision then. The template is not adopted yet.

## Toolchain decisions

The package pins `leanprover/lean4:v4.33.1` in `lean-toolchain` and uses Lake for builds. Its generated dependency manifest contains no external packages. Bundled Lean libraries suffice for the setup, protocol, engine, and compiler proofs; Mathlib is not a dependency. See [development setup](development.md) for verified versions and commands.

Select a compatible CIRCT distribution/revision, RTL simulator, and synthesis tool when hardware implementation is authorized. Use CIRCT's compatible MLIR version and extend `development.md` with verified commands then.

## Primary technical sources

- [Lean bitvectors](https://lean-lang.org/doc/reference/latest/Basic-Types/Bitvectors/): fixed-width values and bitvector proof automation.
- [Lean Lake documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/): package configuration, builds, and dependency management.
- [CIRCT hardware representation](https://circt.llvm.org/docs/Dialects/HW/RationaleHW/): modules, ports, and hardware dialects.
- [CIRCT sequential operations](https://circt.llvm.org/docs/Dialects/Seq/): clocked state and registers.
- [CIRCT Verilog generation](https://circt.llvm.org/docs/VerilogGeneration/): RTL export.
- [CIRCT setup](https://circt.llvm.org/docs/GettingStarted/): toolchain setup and LLVM/MLIR revisions.

These links are live documentation, not immutable snapshots. Verify compatibility against selected revisions during setup.
