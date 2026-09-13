# Architecture plan: Lean as the foundation

Planning record: **2026-09-12**.

Implementation update: **2026-09-13**. The pure Lean [UART transmitter](uart-model.md), [mode-0 SPI controller](spi-model.md), and [shared programmable engine with both compilers](engine-model.md) are implemented with correctness proofs. See [development setup](development.md) for the toolchain and [shared-engine design](shared-engine.md) for the rationale. The [binary encoding](hardware-baseline.md) and [structural countdown slice](countdown-hardware.md) are also implemented, with Lean proofs, generated RTL simulation, and generic synthesis. The [complete execution core](core-hardware.md) now has structural refinement proofs, generated RTL checks, and generic synthesis. Physical loading and reactive protocol control flow remain future work.

## Design objective

The [pure Lean I²C write experiment](i2c-model.md) supplies the next protocol reference. The [candidate reactive engine](reactive-engine.md) now implements drive enables, observed-input waits, guarded timing, terminal capture, conditional continuation, and input qualification. [Compiled I²C](compiled-i2c.md) has complete reference-controller correspondence and executable reload evidence alongside UART/SPI. Its 79-instruction expansion uses an experimental 128-slot typed bank with per-program execution limits; storage/encoding selection and the extended structural circuit remain ahead. The original encoded core remains the measured hardware baseline.

Build a programmable protocol engine whose instruction semantics make precise pin timing explicit. Use Lean to specify behavior, execute reference models, and prove properties that inform the circuit design. The [competition brief](competition.md) owns external requirements; the [UART experiment](uart-experiment.md) owns the first milestones.

The [processor verification plan](processor-verification.md) owns the next hardware milestones: encoded instructions, a circuit description with Lean semantics, a proof that the concrete processor implements the current engine, generated-RTL validation, and physical-flow checks. The goal includes correctness of the register/logic implementation itself. Producing Verilog is one step in establishing and realizing that design.

Lean replaces Mojo's proposed roles in hardware generation, program assembly, and reference checking, and adds specifications and proofs. The prior Python packaging scaffold has been removed. The implemented hardware route covers the countdown slice and complete timed-action core. It emits a restricted circuit language; it does not synthesize arbitrary Lean programs.

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

Use these obligations to evaluate instruction encoding, counters, and possible prefetching. Prove timing claims for the supported finite ranges; measure hardware cost through synthesis before expanding the instruction set. The first instruction bank is implemented as 32×16 register bits. Full-core generic synthesis reports 1,907 cells including 543 flip-flop bits. Staging storage, technology-mapped area, clock frequency, and further microarchitecture choices remain open.

The implemented execution core targets the existing 32-slot logical engine. Its canonical 16-bit encoding is implemented, and the [core baseline](hardware-baseline.md) selects a register-backed store with combinational read; synchronous memory would require explicit fetch-latency and buffering arguments. The current atomic load operation also needs a separate refinement to a concrete write/commit interface, including all staging storage and behavior during interrupted uploads.

## Proposed hardware path

```text
Circuit:
Lean circuit description -> hardware MLIR text -> CIRCT -> Verilog
                                                        -> simulation / synthesis

Program:
Lean protocol compiler -> encoded instructions -> writable engine memory
```

Lean now constructs a restricted circuit representation with explicit digital semantics and emits ordinary MLIR text using existing CIRCT hardware dialects for the countdown slice and complete core. Prove that the represented circuit implements the engine before claiming processor-model correctness. This is a small custom emitter, not automatic synthesis of arbitrary Lean functions. The countdown circuit has passed the first backend integration gate, with checked state correspondence, generated RTL simulation, and generic synthesis; see the [processor plan](processor-verification.md#milestone-2-a-small-circuit-language-and-a-complete-vertical-slice).

CIRCT has simulation validation for the slice and complete core; see the [core record](core-hardware.md). Translation preservation and gate equivalence remain future work. No custom MLIR dialect or general-purpose hardware compiler is needed for the first experiment.

## Proof and validation boundaries

- State protocol behavior independently of implementation transitions. A checker may use the protocol contract, but must not reuse the generator's transition or frame-assembly logic as its oracle.
- Keep proofs beside the definitions they establish. Accepted claims must contain no unfinished proof placeholders (`sorry`/`admit`) and must disclose assumptions and axiom dependencies; do not add an axiom to assume the desired result.
- Prove the fixed transmitter's observations satisfy the UART contract, then prove the UART program compiler against the engine semantics. State supported parameter ranges and initial-state, reset, and loading assumptions.
- A Lean theorem about a model does not verify the circuit emitter, CIRCT transformations, or emitted RTL. Establish implementation correspondence separately; report simulation as simulation until a proof or equivalence check covers the stated boundary.
- The circuit-refinement proof must include actual instruction decoding, memory access semantics, register encodings, and execution-edge timing. A host upload may span several clocks; relate accepted commits to atomic abstract loads without allowing extra execution cycles. Document reset/initialization, malformed encodings, unknown-state treatment, and any black-boxed components.
- Clock-cycle proofs assume a digital clock and defined sampling behavior. Synthesis, mapped area, routed timing, and electrical constraints require their own checks. No first-stage result establishes physical pin behavior or tapeout readiness.

Record exactly which artifacts each result covers, along with tool versions, configurations, program contents, and RTL identity. Preserve failed checks and unresolved assumptions alongside successful evidence.

## Proposed repository structure

The protocol/engine libraries, hardware encoding/core/refinement modules, tests, and hardware scripts below now exist. `Trace.lean`, the physical interface module, the general CLI, and examples remain planned; create them only when their milestone begins. Keep this document as the single source for the proposed layout.

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
  I2C/
    Bus.lean                     # Drive/release commands and resolved shared lines
    Spec.lean                    # Address/write bits, replies, and bounded timing
    Controller.lean              # Pure write controller with ACK and stretching
    Proofs.lean                  # Wire order, capture, wait, and abort theorems
  Engine/
    ISA.lean                     # Typed actions and bounded program storage
    Step.lean                    # Cycle semantics, state, and atomic loading
    Proofs.lean                  # General duration, composition, interface proofs
    Reactive.lean                # Candidate drive/observe/wait machine and typed ISA
    ReactiveProofs.lean          # Wait/timer composition and interface guarantees
    ControlProofs.lean           # Guard, terminal capture, branch, qualification guarantees
    Compatibility.lean           # All legacy programs embed; UART/SPI corollaries
  Compile/
    UART.lean                    # UART -> engine program, correctness
    SPI.lean                     # SPI -> engine program, correctness
    StretchedPulse.lean          # Five-slot program for candidate reactive engine
    I2C.lean                     # 79-instruction write compiler and result decoding
    I2CPhases.lean               # Reference/compiled-state relation and phase proofs
    I2CProofs.lean               # Full-run pin, busy, and result correspondence
  Hardware/
    Encoding.lean                # Canonical binary format and round-trip proofs
    RawProgram.lean              # Raw-word execution, faults, encoding refinement
    Circuit.lean                 # Width-indexed logic/register trees and semantics
    Countdown.lean               # Timer circuit and engine countdown correspondence
    Decode.lean                  # Structural decoder and canonical-word proofs
    Store.lean                   # Finite register-bank read circuit and selection proof
    CoreState.lean               # Typed core ports/registers and state embedding
    Core.lean                    # Concrete scheduler and executable equations
    CoreProofs.lean              # Structural register updates match those equations
    Refinement.lean              # Concrete-to-engine state/trace and commit proofs
    Protocols.lean               # Core UART/SPI waveform and receive corollaries
    Interface.lean               # Planned host loading ports and commit semantics
    Emit.lean                    # Structural HW/Comb/Seq MLIR emission
Main.lean                        # Generation / model execution CLI
test/
  UART.lean                      # Executable model checks and CSV trace
  SPI.lean                       # Receive/timing/interface checks and CSV trace
  I2C.lean                       # Wire-driven target/monitor, boundaries, negative cases
  I2CAxioms.lean                 # All I2C theorem dependency checks
  Reactive.lean                  # Pulse deadlines, legacy contracts, waits and reload
  ReactiveAxioms.lean            # Candidate-engine theorem dependency audit
  Control.lean                   # Guard/branch/qualification boundaries and faults
  CompiledI2C.lean               # Compiled wire monitor, reference checks, faults/reload
  CompiledI2CAxioms.lean         # Compiler correspondence dependency audit
  Engine.lean                    # Compiled protocols, reloadability, machine checks
  Encoding.lean                  # Exhaustive raw-word and typed instruction checks
  Hardware.lean                  # Circuit timing checks, MLIR and CSV generation
  countdown_tb.sv                # Independent RTL timing oracle
  Core.lean                      # Core/decoder emission and structural vector checks
  CoreAxioms.lean                # Selected full-core theorem dependency audit
  core_tb.sv                    # Full-core RTL observations and memory retention
  decoder_tb.sv                 # Exhaustive standalone RTL decoder checks
scripts/
  check-i2c.py                   # Pure Lean I2C build/audit/checks and artifact receipt
  check-reactive.py              # Candidate-engine proofs, tests, and artifact receipt
  check-compiled-i2c.py          # I2C compiler proofs, execution checks, and receipt
  install-hardware-tools.py      # Checksum-verified local tool installation
  check-hardware.py              # Countdown proof/RTL checks and synthesis
  check-core.py                  # Full-core proof/RTL checks and synthesis
  core-vectors.py                # Independent deadlines and protocol oracles
tools/
  hardware-toolchain.json        # Official archive pins for darwin-arm64
examples/                        # Small protocol programs
docs/
  competition.md                 # External rules and sources
  architecture.md                # Design layers and proof boundaries
  uart-experiment.md             # Milestones and acceptance criteria
  uart-model.md                  # Implemented pure Lean contract and proof coverage
  spi-model.md                   # Implemented SPI contract and proof coverage
  i2c-model.md                   # Pure I2C experiment and derived engine extensions
  reactive-engine.md             # Candidate extended machine and compatibility evidence
  compiled-i2c.md                # Complete write compilation, proofs, storage decision
  shared-engine.md               # Derived requirements and implementation rationale
  engine-model.md                # Implemented engine contract and proof/test evidence
  processor-verification.md      # Staged concrete-processor proof and hardware plan
  hardware-baseline.md           # Binary format and implemented core contract
  countdown-hardware.md          # Implemented circuit slice and artifact evidence
  core-hardware.md               # Complete core, proof/RTL/synthesis evidence
  development.md                 # Toolchain setup and verification commands
build/                           # Ignored generated RTL, traces, reports
.lake/                           # Ignored Lean build/dependency cache
```

The UART model uses bounded symbol and cycle counters. SPI uses bounded phase and cycle counters plus eight receive registers. The shared engine uses 32 instruction slots, a bounded program index, a remaining-duration counter, output registers, and eight receive slots. A standalone `Trace.lean` abstraction remains deferred until shared definitions help further proofs. Expand the backend's circuit representation only for operations the implementation uses.

When adopting Tiny Tapeout, reserve its conventional `src/`, `test/`, and `info.yaml` paths for the hardware flow, with Lean sources under `Pinwheel/`. Reconcile generated RTL staging, explicit source lists, test commands, and the upstream template revision then. The template is not adopted yet.

## Toolchain decisions

The package pins `leanprover/lean4:v4.33.1` in `lean-toolchain` and uses Lake for builds. Its generated dependency manifest contains no external packages. Bundled Lean libraries suffice for the setup, protocol, engine, and compiler proofs; Mathlib is not a dependency. See [development setup](development.md) for verified versions and commands.

The [pinned hardware tools](../tools/hardware-toolchain.json) use CIRCT firtool-1.159.0 and OSS CAD Suite 2026-09-13. Their verified installation and reproduction commands are in [development.md](development.md#hardware-milestones-1-and-2).

## Primary technical sources

- [Lean bitvectors](https://lean-lang.org/doc/reference/latest/Basic-Types/Bitvectors/): fixed-width values and bitvector proof automation.
- [Lean Lake documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/): package configuration, builds, and dependency management.
- [CIRCT hardware representation](https://circt.llvm.org/docs/Dialects/HW/RationaleHW/): modules, ports, and hardware dialects.
- [CIRCT sequential operations](https://circt.llvm.org/docs/Dialects/Seq/): clocked state and registers.
- [CIRCT Verilog generation](https://circt.llvm.org/docs/VerilogGeneration/): RTL export.
- [CIRCT setup](https://circt.llvm.org/docs/GettingStarted/): toolchain setup and LLVM/MLIR revisions.

These links are live documentation, not immutable snapshots. Verify compatibility against selected revisions during setup.
