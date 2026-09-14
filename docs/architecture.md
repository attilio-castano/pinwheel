# Architecture plan: Lean as the foundation

Planning record: **2026-09-12**.

Implementation update: **2026-09-14**. The pure Lean [UART transmitter](uart-model.md), [mode-0 SPI controller](spi-model.md), and [shared programmable engine with both compilers](engine-model.md) are implemented with correctness proofs. See [development setup](development.md) for the toolchain and [shared-engine design](shared-engine.md) for the rationale. The [binary encoding](hardware-baseline.md) and [structural countdown slice](countdown-hardware.md) are also implemented, with Lean proofs, generated RTL simulation, and generic synthesis. The [complete execution core](core-hardware.md) now has structural refinement proofs, generated RTL checks, and generic synthesis. The later [reactive core](reactive-core-hardware.md) now integrates both E64 stores with structural control and complete-machine refinement. The [atomic loader](atomic-loader.md) now implements synchronous staging/commit for the indexed core. External serialized loading remains future work.

## Design objective

The [pure Lean I²C write experiment](i2c-model.md) supplies the next protocol reference. The [candidate reactive engine](reactive-engine.md) now implements drive enables, observed-input waits, guarded timing, terminal capture, conditional continuation, and input qualification. [Compiled I²C](compiled-i2c.md) has complete reference-controller correspondence and executable reload evidence alongside UART/SPI. Its 79-instruction expansion uses an experimental 128-slot typed bank with per-program execution limits. A [counted byte loop](looped-i2c.md) now reuses 15 templates with separate byte data and proves complete-state equality; a [canonical V0 binary image](binary-images.md) now preserves both program forms. The [E64 layout](execution-records.md) and [frontend experiment](execution-hardware.md) now supply a wider decoder and measured direct/indexed stores. The [integrated reactive core](reactive-core-hardware.md) now supplies the extended structural scheduler, metadata, and raw setup interface. The atomic loader now preserves the prior image during upload. [CMOS5L mapping](technology-mapping.md) finds its double-bank register storage too large for the nominal allocation; the original encoded core remains a separate measured baseline.

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

Use these obligations to evaluate instruction encoding, counters, and possible prefetching. Prove timing claims for the supported finite ranges; measure hardware cost through synthesis before expanding the instruction set. The first instruction bank is implemented as 32×16 register bits. Full-core generic synthesis reports 1,907 cells including 543 flip-flop bits. The later atomic-loader experiment now counts staging storage and measures technology-mapped area. Clock frequency, physical fit, and the next storage architecture remain open.

The implemented execution core targets the existing 32-slot logical engine. Its canonical 16-bit encoding is implemented, and the [core baseline](hardware-baseline.md) selects a register-backed store with combinational read; synchronous memory would require explicit fetch-latency and buffering arguments. The later indexed reactive core now has a separate [synchronous loading refinement](atomic-loader.md), counting both images and defining interrupted-upload behavior. External transport and pin mapping still need their own refinement.

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
    RegisterRead.lean            # Combined register-read reference with repeated START
  Engine/
    ISA.lean                     # Typed actions and bounded program storage
    Step.lean                    # Cycle semantics, state, and atomic loading
    Proofs.lean                  # General duration, composition, interface proofs
    Reactive.lean                # Candidate drive/observe/wait machine and typed ISA
    ReactiveProofs.lean          # Wait/timer composition and interface guarantees
    ControlProofs.lean           # Guard, terminal capture, branch, qualification guarantees
    Compatibility.lean           # All legacy programs embed; UART/SPI corollaries
    Fetch.lean                   # Functional-store adapter; no runtime expansion
    FetchProofs.lean              # Agreeing stores preserve the complete engine state
    Counted.lean                 # Bounded nested-loop storage and data operands
  Compile/
    UART.lean                    # UART -> engine program, correctness
    SPI.lean                     # SPI -> engine program, correctness
    StretchedPulse.lean          # Five-slot program for candidate reactive engine
    I2CRead.lean                 # Bounded register-read compiler (256 addresses, 16 samples)
    I2CReadProofs.lean           # Universal read compiler/reference correspondence
    I2C.lean                     # 79-instruction write compiler and result decoding
    I2CPhases.lean               # Reference/compiled-state relation and phase proofs
    I2CProofs.lean               # Full-run pin, busy, and result correspondence
    I2CLoop.lean                 # 15-template write and two separate data bytes
    I2CLoopProofs.lean           # Every fetched instruction equals the explicit image
    I2CLoopCorrectness.lean      # State equality and reference trace corollaries
  Binary/
    Basic.lean                  # Bounded byte/bit/Boolean codecs and prefix laws
    Collections.lean            # Fixed-count list/vector codecs and proofs
    Records.lean                # Canonical operand and instruction record grammar
    RecordProofs.lean           # Every record preserves its following suffix
    Layout.lean                 # Preorder loop/sequence encoding and bounded parser
    Explicit.lean               # Literal instruction adapter and round-trip proof
    Image.lean                  # PWL v0 headers, bounds, canonical whole-image decoding
    ImageProofs.lean            # Whole-image round trips and canonicality
    Bytes.lean                  # Native ByteArray conversions and proofs
    Execution.lean              # Decoded loading/execution and I2C correspondence
    Storage.lean                # Exact serialized-image byte accounting
  Hardware/
    Reactive/                   # Structural reactive scheduler and complete E64 core
      State.lean                # Fixed-width register encoding and model relation
      Scheduler.lean            # Timers, guards, capture forwarding and successor selection
      Equations.lean            # Explicit register-update equations
      Primitives.lean           # Capture/input circuit lemmas
      SchedulerProofs.lean      # Circuit equations
      Refinement.lean           # Scheduler-to-engine step/history proofs
      Core.lean                 # Direct/indexed stores, metadata and raw write interlocks
      CoreProofs.lean           # Full-register-bank machine correspondence
      Emit.lean                 # Named component bindings and MLIR adapter
    Loader/
      Control.lean              # Ordered upload commands, validation and structural control
      Proofs.lean               # Gate/update correspondence and completion/cursor claims
      Store.lean                # Indexed image plus metadata, structural reads/writes
      Machine.lean              # Two images, one reactive scheduler, atomic selection
      MachineProofs.lean        # Complete register-bank step/history correspondence
      Contract.lean             # Preservation, commit, startup and validity invariants
      Emit.lean                 # Named component bindings and MLIR adapter
    Execution/
      Record.lean               # E64 literal fields and canonical codec
      RecordProofs.lean         # Typed round trips and accepted-word canonicality
      Images.lean               # Direct/indexed lowering, certificates, V0 operand widening
      Memory.lean               # Balanced generic read tree and lookup proof
      Decode.lean               # E64 validity checks and structural output wires
      DecodeProofs.lean          # Universal validity and wire-output correspondence
      Stores.lean               # Equal-interface writable direct/indexed circuits
      StoreProofs.lean          # Read/write, busy retention, fetch/run composition
      Emit.lean                 # E64 MLIR modules and port/register names
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
    Interface.lean               # Planned serialized transport and physical pin mapping
    Emit.lean                    # Structural HW/Comb/Seq MLIR emission
Main.lean                        # Generation / model execution CLI
test/
  UART.lean                      # Executable model checks and CSV trace
  SPI.lean                       # Receive/timing/interface checks and CSV trace
  I2C.lean                       # Wire-driven target/monitor, boundaries, negative cases
  I2CAxioms.lean                 # All I2C theorem dependency checks
  I2CRead.lean                   # Combined-read wire matrix and packed fetch backends
  I2CReadAxioms.lean             # Read compiler/reference theorem audit
  Execution.lean                # E64 emission, file lowering, independent vector checks
  Loader.lean                  # Atomic RTL emission and component/oracle checks
  LoaderAxioms.lean            # Every public loader theorem audit
  loader_tb.sv                 # Host commands and physical memory retention checks
  ReactiveCore.lean            # Core emission and structural component/oracle checks
  ReactiveCoreAxioms.lean      # Every public reactive hardware theorem audit
  reactive_core_tb.sv          # Integrated RTL against independent expected states
  ExecutionAxioms.lean          # Every public E64 theorem dependency audit
  execution_decoder_tb.sv       # Raw E64 decoder oracle checks
  execution_store_tb.sv         # Direct/indexed write/read edges and CSV comparison
  Reactive.lean                  # Pulse deadlines, legacy contracts, waits and reload
  ReactiveAxioms.lean            # Candidate-engine theorem dependency audit
  Control.lean                   # Guard/branch/qualification boundaries and faults
  CompiledI2C.lean               # Compiled wire monitor, reference checks, faults/reload
  CompiledI2CAxioms.lean         # Compiler correspondence dependency audit
  Counted.lean                   # Serial selection, loop boundaries, faults/loading
  LoopedI2CAxioms.lean           # Counted-store/compiler theorem dependency audit
  Binary.lean                    # Goldens, malformed images, file/load checks, storage CSV
  BinaryAxioms.lean              # Every public binary theorem dependency audit
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
  check-i2c-read.py              # Combined-read proofs, wire checks, and receipt
  check-loader.py                # Atomic loader proof/RTL/mutation/synthesis receipt
  loader-vectors.py              # Independent host protocol and reload oracle
  check-technology.py            # Pinned CMOS5L mapping of core and atomic loader
  install-technology-library.py  # Hash-verified local Liberty files and license
  check-reactive-core.py         # Whole-machine proof/RTL/synthesis receipt
  reactive-core-vectors.py       # Independent E64 machine and wire protocol oracle
  check-execution.py             # E64 audit, Lean/RTL checks, mutations, synthesis
  execution-vectors.py           # Independent E64 grammar and raw store stimuli
  check-compiled-i2c.py          # Explicit/--looped proofs, shared wire checks, receipts
  check-binary.py                # Binary proofs, files, independent lookup, decoded wire suites
  binary_v0.py                   # Independent Python format/lookup oracle
  install-hardware-tools.py      # Checksum-verified local tool installation
  check-hardware.py              # Countdown proof/RTL checks and synthesis
  check-core.py                  # Full-core proof/RTL checks and synthesis
  core-vectors.py                # Independent deadlines and protocol oracles
tools/
  hardware-toolchain.json        # Official archive pins for darwin-arm64
  technology-library.json        # IHP CMOS5L commit and Liberty/license hashes
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
  looped-i2c.md                  # Counted-store comparison, bounds, proof and cost evidence
  binary-images.md               # PWL v0 grammar, proof boundaries, exact storage report
  i2c-register-read.md           # Combined-read contract and capacity consequences
  execution-records.md           # E64 layout, lowering, and storage choice
  atomic-loader.md              # Host contract, proof boundaries and measured storage
  technology-mapping.md         # Early mapped area/delay and next storage decision
  execution-hardware.md          # Frontend proofs, RTL checks, measurements, next boundary
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

## Register-read capacity experiment

The [bounded register read](i2c-register-read.md) preserves four phases per bit and requires 155 execution addresses plus eleven meaningful sample slots. `Reactive` and `Fetch` now parameterize those capacities while retaining the previous defaults, so the read shares the same instruction semantics at 256 addresses and 16 samples. PWL V0, counted programs, and the measured 32×16 hardware retain their earlier contracts. The E64 layout now accounts for those wider addresses and destinations. Its direct and indexed stores have proved read/write/decoder equations and measured generic RTL costs. The [integrated reactive core](reactive-core-hardware.md) now connects both stores to the scheduler and proves complete-register-bank correspondence. Its indexed candidate saves generic cells while lengthening the dependent read path. The [atomic loader](atomic-loader.md) now supplies synchronous loading and the [technology study](technology-mapping.md) measures early mapped area/delay. Its area result makes storage reduction the next architecture task. Serialized physical loading and routed timing remain ahead.
