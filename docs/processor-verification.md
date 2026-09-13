# Plan: a processor designed and verified in Lean

Planning record: **2026-09-13**. This document defines future implementation milestones. The current completed work is recorded in [engine-model.md](engine-model.md); no circuit representation, encoded processor, RTL backend, or physical implementation is established by this plan.

## Objective and relationship to the competition

Design the circuit that executes Pinwheel's instructions and prove that its digital behavior implements the instruction-level engine. Compose that result with the existing UART and SPI compiler proofs. Use implementation and physical-flow evidence to establish the remaining constraints.

The competition asks for an open-source, reprogrammable protocol-emulator ASIC, encourages novel design/verification methods, and requires attention to mapped area and routed timing. Its announced allocation is 8×4 Tiny Tapeout tiles. These external requirements belong in [competition.md](competition.md), with the [Jane Street announcement](https://blog.janestreet.com/protocol-emulator-asic-competition/) as the authority. Lean and the particular proof architecture below are Pinwheel design choices.

The immediate target is a concrete implementation of the existing timed-action engine. This gives us a checked baseline for hardware experiments. Meeting that baseline does not establish the competition's broader flexibility goal: payload reuse, input-dependent control, line release, and further protocols still require design work.

## What we already have

- Independent cycle-level UART and SPI specifications and verified finite controllers.
- A shared engine with 32 typed instruction slots, bounded execution state, exact action duration, entry-edge input capture, halt/fault behavior, and atomic loading while stopped.
- Typed program compilers with proofs that engine executions satisfy the protocol specifications.
- Executable boundary, noise, reset, reload, and protocol checks, plus reference CSV traces.

Preserve these as the behavioral reference. A lower-level implementation may add internal registers or change state encoding, but must establish correspondence to the engine's observations. A timing change requires an explicit contract revision and renewed protocol proofs.

## The chain of evidence

```text
Independent protocol contracts
    ^ checked compiler/controller proofs: already implemented
Typed programs + instruction-level engine
    ^ encoding and circuit-refinement proofs: planned
Explicit register, logic, and memory circuit described in Lean
    ^ translation validation / semantics-preservation work: planned
Generated Verilog RTL
    ^ formal equivalence checks where supported: planned
Mapped gate implementation
    + physical-flow checks: area, routing, timing, and process rules
```

Lean would host a restricted hardware-description language with an explicit meaning for its operations. An executable mathematical next-state function alone does not specify the physical memory ports, clock behavior, or logic structure. The circuit representation must make these choices visible.

The central proof obligation is a relation `R` between concrete circuit state and abstract engine state:

1. Reset/initialization establishes the relation under documented program-initialization assumptions.
2. For each execution clock edge and allowed input snapshot, related states transition to related states.
3. Related states have equal output levels, busy/completion/fault observations, and receive results.

This should hold for all supported loaded programs and input histories, rather than only the UART/SPI examples. Induction then extends the one-edge result to whole executions. Internal fetch preparation must not insert observable execution cycles. Multi-cycle host loading will have a separate correspondence to accepted abstract load operations; execution timing cannot be weakened by silently permitting extra cycles.

## Milestone 1: encoded instructions and a concrete core contract

Select a canonical binary instruction format and define both encoding and decoding in Lean. A candidate to evaluate is a 16-bit word containing an opcode bit, three output bits, eight duration bits, a capture-enable bit, and three receive-slot bits. This is a planning candidate, not a selected external ABI. Specify which unused field combinations are canonical, legal aliases, or rejected.

Prove `decode (encode instruction) = success instruction`. Classify every raw word; malformed words must have defined fault behavior. Invalid binary words have no counterpart in today's typed instruction type, so specify the decoder/error wrapper separately and prove that legal encoded programs preserve the existing semantics. Include halt, disabled capture, and minimum/maximum duration cases. Convert checked external integers to bounded values explicitly; do not use modular conversion as input validation.

Select explicit bit encodings for execution state and signals. Document reset polarity and synchrony, accepted-start timing, result lifetime, and behavior for unused control encodings. Define initialization: which registers reset, whether a program has been committed, and when execution may begin. Reset must not be assumed to initialize an arbitrary memory macro or erase a committed program.

For the first core, evaluate a small register-backed instruction store with combinational read and clocked writes. This exposes the simplest path for entering consecutive one-cycle actions. Record the complete read/decode/register-update path. A synchronous memory alternative must specify first-instruction availability, fetch latency, and any buffering before adoption. Neither choice comes with a proven clock frequency yet.

**Exit evidence:** a checked encoding/decoding contract, raw-word rejection checks, an explicit state/port/reset contract, and a clock-edge schedule for start, consecutive one-cycle actions, halt, and end-of-memory fault. Preserve the existing abstract engine tests.

## Milestone 2: a small circuit language and a complete vertical slice

Define only the circuit primitives needed by the first core: fixed-width constants and signals, bit selection/concatenation, Boolean logic, comparisons, multiplexers, bounded arithmetic, and clocked registers with defined reset/enables. Keep combinational dependencies acyclic. Introduce memory ports with explicit semantics when implementing the store. Avoid a general Lean-to-hardware compiler or a custom MLIR dialect.

Give these structures an executable Lean semantics. Prove primitive behavior at the declared widths, including wraparound and reset priority. Specify how all next-register values are calculated from the same pre-edge state and input snapshot, then installed simultaneously. A bounded value such as `Fin 256` in the reference model still needs a correspondence to an actual eight-bit register and its operations.

Build the first circuit slice: an eight-bit duration register, load/decrement selection, zero detection, and the action-boundary pulse. Prove it implements the existing countdown convention, including duration one and 256. Then emit this slice through the candidate CIRCT path, simulate its generated RTL, and perform an initial synthesis. Pin tool versions and record generated artifact identities in the development record.

**Exit evidence:** checked circuit semantics and slice correspondence, accepted generated RTL, matching independent reset/load/countdown traces, and a synthesis report. This tests the hardware route early, before investing in full-processor proofs. A failed backend or cost check is a reason to revise the implementation approach while the circuit is still small.

## Milestone 3: implement and prove the execution core

Construct the instruction store/read path, decoder, program counter, countdown, output registers, eight receive registers, and status logic using the circuit primitives. Make instruction fetch and decode part of the modeled circuit. Prove address bounds, correct instruction selection, timer behavior, capture destination/retention, and defined halt/fault handling.

Define the concrete-to-abstract state relation and prove the one-edge execution theorem. Include reset priority, starts ignored while busy, completion-edge behavior, and input capture from the specified edge. Derive trace and result correspondence, then compose it with the existing compiler proofs to recover UART and SPI correctness for the concrete core.

Check the hardest timing cases early: consecutive one-cycle actions, an entry capture on each of those boundaries, overwriting a receive slot, halt in slot zero, halt in the final slot, and fall-through from the final slot. An instruction-memory access is not an instantaneous abstract function unless the chosen circuit and clock assumptions justify it.

**Exit evidence:** whole-core refinement for legal encoded programs and arbitrary input histories, defined behavior for malformed words, audited theorem assumptions, and generated-core simulations against the independent protocol and mixed-action contracts. Synthesize this core before extending the instruction set.

## Milestone 4: connect proofs to emitted RTL and mapped gates

Record exactly what the Lean theorem covers: the semantics of a particular circuit structure. Generating Verilog from that structure does not automatically extend the proof to emitted text or downstream transformations.

For each emitted operation, document the correspondence between Lean circuit semantics and the selected CIRCT operations. Validate widths, reset behavior, clock enables, input sampling, and memory read/write behavior. Keep the emitter small and deterministic. Use independent RTL tests and deliberate faulty fixtures to check that the validation catches wrong reset priority, off-by-one duration, and wrong capture edges.

State the remaining trust boundary explicitly. A checked lowering proof or a validated interpretation of the generated artifact would support a stronger claim than matching simulations. An independently expressed reference RTL and a formal equivalence check can add evidence, but must have its own justified connection to the Lean model; two outputs of the same faulty emitter are not independent validation.

Evaluate an RTL-to-mapped-netlist equivalence check using a suitable formal hardware tool, such as [EQY](https://yosyshq.readthedocs.io/projects/eqy/en/latest/). Pin the configuration, assumptions, reset/initial-state treatment, memory treatment, and comparison endpoints. Its result is separate tool evidence, not automatically a Lean-checked theorem. Do not treat black-boxed logic as proved. Address the relationship between Lean's two-valued digital semantics and uninitialized or unknown states in RTL tools.

**Exit evidence:** identified Lean circuit and RTL artifacts, recorded translation validation, a stated trusted-tool boundary, passing independent RTL tests, and an equivalence result for the chosen supported endpoints or an explicit unresolved gap. Report simulation as simulation when equivalence has not been established.

## Milestone 5: implement real loading and external interfaces

Today's load operation replaces the complete program and idle profile atomically. A chip will receive writes over a concrete interface. Define accepted commands, response/status, address/data widths, reset behavior, and priority among writes, commit, and start. Begin at synchronous core ports; select a serialized transport and package-pin mapping only after checking the available I/O budget.

The baseline to evaluate is staged program writes followed by an atomic commit. Ordinary staging writes preserve the previous committed program and its observable state; successful commit applies the new idle profile and clears execution/results exactly as the abstract load does. Define incomplete uploads, rejected commands, loading from fault, reset during upload, and whether a start during staging is accepted or rejected. Reset retains the committed program while applying the defined reset state; starts must never execute a partially uploaded program. Busy writes/commit must not mutate the executing program. Account for all staging storage: preserving an old program while receiving a new one may require two banks or an equivalent buffer. A cheaper in-place loader would need an explicit revised contract, not an implicit loss of atomicity.

Prove accepted commits correspond to abstract loads and intermediate loading steps have the specified observable behavior. Define the clock-domain and input-observation boundary. If synchronization or buffering introduces latency, model it and relate protocol timing assumptions to the physical pins; do not silently reinterpret the sample times already proved.

**Exit evidence:** interface/refinement proofs, interrupted-upload/reset/conflicting-command tests, and UART → SPI → UART on one generated RTL design with changed instruction contents and no regeneration. Record the actual I/O and storage costs.

## Milestone 6: demonstrate physical feasibility and review flexibility

Adopt a pinned competition-compatible Tiny Tapeout template and verify that its flow supports the announced allocation. Recheck the template-size discrepancy recorded in the competition brief. Integrate the exact generated RTL and explicit source list, clock/reset/I/O constraints, and loading interface.

Run technology-mapped synthesis and the place-and-route flow. Record memory implementation, mapped area, clock-tree/routing overhead, constrained timing paths, I/O delays, and required physical-rule checks. Choose and justify the clock and operating assumptions. A four-cycle proof establishes four cycles; it does not establish their duration in nanoseconds or external electrical compliance. Area fit is a result of the implementation flow, not of the number of Lean definitions or instruction slots.

Do not postpone the competition's flexibility question until tapeout. Alongside this baseline, use separate bounded experiments for reusable payload data and input-dependent progress, then the desired I²C subset. Let those experiments motivate additional instructions and line-control semantics. Every extension must update the abstract contract, compilers, concrete refinement, and hardware evidence as applicable. The first fixed-schedule core is a baseline, not a declaration that the final architecture is general-purpose enough.

**Exit evidence:** reproducible physical-flow reports for an identified design, explicit supported timing/I/O limits, and a review of demonstrated programmability versus remaining protocol requirements. Routed timing, process-rule checks, and eventual silicon testing remain different evidence from the Lean functional proofs.

## Execution order and completion criteria

Start with milestones 1 and 2 as the next bounded implementation batch: encoding, core contract, circuit semantics, and a generated/simulated/synthesized countdown slice. This documentation update does not install tools or begin those implementations. Continue to the complete core once that vertical slice establishes a viable route. Begin translation validation with the slice and repeat it for the core and loading interface; the numbered milestones are acceptance boundaries rather than a reason to delay early feedback.

For each batch, preserve the current reference models, run relevant Lean proofs and executable checks, inspect axiom dependencies, record counterexamples and unresolved assumptions, and commit validated increments. Keep generated artifacts under ignored `build/`; retain reproducible source/configuration and concise evidence records in version control. Do not replace an unresolved proof boundary with a blanket claim that the chip is verified.

File ownership belongs to [architecture.md](architecture.md#proposed-repository-structure). Create circuit/encoding/refinement modules as their milestones begin, without empty scaffolding. Append verified tools and reproduction commands to [development.md](development.md) when hardware integration starts.

Primary implementation references: [CIRCT hardware representation](https://circt.llvm.org/docs/Dialects/HW/RationaleHW/), [sequential operations](https://circt.llvm.org/docs/Dialects/Seq/), [Verilog generation](https://circt.llvm.org/docs/VerilogGeneration/), and [EQY equivalence checking](https://yosyshq.readthedocs.io/projects/eqy/en/latest/). These are candidate tools and live documentation; validate compatible pinned revisions during the implementation milestone.
