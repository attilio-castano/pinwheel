# First experiment: UART specified and modeled in Lean

Planning record: **2026-09-12**.

Status: proposed experiment, recorded for future contributors and agents. As of **2026-09-13**, the minimal Lean package and toolchain setup are authorized, with a separate bitvector setup example. No UART implementation, protocol proofs, circuit simulation, or synthesis results exist yet. UART and hardware implementation remain on hold while planning continues. Commit completed, verified changes when work is authorized.

## Objective and scope

Specify UART behavior in Lean, prove a finite-state transmitter meets that contract, and validate a corresponding generated circuit. Then make its behavior reloadable through timed pin-action programs. See the [competition brief](competition.md) for external requirements and the [architecture plan](architecture.md) for tool roles, proof boundaries, and the proposed file structure.

The first experiment is **simulation only**: one output pin, one clock, and UART transmission with eight data bits, no parity, and one stop bit (8N1). Physical FPGA testing, board purchases, ASIC deployment, additional protocols, and a general-purpose programming language are outside this first pass.

## Stage 1: fixed UART transmitter

### Specify and model

Before coding, define the clock/reset convention, byte/start handshake, bit duration, busy/completion behavior, and output changes relative to clock edges. Begin with a positive integer number of clock cycles per bit; choose finite counter bounds and supported parameter ranges explicitly. Actual frequency remains open.

Define the UART output trace independently of the transmitter implementation. Model the implementation in Lean using bounded state for its clock counter, shift register, and idle/start/data/stop control. "Fixed" describes its UART behavior; it accepts a byte so all values can be checked.

Proof acceptance:

- For every byte and supported bit duration, an accepted transmission produces the specified start bit, eight least-significant-bit-first data bits, and stop bit.
- Each bit lasts the specified number of cycles; the frame occupies ten bit intervals. Define any handshake latency separately.
- Idle-high behavior, completion timing, reset behavior, and repeated transmissions follow the stated interface contract.
- Counter and state invariants hold within the supported finite ranges.
- Claims have no unfinished proof placeholders; assumptions and axiom dependencies are recorded as described in the architecture plan.

### Generate and validate the circuit

The candidate path is Lean-generated hardware MLIR through CIRCT to Verilog. First validate a minimal circuit through CIRCT and the selected RTL simulator, then generate the UART circuit. Backend integration and model-to-RTL correspondence are separate from proving the Lean transmitter.

Implementation acceptance:

- CIRCT accepts the generated MLIR and exports RTL the selected simulator can compile.
- An independent UART checker decodes all 256 byte values correctly, including bit order and start/stop framing.
- Explicit cycle checks establish bit durations, frame length, idle-high behavior, and completion timing. Successful decoding alone is insufficient.
- RTL tests cover reset and repeated transmissions, with representative and boundary bit durations from the chosen range.
- A waveform from the generated circuit is available for inspection.
- Basic synthesis succeeds; inspect and record warnings and logic/resource counts before expanding the design.

The reference checker must reason from the UART contract rather than reuse the generator's state-transition or frame-assembly logic. Record what the simulation checks establish and what remains unproved about translation into RTL.

## Stage 2: reloadable timed pin actions

Define a small engine with writable instruction storage and operations provisionally equivalent to:

- Drive an output level for a specified positive number of cycles.
- Stop execution with defined output behavior.

Define instruction encoding, storage capacity, loading/start interface, reset, end-of-program behavior, and invalid-instruction handling before implementation. Initially permit loading while halted; concurrent modification is outside scope. Execution must account for fetch/decode so consecutive actions have their specified durations without accidental gaps, including consecutive one-cycle actions if supported.

A Lean compiler expands UART frames into encoded timed actions. Prove that executing a successfully compiled program under the engine semantics produces the specified UART trace, subject to supported duration and program-capacity bounds. Define rejection behavior for unsupported inputs. Loop and shift instructions are deferred until their benefit can be measured.

Acceptance evidence:

- The executable engine model and its invariants cover instruction execution, finite storage, and the documented loading/reset behavior.
- The UART compiler correctness proof connects the independent protocol contract to the engine semantics, including instruction encoding and decoding.
- The simulated RTL engine reproduces the UART framing and cycle checks from stage 1.
- Load program A, run it, halt, replace it with program B, and run again in the same simulated circuit instance. Do not regenerate hardware or recompile RTL between programs.
- Change the action pattern itself, including a simple non-UART waveform, to show more than UART byte/baud configuration.
- Check invalid instructions, program boundaries, reset, and the loading contract against their defined behavior.
- Preserve generated RTL identity and capture both programs and their output traces as evidence.
- The engine RTL passes basic synthesis; inspect and record warnings and logic/resource counts.

Basic synthesis does not prove IHP tile fit, routed timing, or tapeout readiness. Those require the process-specific flow later. Neither stage proves a physical pin was driven, and neither automatically proves that the generated RTL implements the Lean model.

## Setup and evidence

Follow the [architecture plan](architecture.md#proposed-repository-structure) for file placement and its [toolchain decisions](architecture.md#toolchain-decisions) for dependency selection. The Lean package setup is described in [development setup](development.md). Create protocol and hardware source files only as their milestone begins.

Once experiment implementation begins, extend the development record with assumptions, proof coverage, generated artifact identity, simulation results, and synthesis reports. Toolchain setup alone does not satisfy any UART acceptance criterion.

## Protocol source

- [Microchip UART frame formats](https://onlinedocs.microchip.com/oxy/GUID-173AD72D-41FE-4760-A93C-7078A02BD908-en-US-7.1.1/GUID-585072A2-2328-4EDD-B24F-E2E7672632B5.html): start/data/stop framing and bit order; linked in the original plan checked on 2026-09-12. This is a live reference, not an immutable snapshot.

Lean and CIRCT technical references are collected in the [architecture plan](architecture.md#primary-technical-sources).
