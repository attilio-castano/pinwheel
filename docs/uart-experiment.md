# First experiment: UART through Mojo, MLIR, and CIRCT

Planning record: **2026-09-12**.

Status: proposed implementation direction, recorded for future contributors and agents. No experiment code, dependencies, circuit simulation, or synthesis results exist yet. The user has explicitly kept implementation on hold while planning continues. This document is not authorization to install tools or begin implementation. Commit completed, verified changes when work is authorized.

Repository setup: the unused Python package scaffold has been removed in preparation for a Lean-centered plan. The experiment remains unimplemented; the proposed tool roles and layout below are pending revision.

## Objective and scope

Follow the organizer's suggested UART starting point with a small generated circuit, then make its behavior reloadable. See [the competition brief](competition.md) for the external requirements.

The user selected **simulation only**. The first experiment covers one output pin, one clock, and UART transmission with eight data bits, no parity, and one stop bit (8N1). Physical FPGA testing, board purchases, ASIC deployment, additional protocols, and a general-purpose programming language are outside this first pass.

Programmability comes from the engine's writable program storage, timing controls, and execution logic. MLIR helps describe and compile that hardware; using MLIR alone does not establish programmability.

## Tool roles and integration boundary

| Tool | Proposed role |
| --- | --- |
| Mojo | Generate hardware descriptions, assemble instruction programs, and implement an independent UART reference/checker. |
| MLIR | Explicit, inspectable representation of the circuit using existing CIRCT dialects. |
| CIRCT | Validate and transform hardware MLIR, then emit Verilog/SystemVerilog. |
| RTL simulator | Execute the generated circuit under clock, reset, and input stimulus; capture output-pin behavior. |
| Synthesis tool | Check that the generated RTL can be synthesized and inspect the resulting logic. |

The two paths are:

```text
Circuit:
Mojo generator -> hardware MLIR -> CIRCT -> Verilog -> simulated circuit

Program (stage 2):
Mojo assembler -> encoded instructions -> writable program memory in that circuit
```

Mojo will initially **emit ordinary MLIR text files**. CIRCT owns the interpretation of hardware operations such as modules/ports (`hw`), combinational logic (`comb`), and registers (`seq`). This path does not require those operations to be registered inside the Mojo compiler.

This is distinct from Mojo's inline MLIR feature. Inline MLIR invokes operations registered with Mojo's compiler; integrating a new dialect there would be a separate investigation. The first experiment does not require a custom protocol dialect, a C++ compiler extension, or a Mojo compiler fork.

The first protocol programs may simply be encoded instructions. A protocol-specific MLIR representation remains a later possibility, justified by concrete needs.

## Stage 1: fixed UART transmitter

Use Mojo to generate the hardware MLIR for a clock counter, shift register, and control states for idle, start, data, and stop. Compile through CIRCT and exercise the emitted RTL in a simulator. "Fixed" describes the circuit's UART behavior; it should accept a byte so validation can cover all values.

Before coding, specify the clock/reset convention, byte/start handshake, bit duration, busy/completion behavior, and when the output changes relative to a clock edge. Begin with an integer number of clock cycles per bit; actual frequency and supported counter range are still to be chosen.

Acceptance evidence:

- CIRCT accepts the generated MLIR and exports RTL that the selected simulator can compile.
- An independent UART checker decodes all 256 byte values correctly, including least-significant-bit-first ordering and start/stop framing.
- Explicit cycle checks establish each bit's duration, frame length, idle-high behavior, and completion timing. Successful decoding alone is insufficient.
- Reset and repeated transmissions behave according to the documented interface contract.
- A waveform from the generated circuit is available for inspection.

The reference checker must reason from the UART contract rather than reuse the generator's state-transition or frame-assembly logic.

## Stage 2: reloadable timed pin actions

Generate a small engine with writable instruction storage and operations provisionally equivalent to:

- Drive an output level for a specified positive number of cycles.
- Stop execution with defined output behavior.

Define the encoding, storage capacity, loading/start interface, reset behavior, end-of-program behavior, and handling of invalid instructions before implementation. Initially permit loading while halted; concurrent modification is outside the first scope. Execution must account for instruction fetch/decode so consecutive actions have their specified durations without accidental gaps.

A Mojo assembler expands UART frames into timed actions. Loop and shift instructions are deferred until their benefit can be measured.

Acceptance evidence:

- The simulated engine reproduces the UART framing and cycle checks from stage 1.
- Load program A, run it, halt, replace it with program B, and run again in the same simulated circuit instance. Do not regenerate hardware or recompile RTL between programs.
- Change the action pattern itself, including a simple non-UART waveform, to show more than UART byte/baud configuration.
- Preserve the generated RTL identity and capture both programs and their output traces as evidence.
- The generated RTL passes a basic synthesis check; inspect and record warnings and logic/resource counts.

Basic synthesis is a feasibility check, not proof of IHP tile fit, routed timing, or tapeout readiness. Those require the process-specific flow later. Neither stage proves a physical pin was driven.

## Proposed repository layout

Create files as their stage begins; this tree is a plan, not existing implementation. Supporting build and test configuration will accompany the code that needs it.

```text
README.md
pyproject.toml                    # Mojo dependency configuration
uv.lock                           # Resolved dependency versions
.gitignore
Makefile                          # Generate, simulate, and check commands
docs/
  competition.md
  uart-experiment.md
  development.md                 # Verified setup and commands, once established
src/
  hardware/
    fixed_uart.mojo              # Stage 1 circuit generator
    action_engine.mojo           # Stage 2 circuit generator
  mlir_text.mojo                  # Hardware MLIR emission helpers
  uart_program.mojo               # Stage 2 instruction assembler
  uart_reference.mojo             # Independent UART behavior/checking
examples/
  uart_tx.mojo                    # Generate an example instruction program
tests/
  fixed_uart_tb.sv                # Stage 1 RTL stimulus and capture
  action_engine_tb.sv             # Stage 2 loading/replacement test
  check_uart.mojo                 # Check captured pin values and cycle counts
build/                            # Ignored generated IR, RTL, traces, reports
```

The Tiny Tapeout template is not adopted yet. Its source-file configuration and the placement of generated RTL must be reconciled when it is integrated.

## Dependency decisions still open

Select and verify a compatible Mojo release, CIRCT distribution/revision, RTL simulator, and synthesis tool. Use CIRCT's compatible MLIR version rather than assume that an independently installed LLVM package will match. No exact versions or installation commands are approved by this plan.

Use a project-local Mojo environment with a committed lockfile. Record actual versions and reproducible commands in `development.md` after verification. The first integration check should be a minimal generated circuit accepted by CIRCT and the RTL simulator, before attempting the full UART.

## Primary technical sources

Checked on 2026-09-12; these are live documentation links, not immutable snapshots.

- [CIRCT hardware representation](https://circt.llvm.org/docs/Dialects/HW/RationaleHW/): modules, ports, and the relationship between hardware dialects.
- [CIRCT sequential operations](https://circt.llvm.org/docs/Dialects/Seq/): clocked state and register operations.
- [CIRCT Verilog generation](https://circt.llvm.org/docs/VerilogGeneration/): RTL export infrastructure.
- [CIRCT setup](https://circt.llvm.org/docs/GettingStarted/): toolchain setup and its relationship to LLVM/MLIR revisions.
- [Mojo inline MLIR reference](https://mojolang.org/docs/reference/inline-mlir/): direct access to registered operations; relevant to understanding the separate inline integration path.
- [Microchip UART frame formats](https://onlinedocs.microchip.com/oxy/GUID-173AD72D-41FE-4760-A93C-7078A02BD908-en-US-7.1.1/GUID-585072A2-2328-4EDD-B24F-E2E7672632B5.html): reference for start/data/stop framing and bit order.
