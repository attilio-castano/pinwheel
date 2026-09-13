# Pinwheel

An early-stage project exploring an entry in Jane Street's protocol emulator ASIC competition.

Start with:

1. [The competition brief](docs/competition.md) for official constraints and primary sources.
2. [The architecture plan](docs/architecture.md) for Lean's role, proof boundaries, and the proposed repository structure.
3. [The UART experiment plan](docs/uart-experiment.md) for the first milestones and acceptance criteria.
4. [Development setup](docs/development.md) for the pinned Lean toolchain and terminal build commands.
5. [The pure Lean UART experiment](docs/uart-model.md) for its interface, proved claims, and runnable trace.
6. [The pure Lean SPI experiment](docs/spi-model.md) for full-duplex sampling, timing proofs, and runnable checks.
7. [The shared-engine design](docs/shared-engine.md) for requirements learned from both protocols.
8. [The implemented engine](docs/engine-model.md) for typed programs, timing proofs, compiler correctness, and reloadability evidence.
9. [The processor verification plan](docs/processor-verification.md) for milestone status and the remaining path to physical feasibility.
10. [The hardware baseline](docs/hardware-baseline.md) for the implemented instruction encoding and core contract.
11. [The countdown hardware record](docs/countdown-hardware.md) for the first circuit slice.
12. [The execution-core record](docs/core-hardware.md) for complete-core proofs, reloadable RTL, independent checks, and synthesis evidence.
13. [The pure Lean I²C experiment](docs/i2c-model.md) for open-drain writes, ACK/NACK, stretching, and the next engine extensions.
14. [The candidate reactive engine](docs/reactive-engine.md) for proved legacy compatibility, selected-input waits, and a programmable stretched pulse.
15. [Compiled I²C](docs/compiled-i2c.md) for guarded timing, ACK branches, complete write programs, and compiler correspondence proofs.

Pinwheel centers on Lean specifications, executable machine models, and proofs that connect protocol behavior to a programmable engine. Fixed UART and SPI models establish concrete contracts. A shared Lean engine now runs both as reloadable timed-action programs, with compiler correctness proofs against those contracts.

The complete execution core is now described structurally in Lean and proved to implement the engine: a 32×16 instruction store, decoder, scheduler, timer, pin registers, and input capture. Composed proofs recover UART/SPI waveform correctness and SPI receive correctness for the concrete core.

The same generated SystemVerilog runs both protocols through internal atomic program commits. Lean and RTL matched on **71,703 clock edges**, including **1,032 UART/SPI transfers**. The standalone decoder passed all **65,536** input words. Three faulty RTL variants were rejected, and generic synthesis produced **1,907 cells**, including **543 register bits**. See the [core record](docs/core-hardware.md) for coverage and artifact identities.

These results establish digital circuit-model correctness and measured RTL behavior. The emitter and CIRCT transformations have not been proved correct; generic synthesis establishes neither competition area fit nor operating frequency. Translation/equivalence evidence and a physical program-loading interface remain open. Programs still embed payload bits; reusable payloads, reactive control flow, line release, and broader protocol support remain future work for the shared core.

A separate pure Lean I²C reference controller writes an address and one byte over an ideal open-drain bus, handles ACK/NACK, and waits through clock stretching. Its 19 audited theorems cover bus behavior and controller timing; 4,224 closed-loop transactions and three rejected faulty variants provide executable evidence. See the [I²C record](docs/i2c-model.md) for scope and proof boundaries; reproduce with `python3 scripts/check-i2c.py`, using only Lean and Python.

A candidate Lean engine separates drive commands from two observed inputs and supports waits, guarded timing, terminal capture, conditional branches, and input qualification. Its 38 audited theorems retain legacy compatibility and establish the general operations. Checks pass 1,024 stretched pulses and 1,024 UART/SPI transfers; reproduce with `python3 scripts/check-reactive.py`.

I²C now runs as a 79-instruction program on that candidate engine. Compiler proofs establish identical pin commands, busy status, and results to the reference for arbitrary sampled input histories during a run. The compiled suite passes 4,224 transactions, fault injections, three corrupted programs, and UART → SPI → I²C → UART reload. See [compiled I²C](docs/compiled-i2c.md) for the 29-theorem audit, reset boundary, and experimental 128-slot bank; reproduce with `python3 scripts/check-compiled-i2c.py`. The encoded hardware still implements the original UART/SPI engine. Storage/encoding selection and a corresponding extended circuit remain ahead.

The package pins Lean 4.33.1 and uses bundled libraries only. Run `lake build` to check the proofs. Run `lake env lean -DwarningAsError=true --run test/Engine.lean` for compiled protocols and the reference engine's boundary/reload cases. The equivalent commands for `test/UART.lean` and `test/SPI.lean` exercise the fixed reference models. These suites write CSV traces under `build/`.

Run `python3 scripts/install-hardware-tools.py` once for the pinned Apple Silicon tools, then `python3 scripts/check-core.py` to reproduce the complete-core proofs, axiom audit, independent traces, RTL simulations, fault injections, and generic synthesis. `python3 scripts/check-hardware.py` reproduces the separate countdown/encoding experiment. See [development setup](docs/development.md) for commands and requirements.
