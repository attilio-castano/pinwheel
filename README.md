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
9. [The processor verification plan](docs/processor-verification.md) for building and proving a concrete register/logic implementation, then checking RTL and physical feasibility.

Pinwheel centers on Lean specifications, executable machine models, and proofs that connect protocol behavior to a programmable engine. Fixed UART and SPI models establish concrete contracts. A shared Lean engine now runs both as reloadable timed-action programs, with compiler correctness proofs against those contracts.

Our next hardware objective is to describe the processor's registers, decoder, logic, and memory in Lean and prove that their clock-by-clock behavior implements the existing engine. That would connect circuit execution to the UART/SPI contracts through the compiler proofs we already have.

The [staged processor plan](docs/processor-verification.md) starts with instruction encoding and a small, proved countdown circuit carried through RTL generation, simulation, and synthesis. It then covers the whole execution core, translation/equivalence checks, a real loading interface, and physical feasibility. The proposed backend remains hardware MLIR through CIRCT to Verilog; this integration is unvalidated. Formal digital correctness, generated-artifact correspondence, and physical area/timing are separate evidence requirements.

The pure Lean UART transmitter, mode-0 SPI controller, bounded programmable engine, and both protocol compilers are implemented. Proofs cover waveform correctness, timing, input capture, receive results, and the defined interfaces. Programs currently embed outgoing payload bits; binary instruction encoding, payload registers, reactive control flow, RTL generation, RTL simulation, and synthesis remain pending. The full competition architecture and broader protocol scope remain open.

The package pins Lean 4.33.1 and uses bundled libraries only. Run `lake build` to check the proofs. Run `lake env lean -DwarningAsError=true --run test/Engine.lean` for both compiled protocols, general engine checks, and reloadability. The equivalent commands for `test/UART.lean` and `test/SPI.lean` exercise the fixed reference models. All three suites write CSV traces under `build/`. These are Lean models, not generated or physical circuits.
