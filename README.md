# Pinwheel

An early-stage project exploring an entry in Jane Street's protocol emulator ASIC competition.

Start with:

1. [The competition brief](docs/competition.md) for official constraints and primary sources.
2. [The architecture plan](docs/architecture.md) for Lean's role, proof boundaries, and the proposed repository structure.
3. [The UART experiment plan](docs/uart-experiment.md) for the first milestones and acceptance criteria.
4. [Development setup](docs/development.md) for the pinned Lean toolchain and terminal build commands.
5. [The pure Lean UART experiment](docs/uart-model.md) for its interface, proved claims, and runnable trace.
6. [The pure Lean SPI experiment](docs/spi-model.md) for full-duplex sampling, timing proofs, and runnable checks.
7. [The shared-engine proposal](docs/shared-engine.md) for requirements learned from both protocols and the next implementation plan.

Pinwheel centers on Lean specifications, executable machine models, and proofs that connect protocol behavior to a programmable engine. Fixed UART and SPI models establish concrete contracts; the next proposed experiment runs both as reloadable programs on one Lean machine.

The proposed implementation path is Lean-generated hardware MLIR through CIRCT to Verilog, followed by RTL simulation and synthesis. This integration has not been validated. Proofs about a Lean model do not by themselves establish correctness of the generated RTL or physical chip.

The pure Lean UART transmitter and mode-0 SPI controller are implemented, with proofs of waveform correctness, exact busy timing, and interface behavior. SPI adds receive correctness for arbitrary input histories. The programmable engine, RTL generation, RTL simulation, and synthesis remain pending. The full competition architecture and broader protocol scope remain open.

The package pins Lean 4.33.1 and uses bundled libraries only. Run `lake build` to check the proofs. Run `lake env lean -DwarningAsError=true --run test/UART.lean` and `lake env lean -DwarningAsError=true --run test/SPI.lean` to exercise both models and write CSV pin traces. These are Lean models, not generated or physical circuits.
