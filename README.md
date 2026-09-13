# Pinwheel

An early-stage project exploring an entry in Jane Street's protocol emulator ASIC competition.

Start with:

1. [The competition brief](docs/competition.md) for official constraints and primary sources.
2. [The architecture plan](docs/architecture.md) for Lean's role, proof boundaries, and the proposed repository structure.
3. [The UART experiment plan](docs/uart-experiment.md) for the first milestones and acceptance criteria.
4. [Development setup](docs/development.md) for the pinned Lean toolchain and terminal build commands.
5. [The pure Lean UART experiment](docs/uart-model.md) for its interface, proved claims, and runnable trace.

Pinwheel centers on Lean specifications, executable machine models, and proofs that connect protocol behavior to a programmable engine. The first planned experiment is a simulation-only UART transmitter, followed by reloadable timed pin-action programs in the same simulated engine.

The proposed implementation path is Lean-generated hardware MLIR through CIRCT to Verilog, followed by RTL simulation and synthesis. This integration has not been validated. Proofs about a Lean model do not by themselves establish correctness of the generated RTL or physical chip.

The pure Lean UART specification and finite-state model are implemented, with proofs of waveform correctness, exact busy timing, and interface behavior. RTL generation, simulation, and synthesis remain pending. The full competition architecture and broader protocol scope remain open.

The package pins Lean 4.33.1 and uses bundled libraries only. Run `lake build` to check the proofs and `lake env lean -DwarningAsError=true --run test/UART.lean` to exercise the model and write a CSV pin trace. This is a Lean model, not a generated or physical circuit.
