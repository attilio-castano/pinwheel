# Pinwheel

An early-stage project exploring an entry in Jane Street's protocol emulator ASIC competition.

Start with:

1. [The competition brief](docs/competition.md) for official constraints and primary sources.
2. [The architecture plan](docs/architecture.md) for Lean's role, proof boundaries, and the proposed repository structure.
3. [The UART experiment plan](docs/uart-experiment.md) for the first milestones and acceptance criteria.

Pinwheel centers on Lean specifications, executable machine models, and proofs that connect protocol behavior to a programmable engine. The first planned experiment is a simulation-only UART transmitter, followed by reloadable timed pin-action programs in the same simulated engine.

The proposed implementation path is Lean-generated hardware MLIR through CIRCT to Verilog, followed by RTL simulation and synthesis. This integration has not been validated. Proofs about a Lean model do not by themselves establish correctness of the generated RTL or physical chip.

Implementation is on hold while planning continues. The full competition architecture and broader protocol scope remain open; more project context will follow from the maintainers.

Documentation lives in `docs/`. The unused Python package scaffold has been removed. No Lean source, experiment implementation, dependencies, or toolchain configuration exists yet; create them only when the corresponding implementation milestone is authorized.
