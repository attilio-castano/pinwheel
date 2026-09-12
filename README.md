# Pinwheel

An early-stage project exploring an entry in Jane Street's protocol emulator ASIC competition.

Start with:

1. [The competition brief](docs/competition.md) for official constraints and primary sources.
2. [The UART experiment plan](docs/uart-experiment.md) for the proposed first implementation, tool roles, and success criteria.

We are planning a simulation-only experiment: Mojo generates hardware MLIR, CIRCT emits Verilog, and an RTL simulator checks a UART transmitter. A second stage introduces reloadable pin-action programs in the same simulated engine. This integration path has not been implemented or validated.

Implementation is on hold while planning continues. The full competition architecture and broader protocol scope remain open; more project context will follow from the maintainers.

Documentation lives in `docs/`. Implementation directories will be introduced when implementation begins.
