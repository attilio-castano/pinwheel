# Pinwheel

A Lean-centered exploration of a programmable protocol-emulator ASIC for
[Jane Street's competition](docs/competition.md).

UART, SPI, and I²C motivate a shared engine for timed pin updates, input capture,
and conditional execution. Lean specifies the behavior and proves correspondence
between protocol models and machine implementations. Structural circuits lower
through CIRCT to SystemVerilog for independent simulation and hardware measurement.

The project has a general reloadable core with atomic program replacement,
compressed instruction storage, and a current-instruction cache. Its first physical
implementation exposed a slow-corner timing failure. The project has not established
qualified operating frequency or full submission fit. Lean model proofs, RTL checks,
and physical evidence have distinct boundaries.

## Start here

- [Current research status](docs/research/status.md): the active question, evidence, and next decision.
- [Research results](docs/research/results.md): completed conclusions and conditions for reconsidering them.
- [Research journal](docs/research/journal.md): dated milestones and evidence locations.
- [Research workflow](docs/research/README.md): how experiments and outside research become durable knowledge.
- [Technical documentation](docs/README.md): protocol models, architecture, proofs, storage studies, and physical reports.
- [Development setup](docs/development.md): installation, pinned tools, and reproduction commands.

## Build

The repository pins Lean 4.33.1 and uses bundled Lean libraries. With the toolchain
installed, check the library and run the shared UART/SPI engine examples:

```sh
lake build
lake env lean -DwarningAsError=true --run test/Engine.lean
```

Hardware checks additionally require the pinned tools and prerequisite artifacts
described in the relevant study. Generated evidence lives under ignored `build/`;
source, tests, concise research records, and selected result manifests are tracked.
