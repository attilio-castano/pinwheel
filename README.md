# Pinwheel

A Lean-centered exploration of a programmable protocol-emulator ASIC for
[Jane Street's competition](docs/competition.md).

UART, SPI, and I²C motivate a shared engine for timed pin updates, input capture,
and conditional execution. Lean specifies the behavior and proves correspondence
between protocol models and machine implementations. Structural circuits lower
through CIRCT to SystemVerilog for independent simulation and hardware measurement.

[UART reception](docs/uart-receive.md) now supports one 8N1 byte with start
confirmation and framing-error reporting, compiled for the same reloadable engine.
The [UART link proof](docs/uart-link.md) connects transmitted bytes to received
bytes under explicit clock and digital observation-delay bounds.
The [continuous receive model](docs/uart-stream.md) adds automatic rearm, a
one-entry result buffer, explicit consumption/overrun, and proofs for finite
ideal back-to-back frames through a compiled-program supervisor.
The [continuous clock contract](docs/uart-stream-clocks.md) extends those proofs
to unequal TX/RX clocks and varying bounded observation age, including time to
rearm and observe idle high between adjacent frames.

The project has a reloadable core with atomic program replacement, compressed
instruction storage, and proved alternatives for fetching instructions. The
one-port experimental core meets extracted setup and hold at all three corners
of one 20 ns routed run on the 6×4 die area; electrical-limit violations remain.
The [whole chip](docs/whole-chip.md) adds a proved serial loader and Tiny Tapeout
pin map, and has been emitted and mapped, but has no independent RTL check or
routed result. Its interface has no host result-readback transaction, and
the compiled UART receiver does not satisfy the one-port program rule.
The [submission plan](docs/submission-plan.md) records those remaining gates.
No backend is promoted to the default, and full submission fit is unestablished.
Lean model proofs, RTL checks, and physical evidence have distinct boundaries.

## Start here

- [Current research status](docs/research/status.md): the active question, evidence, and next decision.
- [Submission plan](docs/submission-plan.md): remaining functionality, tool changes, dependencies, and completion gates.
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

Run the local pre-push checks (Python 3.12+, no CAD tools or pre-existing fixtures):

```sh
python3 -B -m unittest discover -s test -p 'test_*.py'
python3 scripts/check-foundation.py --tag first-check
```

Use a fresh tag on later runs. The [validation guide](docs/validation.md) explains
the validation scope, hardware prerequisites, and evidence boundaries.

Hardware checks additionally require the pinned tools and prerequisite artifacts
described in the relevant study. Generated evidence lives under ignored `build/`;
source, tests, concise research records, and selected result manifests are tracked.
