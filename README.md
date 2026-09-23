# Pinwheel

An experiment in learning chip design through mathematics, formal verification,
and AI-assisted development.

I started this project as a former mathematician with no experience designing
hardware. The question is whether Lean and modern AI tools can make the journey
from an abstract specification to a working chip more understandable—and make
the iteration and testing loop shorter and more reliable.

The concrete project is a programmable protocol engine: a chip that can be
reloaded with programs for communicating through its pins. UART, SPI, and I²C
provide practical examples of timed outputs, input capture, and conditional
execution. [Jane Street’s chip-design competition](docs/competition.md) supplies
inspiration and useful constraints. The broader goal is to learn what designing
a chip entails and document what these tools help with, where they fall short,
and what the process teaches us.

## Making hardware feel closer to mathematics

The approach is to make assumptions explicit, describe behavior precisely, and
build implementations through small, checkable steps. Lean gives us a place to
state models and prove relationships between them. AI tools help explore ideas,
write code and proofs, investigate failures, and interpret experiments. Their
suggestions still need evidence from proof checking, independent tests, and
hardware measurements.

For example, transmitting a UART byte connects several kinds of reasoning:

1. Specify the bit sequence and when each bit should appear at the output pin.
2. Compile it into an engine program and prove that the modeled execution
   produces the specified trace under explicit assumptions.
3. Emit a structural circuit through CIRCT to SystemVerilog, test it independently,
   and measure whether its physical implementation can meet timing and electrical
   constraints.

A correct abstract machine still has to become wires, clocks, and transistors.
Lean can catch some mistakes before expensive hardware runs; placement and
routing expose costs that the behavioral model does not capture. An important
part of the experiment is feeding those discoveries back into better interfaces,
assumptions, and checks.

Whether this approach makes the overall process faster or easier is a question
the project is exploring. Failed experiments and the limits of each result are
part of the record.

## Where things stand

Pinwheel has executable protocol models, Lean proofs for parts of the engine and
its protocol behavior, emitted circuits, and independent simulation checks.
The [UART link proof](docs/uart-link.md), for example, connects transmitted bytes
to received bytes under explicit clock and observation-delay bounds.

Physical experiments have reached placement and routing. Whole-chip timing,
electrical limits, and routing closure remain open. A Lean model proof, an RTL
test, a physical measurement, and a result from silicon establish different
things; the project keeps those evidence boundaries explicit.

The [research status](docs/research/status.md) tracks the current question and
next decision. Detailed measurements and historical milestones live in the
[results](docs/research/results.md) and [journal](docs/research/journal.md).

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
