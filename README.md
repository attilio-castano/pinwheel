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

Pinwheel has executable protocol models, emitted circuits, and independent
simulation checks. For the paired SRAM design, Lean proofs now connect a
certified program upload to cycle-by-cycle execution and package observations.
An [interpretation of the retained RTL](docs/storage/paired-rtl-interpretation.md)
connects both emitted modules to those proofs. The SRAM behavior, digital input
delivery, and artifact interpretation assumptions remain explicit.

The retained chip has completed routing and passes the recorded timing,
electrical, full-rule GDS design-rule, and SRAM boundary checks. **It is not yet
a qualified chip:** SRAM internal qualification, compatible fast timing
conditions, and package power remain [tracked requirements](docs/physical/qualification-followups.md).
The measured area is 4.5942% above the historical allowance. The 64-record
capacity experiment and complete design iteration remain unaccepted.

The [acceptance report](docs/research/implementation-acceptance.md) connects the
proofs and physical evidence without treating one kind of check as another.
Portable validation works from source; replaying the physical evidence still
requires the retained local artifacts and pinned tools.

The [current-A replay workflow](docs/research/current-a-replay.md) inventories and
recovers those dependencies into a movable snapshot with their original hashes.
[Fresh-source RTL interpretation](docs/storage/paired-rtl-interpretation.md#reproduce-and-inspect)
checks new emission without old experiment outputs. The
[package-power request](docs/physical/package-power-contract.md) identifies the
integration inputs and activity evidence needed for the next physical decision.

The current [protocol continuation](docs/research/established-protocol-continuation.md)
delivers SPI modes 0–3, one/two-byte transfers, bounded I²C writes and bus clear,
with separate physical input/output pads and resolved-wire checks. The I²C
programs reuse the SPI circuitry. An opt-in [UART receive supervisor](docs/protocols/uart-supervisor.md)
adds automatic rearm and explicit retained-result/drop ownership. Retained
physical results keep their original source identity.

The [research status](docs/research/status.md) tracks the current question and
next decision. Detailed measurements and historical milestones live in the
[results](docs/research/results.md) and [journal](docs/research/journal.md).

## Find your way around

To resume an experiment, start at [research status](docs/research/status.md) for
the active decision. Use the [technical topic map](docs/README.md) to find the
relevant contract or study, then follow its [result](docs/research/results.md),
manifest, and reproduction steps. The [journal](docs/research/journal.md) records
dated milestones; a next-step statement in an older study is historical context.

| I want to... | Start here |
| --- | --- |
| Try the programmable chip | [Host workflow](docs/host-workflow.md): load UART TX/RX, SPI, I²C, and a custom trigger into one unchanged RTL chip, then retrieve results. |
| Understand a topic quickly | [Technical documentation](docs/README.md): short lessons and paths to the owning studies. |
| See what has been learned | [Research results](docs/research/results.md): conclusions, limits, and reasons to reopen them. |
| Check completion criteria | [Submission plan](docs/submission-plan.md): a dated implementation sequence and durable acceptance gates; use research status for current priority. |
| Reproduce or extend work | [Development setup](docs/development.md), [validation](docs/validation.md), and the [research workflow](docs/research/README.md). |
| Find experiment inputs and records | [Physical inputs](physical/README.md) and [experiment records](physical/experiments/README.md): tracked configurations, selections, and result manifests. |
| Find a checker or flow command | [Script index](scripts/README.md): entry points and the evidence each can establish. |

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
