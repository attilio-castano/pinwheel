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
9. [The processor verification plan](docs/processor-verification.md) for the staged path to a complete core and physical feasibility.
10. [The hardware baseline](docs/hardware-baseline.md) for the implemented instruction encoding and selected core contract.
11. [The countdown hardware record](docs/countdown-hardware.md) for the first proved circuit, generated RTL, simulation, and synthesis evidence.

Pinwheel centers on Lean specifications, executable machine models, and proofs that connect protocol behavior to a programmable engine. Fixed UART and SPI models establish concrete contracts. A shared Lean engine now runs both as reloadable timed-action programs, with compiler correctness proofs against those contracts.

The first hardware slice now works end to end: a structural countdown circuit described in Lean, proved against the engine's timing convention, emitted through CIRCT to SystemVerilog, simulated, and synthesized. Lean and RTL matched on 38,026 clock edges; synthesis produced 38 generic cells, including nine register bits. The canonical 16-bit instruction encoding also has round-trip and raw-execution correspondence proofs.

The next hardware objective is the complete execution core: instruction memory, decoder, program counter, pin updates, capture, and status logic around the proved timer. The [staged processor plan](docs/processor-verification.md) then covers translation/equivalence checks, physical loading, and physical feasibility. The emitter and CIRCT have simulation evidence; semantics preservation through translation has not been proved. Generic synthesis establishes neither competition area fit nor operating frequency.

The pure Lean UART transmitter, mode-0 SPI controller, programmable engine, compilers, binary encoding, and countdown circuit are implemented. Programs still embed outgoing payload bits. Payload registers, reactive control flow, a complete processor circuit, physical loading, and broader protocol support remain future work.

The package pins Lean 4.33.1 and uses bundled libraries only. Run `lake build` to check the proofs. Run `lake env lean -DwarningAsError=true --run test/Engine.lean` for both compiled protocols, general engine checks, and reloadability. The equivalent commands for `test/UART.lean` and `test/SPI.lean` exercise the fixed reference models. All three suites write CSV traces under `build/`. Those three suites exercise the Lean protocol/engine models; the hardware runner below exercises the generated countdown circuit.

Run `python3 scripts/install-hardware-tools.py` once for the pinned Apple Silicon tools, then `python3 scripts/check-hardware.py` to reproduce the encoding/circuit checks, axiom audit, RTL simulations, negative fixtures, and generic synthesis. The [hardware record](docs/countdown-hardware.md) explains timing conventions and artifact identities.
