# Pinwheel

An early-stage project exploring an entry in Jane Street's protocol emulator ASIC competition.

The indexed reactive core now has a **proved atomic loader**: incomplete uploads preserve the old program, and commit switches instructions and metadata together. **41 audited loader theorems** extend the prior 55-theorem reactive-core foundation. Generated RTL runs UART, SPI, and I²C through the same host interface; see [the loader record](docs/atomic-loader.md).

Early CMOS5L mapping exposes the next constraint: the double-bank reference occupies **1.055 mm² of standard cells**, versus **0.550 mm²** for the prior single-image core. It exceeds the nominal competition area before placement/routing. The [cheaper-storage study](docs/storage-study.md) now combines a 32-entry dictionary, proved 55-bit record compression, and proved current-word caching; the combined RTL maps to **0.562 mm²** with an explicit capacity check; [the technology record](docs/technology-mapping.md) gives measurements and boundaries.

The completed study also measures a bounded two-byte I²C runtime-repetition machine at **0.192 mm²**, with separate payload bytes and 15 templates. It has narrower scope than the general candidate. The [SRAM/latch review](docs/storage-primitives.md) records real primitive costs and the timing contracts needed to use them.

The first [physical implementation](docs/physical-validation.md) routes the general core in a **6×4 diagnostic rectangle**, with **0.737 mm² of cells before filler insertion**, zero router/Magic DRC errors, zero antenna violations, and matching layout-versus-netlist checks. Its implemented netlist passes the functional regression. **50 MHz does not close:** extracted slow-corner setup misses by **6.254 ns**, with electrical-limit violations also remaining. The pinned competition flow lacks the announced 8×4 floorplan; this establishes neither submission fit nor a qualified operating frequency. Timing/electrical closure, external serial loading, and translation equivalence remain open.

The [successor-fetch experiments](docs/successor-fetch-study.md) reduce the routed slow-corner miss to **5.055 ns** with flow repair. Two proved speculative-read layouts pass RTL regression, but their mapping results do not justify additional routing yet. Targeted timing reports show nearly tied misses from loader data (**5.055 ns**) and protocol inputs (**4.928 ns**); timing and electrical closure remain open.

Start with:

1. [The competition brief](docs/competition.md) for official constraints and primary sources.
2. [The architecture plan](docs/architecture.md) for Lean's role, proof boundaries, and the proposed repository structure.
3. [The UART experiment plan](docs/uart-experiment.md) for the first milestones and acceptance criteria.
4. [Development setup](docs/development.md) for the pinned Lean toolchain and terminal build commands.
5. [The pure Lean UART experiment](docs/uart-model.md) for its interface, proved claims, and runnable trace.
6. [The pure Lean SPI experiment](docs/spi-model.md) for full-duplex sampling, timing proofs, and runnable checks.
7. [The shared-engine design](docs/shared-engine.md) for requirements learned from both protocols.
8. [The implemented engine](docs/engine-model.md) for typed programs, timing proofs, compiler correctness, and reloadability evidence.
9. [The processor verification plan](docs/processor-verification.md) for milestone status and the remaining path to physical feasibility.
10. [The hardware baseline](docs/hardware-baseline.md) for the implemented instruction encoding and core contract.
11. [The countdown hardware record](docs/countdown-hardware.md) for the first circuit slice.
12. [The execution-core record](docs/core-hardware.md) for complete-core proofs, reloadable RTL, independent checks, and synthesis evidence.
13. [The pure Lean I²C experiment](docs/i2c-model.md) for open-drain writes, ACK/NACK, stretching, and the next engine extensions.
14. [The candidate reactive engine](docs/reactive-engine.md) for proved legacy compatibility, selected-input waits, and a programmable stretched pulse.
15. [Compiled I²C](docs/compiled-i2c.md) for guarded timing, ACK branches, complete write programs, and compiler correspondence proofs.
16. [Reusable byte loops](docs/looped-i2c.md) for the 79-versus-15 storage comparison, cycle-preservation proofs, and remaining hardware costs.
17. [PWL binary images](docs/binary-images.md) for the version-0 format, encoder/decoder proofs, generated files, and exact byte accounting.
18. [Bounded I²C register reads](docs/i2c-register-read.md) for repeated START, received data, and the wider engine capacities.
19. [E64 execution records](docs/execution-records.md) for the selected layout and certified lowering.
20. [Decoder/store hardware](docs/execution-hardware.md) for the standalone frontend comparison.
21. [The integrated reactive core](docs/reactive-core-hardware.md) for fixed-program correspondence and the direct/indexed comparison.
22. [Atomic loading](docs/atomic-loader.md) for staging, validation, commit, initialization, proofs, and RTL checks.
23. [Early CMOS5L mapping](docs/technology-mapping.md) for measured area pressure.
24. [Cheaper storage](docs/storage-study.md) for capacity certificates, caching, dense records, and runtime repetition.
25. [Storage primitives](docs/storage-primitives.md) for pinned SRAM/latch evidence and scheduling requirements.
26. [Timed component contracts](docs/timed-components.md) for shared fetch semantics, checked signal interfaces, named edge observations, and composed structural-cache refinement.
27. [Successor-fetch experiments](docs/successor-fetch-study.md) for the measured path breakdown and controlled flow/architecture comparison with exact-cycle preservation.

Pinwheel centers on Lean specifications, executable machine models, and proofs that connect protocol behavior to a programmable engine. Fixed UART and SPI models establish concrete contracts. A shared Lean engine now runs both as reloadable timed-action programs, with compiler correctness proofs against those contracts.

The original complete execution core is described structurally in Lean and proved to implement the engine: a 32×16 instruction store, decoder, scheduler, timer, pin registers, and input capture. Composed proofs recover UART/SPI waveform correctness and SPI receive correctness for the concrete core.

The same generated SystemVerilog runs both protocols through internal atomic program commits. Lean and RTL matched on **71,703 clock edges**, including **1,032 UART/SPI transfers**. The standalone decoder passed all **65,536** input words. Three faulty RTL variants were rejected, and generic synthesis produced **1,907 cells**, including **543 register bits**. See the [core record](docs/core-hardware.md) for coverage and artifact identities.

These results establish digital circuit-model correctness and measured RTL behavior. The emitter and CIRCT transformations have not been proved correct; generic synthesis establishes neither competition area fit nor operating frequency. Translation/equivalence evidence and a physical program-loading interface remain open. The original hardware baseline embeds payload bits. The later reactive core implements input-dependent control and line release; the general backend lowers counted load images to literal E64 execution records, while the separate bounded write prototype reconstructs them at runtime.

A separate pure Lean I²C reference controller writes an address and one byte over an ideal open-drain bus, handles ACK/NACK, and waits through clock stretching. Its 19 audited theorems cover bus behavior and controller timing; 4,224 closed-loop transactions and three rejected faulty variants provide executable evidence. See the [I²C record](docs/i2c-model.md) for scope and proof boundaries; reproduce with `python3 scripts/check-i2c.py`, using only Lean and Python.

A candidate Lean engine separates drive commands from two observed inputs and supports waits, guarded timing, terminal capture, conditional branches, and input qualification. Its 38 audited theorems retain legacy compatibility and establish the general operations. Checks pass 1,024 stretched pulses and 1,024 UART/SPI transfers; reproduce with `python3 scripts/check-reactive.py`.

I²C now runs as a 79-instruction program on that candidate engine. Compiler proofs establish identical pin commands, busy status, and results to the reference for arbitrary sampled input histories during a run. The compiled suite passes 4,224 transactions, fault injections, three corrupted programs, and UART → SPI → I²C → UART reload. See [compiled I²C](docs/compiled-i2c.md) for the 29-theorem audit, reset boundary, and experimental 128-slot bank; reproduce with `python3 scripts/check-compiled-i2c.py`. The original encoded core remains the UART/SPI baseline. The integrated E64 core now implements the reactive scheduler as well.

A counted-loop alternative now stores **15 templates plus two loop descriptors and two data bytes**, reusing one bit body and one ACK body for both bytes. Its 16 audited theorems establish fetched-instruction and complete-state equality with the explicit image, with no extra modeled cycles. The same 4,224 transactions pass, alongside 6,144 generic serial loops and five rejected loop-specific corruptions. See [the byte-loop comparison](docs/looped-i2c.md); reproduce with `python3 scripts/check-compiled-i2c.py --looped`. The execution PC still spans 79 addresses; a decoder derives the loop indices. The binary-image milestone below measures serialized size; generic E64 decoder/store costs are measured below; early standard-cell mapping is now measured for the integrated indexed core and atomic loader. The later 32-entry dense cached core has the physical diagnostic above; total chip area remains unmeasured.

Canonical **PWL version 0** images now encode both forms: **715 bytes explicit versus 205 bytes counted** for the I²C example, including headers, layout, data, and bank padding. All 37 binary theorems pass the standard-axiom audit. Native file round trips, independent Python lookup, malformed-image checks, and 4,224 wire transactions through each decoded backend pass. See [the format and storage report](docs/binary-images.md); reproduce with `python3 scripts/check-binary.py`. The decoder reconstructs typed programs before execution. These are load-image sizes, not physical memory or chip-area measurements.

The package pins Lean 4.33.1 and uses bundled libraries only. Run `lake build` to check the proofs. Run `lake env lean -DwarningAsError=true --run test/Engine.lean` for compiled protocols and the reference engine's boundary/reload cases. The equivalent commands for `test/UART.lean` and `test/SPI.lean` exercise the fixed reference models. These suites write CSV traces under `build/`.

Run `python3 scripts/install-hardware-tools.py` once for the pinned Apple Silicon tools, then `python3 scripts/check-core.py` to reproduce the complete-core proofs, axiom audit, independent traces, RTL simulations, fault injections, and generic synthesis. `python3 scripts/check-hardware.py` reproduces the separate countdown/encoding experiment. See [development setup](docs/development.md) for commands and requirements.

The combined I²C register-read experiment now runs on a 256-address, 16-sample instance of the same reactive engine. It preserves the four-phase bit schedule, uses 155 addresses and eleven sample bits, and passes 4,468 wire transactions with compiler/reference correspondence proofs. Existing program and PWL V0 bounds retain their defaults. See [the register-read record](docs/i2c-register-read.md).

E64 now lowers programs into fixed 64-bit execution records and compares two writable hardware frontends. All 21 execution theorems pass the standard-axiom audit; Lean and generated RTL match 100,546 decoder vectors and 5,633 read pairs per store. Generic synthesis measures **85,629 cells / 16,384 register bits** for direct storage and **28,944 cells / 5,632 register bits** for indexed storage, with longest combinational paths of **26 versus 34 cell stages**. Each packed backend also passes the 4,468-transaction read suite. The indexed candidate supports at most 64 distinct records; these measurements exclude the wider scheduler and physical loader, and establish no mapped area or frequency. See [the hardware record](docs/execution-hardware.md); reproduce with `python3 scripts/check-execution.py` after the binary-image runner.
