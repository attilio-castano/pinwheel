# Technical documentation

Start at [research status](research/status.md) for the active question and next
decision. These records describe individual milestones and their evidence;
historical next-step statements are not the current work queue.

1. [The competition brief](competition.md) for official constraints and primary sources.
2. [The architecture plan](architecture.md) for Lean's role, proof boundaries, and the proposed repository structure.
3. [The UART experiment plan](uart-experiment.md) for the first milestones and acceptance criteria.
4. [Development setup](development.md) for the pinned Lean toolchain and terminal build commands.
5. [The pure Lean UART experiment](uart-model.md) for its interface, proved claims, and runnable trace.
6. [The pure Lean SPI experiment](spi-model.md) for full-duplex sampling, timing proofs, and runnable checks.
7. [The shared-engine design](shared-engine.md) for requirements learned from both protocols.
8. [The implemented engine](engine-model.md) for typed programs, timing proofs, compiler correctness, and reloadability evidence.
9. [The processor verification plan](processor-verification.md) for milestone status and the remaining path to physical feasibility.
10. [The hardware baseline](hardware-baseline.md) for the implemented instruction encoding and core contract.
11. [The countdown hardware record](countdown-hardware.md) for the first circuit slice.
12. [The execution-core record](core-hardware.md) for complete-core proofs, reloadable RTL, independent checks, and synthesis evidence.
13. [The pure Lean I²C experiment](i2c-model.md) for open-drain writes, ACK/NACK, stretching, and the next engine extensions.
14. [The candidate reactive engine](reactive-engine.md) for proved legacy compatibility, selected-input waits, and a programmable stretched pulse.
15. [Compiled I²C](compiled-i2c.md) for guarded timing, ACK branches, complete write programs, and compiler correspondence proofs.
16. [Reusable byte loops](looped-i2c.md) for the 79-versus-15 storage comparison, cycle-preservation proofs, and remaining hardware costs.
17. [PWL binary images](binary-images.md) for the version-0 format, encoder/decoder proofs, generated files, and exact byte accounting.
18. [Bounded I²C register reads](i2c-register-read.md) for repeated START, received data, and the wider engine capacities.
19. [E64 execution records](execution-records.md) for the selected layout and certified lowering.
20. [Decoder/store hardware](execution-hardware.md) for the standalone frontend comparison.
21. [The integrated reactive core](reactive-core-hardware.md) for fixed-program correspondence and the direct/indexed comparison.
22. [Atomic loading](atomic-loader.md) for staging, validation, commit, initialization, proofs, and RTL checks.
23. [Early CMOS5L mapping](technology-mapping.md) for measured area pressure.
24. [Cheaper storage](storage-study.md) for capacity certificates, caching, dense records, and runtime repetition.
25. [Storage primitives](storage-primitives.md) for pinned SRAM/latch evidence and scheduling requirements.
26. [Timed component contracts](timed-components.md) for shared fetch semantics, checked signal interfaces, named edge observations, and composed structural-cache refinement.
27. [Successor-fetch experiments](successor-fetch-study.md) for the measured path breakdown and controlled flow/architecture comparison with exact-cycle preservation.
28. [Physical validation](physical-validation.md) for the first routed baseline, extracted timing, layout checks, and limitations.
29. [One-byte UART receive](uart-receive.md) for input timing, compiler proofs, E64/storage integration, framing errors, and remaining receive capabilities.
30. [UART link timing](uart-link.md) for TX-to-RX roundtrip proofs, independent clocks, bounded observation delay, and compiler composition.
31. [Continuous UART receive](uart-stream.md) for automatic rearm, buffered delivery, explicit loss accounting, finite frame-sequence proofs, and the compiled-program supervisor.
32. [Continuous reception with unequal clocks](uart-stream-clocks.md) for sufficient clock/observation-age bounds, rearm margins, finite-stream proofs, and compiled receiver composition.
33. [Hardware correspondence closure](hardware-closure.md) for countdown artifact interpretation, the composed dense cached backend, and equivalence boundaries.
34. [External interface contract](external-interface.md) for input-pipeline latency, open-drain pads, and loading transport obligations.
35. [Program-bank selection experiment](bank-selection-study.md) for the composed command-split control, parallel bank reads, full RTL read-back, and mapping/physical advance gates.
36. [Cache-update enable experiment](cache-enable-study.md) for factored update decisions, exact cache observations, and the matched mapping screen.
37. [Physical correlation study](physical-correlation-study.md) for the estimate-versus-extraction capacitance gap, hold-repair area, and flow-level discriminators on unchanged RTL.
38. [Pin-sampler study](pin-sampler-study.md) for the structural two-register input pipeline, its delayed-history refinement, emitted-RTL checks, UART age composition, and the matched physical comparison.
39. [Structural timing](structural-timing.md) for Lean-level arrival levels, reach and non-interference theorems, and their agreement with retained MLIR, mapped and routed evidence.
40. [Register enables](register-enables.md) for certified enable/data views of the proved registers, Lean-chosen gating plans, and the checked flow step that applies them to unchanged RTL.
41. [Input latency](input-latency.md) for latency as a parameter of the pin-level contracts: the bridge from the pin sampler, the SPI rate condition, the three I²C echo hazards, and the qualified STOP hold now compiled into both I²C programs.

[Research workflow](research/README.md) explains how to record new evidence.

[Validation and foundation review](validation.md) describes the local pre-push checks, hardware prerequisites, and review order.
