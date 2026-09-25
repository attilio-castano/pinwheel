# Technical documentation

Use this index to find the record that owns a question. [Research status](research/status.md)
owns the active decision; [results](research/results.md) records completed conclusions
and reopening conditions; the [journal](research/journal.md) preserves dated evidence.
Detailed studies own their assumptions, measurements, and reproduction steps.
Historical next steps in a study are not the current work queue.

Supporting pages are grouped under `protocols/`, `engine/`, `storage/`,
`physical/`, and `history/`. The root keeps entry points and studies whose
paths are cited by experiment records. For generated and tracked evidence, use
the [physical inputs](../physical/README.md) and
[experiment records](../physical/experiments/README.md) indexes. The
[script index](../scripts/README.md) maps common checks to their entry points.

## Choose a path

| If you need to... | Read first | Then follow |
| --- | --- | --- |
| Recover the present question and avoid repeating work | [Research status](research/status.md) | The relevant [result](research/results.md), then its owning study and manifest |
| Understand the design and what is proved | [Architecture and ownership](architecture.md) | [Verification obligations](engine/processor-verification.md), then the relevant contract below |
| Run programs on the chip | [Host workflow](host-workflow.md) | [Whole-chip interface](engine/whole-chip.md) and [external timing](engine/external-interface.md) |
| Change a protocol or pin timing | [Protocol models](#protocols-and-pin-timing) | The shared [engine contract](engine/engine-model.md) and [input latency](input-latency.md) |
| Compare storage, fetch, or paired execution | [Storage primitives](storage-primitives.md) | [Fetch deadlines](fetch-contract-study.md) and [paired execution](storage/compact-execution-study.md) |
| Explain a timing or routing result | [Physical targets](physical-targets.md) | [Organization study](physical/physical-organization-study.md) and [routing diagnostics](routing-diagnostics.md) |
| Reproduce or extend an experiment | [Development setup](development.md) | [Validation](validation.md) and the [research workflow](research/README.md) |

**Read the evidence boundary before reusing a result.** A *reference* model or
flip-flop implementation protects behavior; a *retained* interface or circuit is
used by the current code or checks; an *experiment* tests a candidate under its
recorded conditions. Dated plans and integration guides explain the path taken.
These roles can overlap within a page. Lean proof, emitted RTL checks, local
physical estimates, whole-chip routing, extracted timing, and silicon answer
different questions. A tracked manifest identifies an experiment; its large
artifacts may still need to be regenerated under ignored `build/`.

## Scope, decisions, and research method

The design layers and evidence gates organize the work; dated plans and outside
examples provide context without replacing the [current decision](research/status.md).

| Record | Use it for |
| --- | --- |
| [Competition brief](competition.md) | Official constraints and source links, which must be rechecked before relying on a live external rule. |
| [Architecture and ownership](architecture.md) | The design layers, Lean's role, module map, and boundaries between proof and implementation. |
| [Processor verification obligations](engine/processor-verification.md) | The acceptance gates from protocol semantics to a physically feasible chip. |
| [Submission plan](submission-plan.md) | The dated hybrid implementation sequence and durable acceptance gates; use research status for the current work queue. |
| [Chip-contract integration record](history/branch-integration.md) | A dated account of how retained interfaces and experimental branches were reviewed together. |
| [First UART experiment plan](history/uart-experiment.md) | The historical first milestone and the criteria that led to the implemented UART model. |
| [PIO and PRU lessons](pio-pru-lessons.md) | External architectural lessons and a proposed comparison, without a selected ISA change. |

## Protocols and pin timing

The pure Lean protocol models are behavioral references. Compilers and timing
proofs state when a loaded engine program or sampled pin matches each reference.

| Record | Use it for |
| --- | --- |
| [UART transmitter model](protocols/uart-model.md) | The original byte transmitter, its timing specification, proofs, and runnable trace. |
| [SPI model](protocols/spi-model.md) | Full-duplex bit sampling and the exact timing assumptions for one controller and peripheral. |
| [I²C reference model](protocols/i2c-model.md) | Open-drain writes, acknowledgment, and clock stretching in an ideal bus model. |
| [Compiled I²C write](protocols/compiled-i2c.md) | Guarded timing, ACK branches, and correspondence of a loaded write program to the reference. |
| [Reusable I²C byte loop](protocols/looped-i2c.md) | Cycle-preserving repetition and its instruction-storage tradeoff. |
| [I²C register read](protocols/i2c-register-read.md) | A bounded combined transaction with repeated START and received data. |
| [One-byte UART receive](protocols/uart-receive.md) | Receive timing, framing errors, compiler proofs, and storage integration. |
| [UART link proof](uart-link.md) | TX-to-RX roundtrip under independent clocks and bounded observation delay. |
| [Continuous UART receive](protocols/uart-stream.md) | Rearming, one-slot result buffering, overrun accounting, and finite frame sequences. |
| [UART stream with unequal clocks](protocols/uart-stream-clocks.md) | The clock and observation-age bounds needed for finite-stream correctness. |
| [Input latency](input-latency.md) | The pin-level latency parameter and its consequences for UART, SPI, and I²C programs. |

## Engine, whole chip, and host

Follow this path from the timed-action reference to the structural circuit and
the experimental package top level. The whole-chip page states which end-to-end
claims are proved and which still rely on independent RTL checks.

| Record | Use it for |
| --- | --- |
| [Shared-engine design](engine/shared-engine.md) | Requirements learned from UART and SPI before the exact engine semantics were fixed. |
| [Timed-action engine contract](engine/engine-model.md) | Typed programs, execution timing, compiler correctness, and reloadability in Lean. |
| [Reactive engine](engine/reactive-engine.md) | Selected-input waits, independent drive enables, and compatibility with the earlier engine. |
| [Hardware baseline](engine/hardware-baseline.md) | Instruction encoding, raw-program semantics, and the initial core implementation contract. |
| [Countdown hardware](engine/countdown-hardware.md) | The first proved circuit slice and its generated RTL checks. |
| [Execution-core hardware](engine/core-hardware.md) | Complete-core refinement, reloadable RTL, independent tests, and synthesis evidence. |
| [Integrated reactive core](engine/reactive-core-hardware.md) | The structural scheduler and direct/indexed implementations of the reactive semantics. |
| [Hardware correspondence closure](engine/hardware-closure.md) | The proved dense cached backend and the boundaries of emitted-artifact equivalence. |
| [Timed component contracts](engine/timed-components.md) | Shared fetch semantics, edge observations, and structural-cache refinement. |
| [External interface contract](engine/external-interface.md) | Input-pipeline latency, open-drain behavior, and transport obligations at package pins. |
| [Pin-sampler study](pin-sampler-study.md) | A two-register input pipeline, its Lean/RTL correspondence, and a matched physical comparison. |
| [The whole chip in Lean](engine/whole-chip.md) | Serial upload, program execution, result delivery, and the scope of top-level proofs and checks. |
| [Host workflow](host-workflow.md) | Reproducing several protocol programs and retrieving their results on one unchanged RTL chip. |

## Images, storage, fetch, and paired execution

The load image, execution format, storage device, and instruction fetch are
separate choices. Keep PWL V0 binary images, E64 execution records and the
host's JSON/serial upload path, the logical flip-flop reference, and
experimental SRAM/paired formats distinct.

| Record | Use it for |
| --- | --- |
| [Binary images](storage/binary-images.md) | The canonical PWL V0 load format, decoder proofs, and exact byte accounting. |
| [E64 execution records](storage/execution-records.md) | The selected fixed-width internal record and certified lowering from load programs. |
| [Decoder and store hardware](storage/execution-hardware.md) | Standalone frontend RTL and synthesis comparisons for E64 execution. |
| [Atomic loader](storage/atomic-loader.md) | Staging, validation, and commit without exposing a partially loaded program. |
| [Cheaper storage study](storage/storage-study.md) | Whole-machine capacity and area accounting rather than instruction-bit count alone. |
| [SRAM and latch feasibility](storage-primitives.md) | Primitive measurements, complete-chip comparisons, and the hybrid SRAM decision. |
| [Memory abstraction](memory-abstraction.md) | A latency-aware memory contract and a reference prefetch machine for registered memory. |
| [Successor-fetch experiments](storage/successor-fetch-study.md) | The measured input-to-cache path and controlled fetch alternatives with exact-cycle preservation. |
| [Fetch deadlines and upload pipeline](fetch-contract-study.md) | The existing loop's availability deadlines, electrical cost, and a separate upload-pipeline experiment. |
| [Paired-successor execution](storage/compact-execution-study.md) | The rejected restricted encoding and the later full-capacity paired controller with its proof and physical gates. |
| [Program-bank selection experiment](storage/bank-selection-study.md) | Why a proved and RTL-checked parallel-bank candidate did not pass its mapping advance gate. |
| [Cache-update enable experiment](storage/cache-enable-study.md) | A matched screen with mapping gains, but no physical run or default promotion. |

## Physical organization and measurements

These studies move from logical ownership to mapped paths and saved layouts.
Local repair, global routing, extracted timing, and electrical qualification
remain separate gates; a useful diagnosis is not whole-chip closure.

| Record | Use it for |
| --- | --- |
| [Chip architecture study](physical/chip-architecture-study.md) | State ownership, per-edge resources, and communication costs before another physical run. |
| [Index-map slice study](physical/map-slice-study.md) | Why an exact bit-plane boundary still imported expensive shared controls. |
| [Local map-tile study](physical/map-tile-study.md) | Area/fanout gains from local decoding and the address-distribution cost they did not remove. |
| [Early CMOS5L mapping](physical/technology-mapping.md) | The area pressure of the initial double-bank register-backed design. |
| [General-core physical validation](physical/physical-validation.md) | The first routed baseline, extracted timing, layout checks, and their limits. |
| [First whole-chip SRAM physical experiment](chip-physical-study.md) | Pin-template integration, SRAM geometry, routing failures, and bounded layout screens. |
| [Physical correlation study](physical-correlation-study.md) | The gap between estimated and extracted wire cost, and the routed cost of clock gating. |
| [Physical targets and paired comparison](physical-targets.md) | Checked state-to-pin ownership and the staged local, route, and electrical gates. |
| [Timing and communication organization](physical/physical-organization-study.md) | A saved-chip screen, directional timing obligations, and the cost of regional decoding. |
| [Routing diagnostics](routing-diagnostics.md) | Cheap saved-layout checks before a new search or route. |
| [Structural timing](engine/structural-timing.md) | Lean-level combinational reach/depth related to emitted, mapped, and routed evidence. |
| [Register enables](physical/register-enables.md) | Certified enable/data views and gating plans, without claiming a physical result. |

## Reproduction and validation

Start with portable checks; use the owning study's pinned tools, prerequisites,
and manifest before making a claim about generated hardware or physical behavior.

| Record | Use it for |
| --- | --- |
| [Development setup](development.md) | Pinned Lean/toolchain installation and commands for a fresh checkout. |
| [Validation and review gates](validation.md) | Local pre-push checks, hardware prerequisites, and the limits of each evidence layer. |

The [research workflow](research/README.md) explains how to turn a new experiment
into a recoverable decision without duplicating status, results, or raw receipts.
