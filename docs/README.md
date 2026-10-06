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
| [Complete design iteration](research/complete-design-iteration.md) | The planned path to one physically validated, formally connected reference and a second capacity variant through the same workflow. |
| [Local iteration continuation](research/local-iteration-continuation.md) | Authorized local work on portable current-A replay, fresh-source interpretation and a concrete power request, with physical acceptance still separate. |
| [Established-protocol continuation](research/established-protocol-continuation.md) | Delivered four-mode SPI, bounded I²C writes/bus clear, UART supervisor/result ownership and resolved package wiring. |
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
| [SPI model](protocols/spi-model.md) | Original mode-0 byte model and its sampling/timing proofs. |
| [SPI transactions](protocols/spi-transactions.md) | All four modes, one/two-byte continuous-CS transactions, program/refinement and resolved-pad evidence. |
| [I²C reference model](protocols/i2c-model.md) | Open-drain writes, acknowledgment, and clock stretching in an ideal bus model. |
| [Compiled I²C write](protocols/compiled-i2c.md) | Guarded timing, ACK branches, and correspondence of a loaded write program to the reference. |
| [Reusable I²C byte loop](protocols/looped-i2c.md) | Cycle-preserving repetition and its instruction-storage tradeoff. |
| [I²C register read](protocols/i2c-register-read.md) | A bounded combined transaction with repeated START and received data. |
| [Reusable programs and bounded register reads](protocols/reusable-programs.md) | Named pins/captures/labels, resident UART/SPI payloads through START, compact one/two-byte I²C reads and separate source/kernel/package evidence. |
| [Unified transaction workflow](protocols/transaction-workflow.md) | Bound request/program/pin/result metadata, compile/load/run/decode API and CLI, typed resident semantics and a bounded JTAG flexibility test. |
| [Finite buffered transfers](protocols/buffered-transfers.md) | Single-transfer TX/RX ownership, retained completion, timeout recovery and independent four-byte SPI/32-bit JTAG reference-model witnesses; hardware integration remains separate. |
| [Shared buffered reactive execution](protocols/buffered-reactive.md) | Compose Reactive timing/decisions with owned data and compact counted schedules; four-byte I²C, early NACK, clock-stretch timeout and partial results on the same reference engine. |
| [First buffered hardware slice](protocols/buffered-hardware.md) | Reloadable linear circuit, dedicated 32-bit TX/RX, retained indexed result reads and release; emitted/gate SPI traces and measured register-store cost. |
| [Compact counted buffered hardware](protocols/buffered-counted-hardware.md) | Nested timed loops, same-edge rollover and shared SPI/JTAG circuitry; source-bound images, retained results and measured saved-gate cost. |
| [Reactive counted buffered hardware](protocols/buffered-reactive-hardware.md) | Shared SPI/JTAG/I²C circuit, sampled decisions, loop-aware branches and retained partial results; measured register-store cost. |
| [Production Lean frontend](protocols/program-export.md) | Static JSON request/response schemas for fixed SPI and compact I²C programs; no generated Lean request source. |
| [Bounded I²C writes and bus clear](protocols/i2c-capabilities.md) | One/two payload bytes, first-NACK STOP, nine-attempt recovery, universal digital proofs and fresh resolved-wire evidence. |
| [One-byte UART receive](protocols/uart-receive.md) | Receive timing, framing errors, compiler proofs, and storage integration. |
| [UART link proof](uart-link.md) | TX-to-RX roundtrip under independent clocks and bounded observation delay. |
| [UART supervisor and retained results](protocols/uart-supervisor.md) | Opt-in circuitry, one-edge mailbox phase, explicit ownership and fresh RTL/wire receipts. |
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
| [Paired image certificates](storage/paired-image-certificate.md) | Kernel-checked canonical source bytes, 290-word uploads and successor histories, integrated with the paired host. |
| [Conditional paired correspondence](storage/paired-formal-correspondence.md) | First proof gate: actual graph and package interpretation under an explicit SRAM contract, legal modes and active-bank preservation. |
| [Paired upload coverage](storage/paired-upload-coverage.md) | Accepted words establish the complete certified image in actual storage after initialization; enabled reads return its rows. The subsequent timed gate connects execution. |
| [Paired running-state ownership](storage/paired-runtime-ownership.md) | Running instructions, cached parameters and SRAM responses belong to the certified image on every initialized history. Actual successor selection supports the subsequent timed proof. |
| [Paired timed execution](storage/paired-timed-execution.md) | Retained public execution outputs agree with E64 before and after every edge of a certified program segment, under an explicit SRAM law. The subsequent package/host gate composes the lifecycle. |
| [Paired package and host lifecycle](storage/paired-host-lifecycle.md) | Accepted certified commit establishes E64 without another reset; actual adapters and mailbox preserve host observations. The subsequent admission gate derives upload success. |
| [Certified paired upload admission](storage/paired-upload-admission.md) | Qualified delivery of any certified image reaches accepted commit, then E64 package observations; arbitrary quiet gaps and stopped replacements are covered. |
| [Paired RTL interpretation](storage/paired-rtl-interpretation.md) | Both retained emitted modules equal their typed components and inherit the certified session theorem; standard-axiom audits and actual RTL fault rejection pass. |
| [Combined implementation acceptance](research/implementation-acceptance.md) | One reproducible report binds host certificates, conditional proof, interpreted RTL and physical implementation; SRAM, fast conditions and package power still prevent A acceptance. |
| [Current-A replay](research/current-a-replay.md) | Preflight every retained dependency, recover an immutable source/evidence snapshot and replay current v2 without relying on retired worktree paths. |
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
| [Seven-net electrical repair](physical/balanced-electrical-experiment.md) | Seven buffers clear the complete coarse electrical screen; original placements, clock routes and all SRAM write holds are preserved. |
| [Power boundary sensitivity](physical/power-boundary-results.md) | Saved-layout source, resistance and checked-workload comparisons; full activity annotation and rejection of silent fallback. Includes the [frozen protocol](physical/power-boundary-experiment.md) and [audit recipe](../physical/fixtures/power-boundary/README.md). |
| [Package-power contract](physical/package-power-contract.md) | Candidate-bound analysis request, input responsibility, activity limits and voltage-budget checks; missing provider or integration evidence prevents readiness. |
| [Qualification follow-ups](physical/qualification-followups.md) | Current local tracking for the three physical requirements, needed inputs and closure criteria; links the [prepared upstream SRAM follow-up](physical/sram-maintainer-followup.md). |
| [Physical qualification assessment](physical/physical-qualification-assessment.md) | Frozen September 28 library inventory, SRAM proposal limits, and the source/activity contract for the subsequent power experiment. Includes a [read-only audit recipe](../physical/fixtures/physical-qualification/README.md). |
| [SRAM provenance and trust boundary](physical/sram-trust-results.md) | Exact release identity, native abstraction coverage and an explicit component-contract proposal. Includes the [unsent maintainer report](physical/sram-maintainer-report.md) and [audit scripts](../physical/fixtures/sram-trust/README.md). |
| [SRAM tile width discrepancy](physical/sram-tile-results.md) | Source/physical widths differ on 96 resistors. Only the explicit counterfactual matches all devices, nets and ports; 42 fault comparisons reject. [Diagnostic recipe](../physical/fixtures/sram-tile/README.md) and [frozen protocol](physical/sram-tile-experiment.md). |
| [Hierarchical SRAM integration](physical/sram-integration-results.md) | Reproduced negative macro comparison with all 351 ports and four array levels preserved. Identifies eight failing circuit types and bounded tile/control contexts; [diagnostic recipe](../physical/fixtures/sram-integration/README.md) and [frozen protocol](physical/sram-integration-experiment.md). |
| [SRAM comparison policy](physical/sram-comparison-results.md) | All four unchanged fixtures pass both modes with checked physical ports and 42 defect rejections. Includes the [reviewable recipe](../physical/fixtures/sram-comparison/README.md), prior-verdict correction and [frozen protocol](physical/sram-comparison-experiment.md). |
| [SRAM context fixtures](physical/sram-context-results.md) | Small complete neighborhoods isolate hierarchy ownership and resistor-model/combination behavior. Six prior database matches are corrected to final-native failures. Includes [tracked reproductions](../physical/fixtures/sram-context/README.md) and the [frozen protocol](physical/sram-context-experiment.md). |
| [SRAM interface and internal qualification](physical/sram-extraction-results.md) | Passing 351-pin GDS boundary LVS and wiring-fault rejection; unchanged macro geometry; remaining internal extraction/model failures and bounded controls. Includes the [frozen protocol](physical/sram-extraction-experiment.md). |
| [Final layout checks and SRAM extraction](physical/chip-finalization-results.md) | The repair survives finishing, full-rule GDS DRC, fresh timing and circuit/pin checks. Exported-GDS LVS fails; matched controls isolate the SRAM extraction/interface boundary. Includes the [frozen protocol](physical/chip-finalization-experiment.md), failed receipts and next gate. |
| [Chip electrical integration](physical/chip-closure-results.md) | The actual chip clears electrical failures after fresh routing/extraction while preserving all clock wires and original placements. Includes failed controls, costs, the [frozen protocol](physical/chip-closure-experiment.md), and remaining final-signoff gates. |
| [Live protection/electrical repair](physical/live-closure-results.md) | A small routed fixture completes checked repair, rerouting and extraction; establishes protection-group and routing-state controls before transfer to the chip. Includes the [frozen protocol](physical/live-closure-experiment.md). |
| [Protection and electrical closure](physical/protection-closure-results.md) | Costs blanket reserve and identifies the native router-state requirement for repair after antenna insertion. The restart probe is rejected; the live fixture above owns the subsequent integration result. Includes the [frozen protocol](physical/protection-closure-experiment.md). |
| [Transport repair and third detailed layout](physical/transport-split-results.md) | Both long-route repairs survive extraction; all previous 14 fanout failures clear, but four different nets and one capacitance outlier still fail. Includes the [frozen protocol](physical/transport-split-experiment.md). |
| [Antenna-aware branch placement](physical/antenna-load-results.md) | Reject the coarse candidate: fanout headroom preserves function and timing, but two parent wires exceed capacitance. Includes the [frozen protocol](physical/antenna-load-experiment.md). |
| [Balanced detailed layout](physical/balanced-detailed-experiment.md) | Positive extracted timing and passing stated layout/circuit checks; antenna-induced fanout and one capacitance failure remain. Both A attempts used. |
| [Balanced signal distribution](physical/buffer-balance-experiment.md) | Shallow mapped buffer trees clear coarse congestion; completed repair passes screening timing, with seven electrical nets still open. |
| [Upload-validation lookup isolation](physical/validation-isolation-experiment.md) | Opt-in circuit equivalence, explicit area cost and a fresh physical screen of the SRAM-to-rejection dependency. |
| [Design A detailed layout](physical/design-iteration-experiment.md) | Completed routing, DRC import diagnosis, LVS and extracted timing under the complete-design-iteration plan. |
| [Coordinated status/decode placement](physical/status-region-placement-experiment.md) | Joint placement improves local timing without added area; complete routing creates new clock, hold, electrical and congestion failures. |
| [Placement, routing and repair](physical/routed-repair-experiment.md) | A matched native repair flow clears electrical violations and improves setup on the coordinated layout; hold, reserve and routing gates remain separate. |
| [Protected-load hold repair](physical/hold-repair-experiment.md) | A tested native fix completes the continuation and passes retained setup/hold and reported electrical limits; reserve, area and congestion remain explicit. |
| [Route import repair and one signal buffer](physical/route-import-fix-experiment.md) | Exact import and real edit/revert accounting pass; one buffer removes a reserve shortfall with unchanged global timing/clocks. Four shortfalls and 25 overflow units remain. |
| [Saved-route import controls](physical/incremental-routing-import-experiment.md) | Unchanged routes and timing conceal lost demand and capacity drift; a failed control blocks the local signal edit. |
| [Routing policy and reserve](physical/routing-policy-experiment.md) | An ineffective grid option and matched timing-priority reroute expose route-dependent electrical failures; retain the saved hold-repair checkpoint. |
| [Control distribution and competing read paths](physical/control-distribution-experiment.md) | Two further variants fail qualification; complete-route regressions, changing critical paths and distinct congestion measures motivate a regional placement comparison. |
| [SRAM distribution and write timing](physical/sram-distribution-experiment.md) | Full-watchlist timing, two buffer variants, matched coarse routes and the remaining qualification gaps. |
| [Regional decoding](physical/regional-decoding-experiment.md) | Actual combinational copies, input distribution, area overage and their measured timing effect. |
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
