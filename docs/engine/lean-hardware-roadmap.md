# Lean hardware library: autonomous development goal

Build a reusable Lean hardware library capable of constructing and verifying a
small processor-based system, with proofs that survive component parameter and
composition changes. The library is the product; the integration designs test
whether its abstractions are sufficient and reusable.

## Operating agreement

Choose the next missing abstraction from a concrete integration requirement.
Develop its semantics, contract, circuit, proofs, and independent validation
together. Commit coherent validated increments. Record decisions and distinguish
what is proved, simulated, synthesized, and physically qualified.

Local implementation, inspection, testing, refactoring and commits are authorized.
Escalate changes to the agreed goal, paid infrastructure, publication, or
fabrication. Preserve unrelated work and existing physical artifacts. Keep work
on `codex/lean-stream-hardware-milestone` until isolation or review requires another
branch. The existing untracked relocation script is outside this campaign.

## Completion criteria

1. A coherent public API covers typed interfaces, combinational logic, state,
   memories, streams, hierarchy and composition, with documented semantics.
2. Standard components carry parameterized contracts for relevant safety,
   ordering, capacity, reset and conditional progress properties.
3. The packet switch, memory-to-memory accelerator and processor system have
   executable specifications, Lean simulation, emitted RTL, independent replay,
   artifact correspondence and synthesis evidence.
4. The processor has architectural refinement to an explicitly frozen ISA model;
   memory, peripheral and environment assumptions are visible.
5. Synthesis area and timing are compared with straightforward independently
   validated implementations under matching constraints. Material regressions are
   investigated rather than hidden behind proof success.
6. Fresh-checkout commands reproduce validation, and a new example can be built
   through the public API without changing library internals.

The current two-state digital RTL interpretation boundary includes Yosys and the
restricted JSON adapter. Reducing this boundary is desirable; universal synthesis
correctness and physical qualification are not implied by artifact proofs.

## Campaigns and gates

| Campaign | Deliverable and completion gate | Status |
| --- | --- | --- |
| Serial foundation | Parameterized FIFO/map pipelines; contracts, RTL and fresh-source validation | Complete: `224b288` |
| Branching foundation | Named bundles; atomic broadcast and ordered join; 27 configurations and 54 artifact certificates | Complete: `5e373bf` through `b1bf8b2` |
| Packet switch | Buffered input queues, routing, round-robin arbitration, output stability, per-flow order and conditional fairness; multiport RTL certificates and synthesis baseline | Active |
| Memory and accelerator | Explicit RAM read/write/collision semantics, request/response interfaces, reusable DMA-style movement and a streaming transform; memory assumptions and refinement | Active: RAMs and host accelerator certified through RTL; baseline/matched mapping complete; proved ownership optimization improves estimated delay; 24 pre-layout STA analyses complete with positive setup/hold slack but fanout violations in every case |
| Processor system | Simple single-hart RV32I implementation, on-chip memory, GPIO, timer and UART; architectural refinement and reuse of prior components | [Firmware, artifact and physical verification](#rv32i-firmware-and-hardware-verification). Core/system cycle and architectural-event refinement are proved. Byte RAM/MMIO and four UART/MMIO configurations have imported RTL certificates. Cold-loaded firmware replay passes emitted and synthesized RTL. 548 Sail cases and 39 upstream architecture-test bodies in two modes pass. |
| Library release gate | Public API consolidation, independent usage example, reproducible evidence, comparative synthesis results | Active. A standalone lane client exercises simulation, RTL replay and kernel correspondence across two configurations and two FIFO backends. |

Processor scope starts with a simple multicycle implementation and polling
peripherals. Privileged modes, interrupts, caches, speculation and multiple clock
domains require later explicit decisions. Before processor implementation, freeze
the authoritative ISA version and the execution environment, including reset,
alignment, unsupported operations and faults.
The [processor plan](lean-hardware-processor-plan.md) records the selected
official RV32I revision, frozen environment choices, and the remaining device
and architectural-event contracts. The official specification hash and memory
map are fixed. Decoder, checked routing, instruction execution and atomic device
contracts support the complete physical core's cycle refinement and reset
recovery. Digital UART frame timing and structural correspondence are proved.
Connected system cycle refinement and cold loaded firmware replay are complete.
Actual-port architectural-event refinement, cancellation accounting and
conditional service-count progress are complete. The independent Sail comparison
and selected upstream architecture-test campaign pass in their documented model
environments.

## RV32I firmware and hardware verification

The reference system is a cold-loaded RV32I processor that drives Ready through
its existing GPIO words. A ROM program sends quad commands, polls readiness,
samples each reply nibble, acknowledges the result and releases the SPI engine.
The target supplies MISO independently. There are two implementations of Ready
program storage, direct and registered. Both expose the same timed interface.

At a clock edge, a circuit maps its current registers and inputs to outputs
and next registers. Proving both maps agree gives agreement over any finite
run by induction. This still works with feedback: matching outputs make the
same CPU and peer choose matching next inputs. The protocol proof can then
use that common pin history, and a store replacement can reuse the CPU proof.

### Current evidence

- `ReadyHost.feedback_refines` connects the typed processor to its model under
  feedback from an arbitrary device and peer. For a valid CPU state after
  loader release, each finite prefix agrees on the projected CPU state, peer
  state, device state and observed edges. `store_substitution` gives the
  corresponding result when replacing the Ready instruction store.
- `ReadySPI.sample_retirement` follows the ROM's load at PC 100 through four
  CPU clocks. The value retired to x12 comes from the pads at MMIO service.
  `collected_gpio_word` proves that eight matching data nibbles give the
  chosen 32-bit value in x25, for arbitrary GPIO status bits and accumulator.
- `ReadySPI.completed_feedback` specializes the SPI timing and data theorem
  to the typed CPU and an independently reacting peer. Given an admitted
  START, legal runtime traffic with no intervening RELEASE, and an accepted
  RELEASE, chip select brackets the requested pulses, MOSI carries the
  accepted bits, MISO supplies the exported bits and the entire count is
  acknowledged. Proving the ROM reaches those service points is the next
  firmware obligation.
- `scripts/check-processor-ready-spi.py --tag TAG` emits both store variants
  and the processor, checks mode-0 MOSI at the peer, and decodes all ten
  firmware-read replies including CRC and sequence. Two independent MISO
  words reach x25 on both stores. Each run takes 29,723 clocks, including
  29,717 post-loader clocks checked against the Lean processor model. The
  inverse-MISO control changes both the receipt and x25 on each store.
- The full RV32I core certificate proves trace agreement for arbitrary raw
  registers and finite input histories. It covers all 37 next-register
  values and 67 outputs. The SPI gate's `--core-report` option checks the
  exact instantiated core and matches the wrapper, RAM and MMIO Verilog
  against the cold-boot reference. The bus changes with the ROM. The
  [processor verification record](lean-hardware-processor-plan.md#tapped-core-rtl-correspondence)
  gives the commands and evidence boundary.

### Autonomous execution order

| Milestone | Work and acceptance gate |
| --- | --- |
| 1. Certify the processor hierarchy | The tapped core and its identity in the firmware hierarchy are checked. Certify the ROM-specific bus, bind the exact RAM and MMIO implementations, then compose the four leaf certificates over the typed top-level wires. Re-run the cold-load and feedback clients. |
| 2. Prove firmware service | Give the ROM loop an invariant over PC, frame number, nibble index, receive accumulator and Ready owner. Prove its GPIO stores produce one rising host-clock edge per nibble and its loads sample the corresponding reply. Derive acknowledgement, RELEASE and x25 from the peer's sampled word. State readiness, reset and peer timing assumptions, then derive a cycle bound under bounded service. |
| 3. Demonstrate reuse | Run a different transfer length or SPI mode, then a UART firmware exchange through the existing serial interface. Reuse the CPU and memory proofs. Identify and discharge only the new framing, device, buffer and timing obligations. Check changed firmware images through their own ROM binding. |
| 4. Map the same system to FPGA | Freeze RTL, ROM, pin map and clock constraints. Synthesize and place-and-route for one named part. Check the mapped logic against the RTL at the same interfaces, replay the firmware and report utilization, unconstrained paths and worst constrained slack. Board measurement adds a separate trace of the peer exchange. |
| 5. Compare ASIC implementations | Start with the pinned IHP SG13CMOS5L typical and slow cell libraries. Map both Ready stores with the same firmware, clock, loads and flow settings. Measure area and the critical path and replay the mapped result. Carry the selected implementation through routing, extracted timing and physical checks. Record pad, memory, clock and electrical assumptions at the target boundary. |

For each increment, preserve the passing artifact by digest, isolate the first
failing obligation, then rerun its consumer with the replacement proof or
artifact. A useful optimization experiment changes only Ready storage while the
firmware, peer workload and external contract stay fixed. FPGA timing,
ASIC corner timing and measured board behavior each have their own gate.

## First campaign: buffered packet switch

Start with single-flit packets: destination plus payload, transferred atomically
on a ready/valid handshake. Inputs and outputs are parameterized independently.
Each input has a bounded FIFO; each output has a holding register and a
round-robin cursor. Only an input's head packet participates in routing.

The output register decouples the chosen transaction from future arbitration,
so a stalled output remains stable. Arbitration selects an eligible head when
the output slot can accept. Its cursor advances on a successful internal transfer,
not on an unaccepted combinational grant. A full input FIFO may dequeue and
enqueue together. New inputs cannot bypass the registered FIFO.

Safety goals:

- Every admitted packet is either pending or emitted exactly once in its reset
  epoch, at its declared destination.
- Each input dequeues in FIFO order; each source/destination flow emits in order.
  Different destinations may complete at different times, so there is no total
  completion-order promise across them or across independent sources.
- An input cannot be consumed by two outputs on one edge; an output cannot take
  two inputs on one edge. Occupancy stays within declared bounds.
- Reset cancels transfers, clears pending work and restores a specified initial
  cursor. Physical refinement must establish initialization from arbitrary bits.

Progress goals:

- A continuously eligible head request is served within a bound measured in
  successful arbitration opportunities, with cursor advancement defined above.
- Cycle bounds additionally require downstream readiness assumptions.
- Head-of-line blocking is explicit: a blocked head can prevent packets for other
  destinations behind it from progressing. Fairness is not an unconditional
  latency guarantee for every enqueued packet.

The logical destination type is finite. The hardware adapter must separately
define what happens to unused raw destination encodings for non-power-of-two
output counts; an invariant over `Fin outputs` alone is insufficient.

Implementation sequence:

1. Executable round-robin selection and buffered-switch model; local invariants.
2. Multiport, per-flow accounting and ordering; fairness assumptions and proofs.
3. Typed physical interface, destination decoding, arbitration circuit, queue and
   output-register composition; structural refinement.
4. Independent traffic oracle, targeted mutations, parameter matrix, and complete
   flat/hierarchical artifact correspondence.
5. Synthesis and baseline comparison; API cleanup demonstrated by a second user
   of the arbitration and buffering components.

Do not mark the campaign complete when only its model or simulation passes.
Each gate needs evidence at its stated abstraction level.

The [switch implementation record](lean-hardware-switch.md) tracks the reusable
APIs, validation commands and remaining artifact/resource gates. The executable
model, multiport contracts, conditional fairness, physical codec and complete
structural refinement are implemented. Reset recovery includes arbitrary physical
register bits. Whole-switch emitted/synthesized RTL replay, an independent
resource baseline and arbitrary-state hierarchy comparisons are complete.
Full-matrix artifact certificates for both flat architectures and the original
hierarchy are complete. Shared selection has matched technology-mapping and
mapped-RTL replay evidence; physical timing remains open. The
[buffered merge](lean-hardware-buffered-merge.md) completes the second arbitration
integration through parameterized contracts, structural proofs, RTL replay and
15 complete artifact certificates. The [memory campaign](lean-hardware-memory-plan.md) is progressing in
parallel using the existing single-port contract and decoded flop storage.

## Decision log

- 2026-11-16: Accepted the reusable-library goal and the three integration designs.
- 2026-11-16: Start switch traffic with atomic single-flit packets. Variable-length
  packet locking and virtual-output queues are later extensions.
- 2026-11-16: Use per-input FIFO and per-output holding registers. This makes
  output stability explicit and exposes head-of-line blocking honestly.
- 2026-11-16: Keep per-flow order separate from cross-source arbitration order.
  Round-robin service is conditioned on eligibility and output opportunities.
