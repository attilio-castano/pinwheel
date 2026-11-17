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
| Memory and accelerator | Explicit RAM read/write/collision semantics, request/response interfaces, reusable DMA-style movement and a streaming transform; memory assumptions and refinement | Active: RAMs, open controller and host accelerator certified through RTL; reset preserves arbitrary memories; comparative accelerator synthesis remains |
| Processor system | Simple single-hart RV32I implementation, on-chip memory, GPIO, timer and UART; architectural refinement and reuse of prior components | Planned |
| Library release gate | Public API consolidation, independent usage example, reproducible evidence, comparative synthesis results | Planned |

Processor scope starts with a simple multicycle implementation and polling
peripherals. Privileged modes, interrupts, caches, speculation and multiple clock
domains require later explicit decisions. Before processor implementation, freeze
the authoritative ISA version and the execution environment, including reset,
alignment, unsupported operations and faults.
The [processor plan](lean-hardware-processor-plan.md) records the selected
official RV32I revision, proposed environment choices, and the missing byte-access
and architectural-event contracts. Specification hash and memory-map freeze
remain prerequisites to CPU construction.

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
mapped-RTL replay evidence; physical timing and a second arbitration integration
remain open. The [memory campaign](lean-hardware-memory-plan.md) is progressing in
parallel using the existing single-port contract and decoded flop storage.

## Decision log

- 2026-11-16: Accepted the reusable-library goal and the three integration designs.
- 2026-11-16: Start switch traffic with atomic single-flit packets. Variable-length
  packet locking and virtual-output queues are later extensions.
- 2026-11-16: Use per-input FIFO and per-output holding registers. This makes
  output stability explicit and exposes head-of-line blocking honestly.
- 2026-11-16: Keep per-flow order separate from cross-source arbitration order.
  Round-robin service is conditioned on eligibility and output opportunities.
