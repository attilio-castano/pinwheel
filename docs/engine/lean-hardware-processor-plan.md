# Processor integration contract

The processor is a later integration test for the library. Implementation stays
focused on the memory-transfer controller first. This record selects the semantic
target and identifies the contracts to freeze before CPU construction.

## ISA target and execution environment

Use the official **Unprivileged ISA release 20260120, RV32I version 2.1**.
The [official specification PDF](https://docs.riscv.org/reference/isa/v20260120/_attachments/riscv-unprivileged.pdf)
is archived in the ignored build cache and pinned by `tools/riscv-isa.json`:
4,580,174 bytes, SHA-256
`06bb3c23074f72060a0ec061a80933af948cae7ceafdcd9d1fe177b05fd150bc`.
The manifest retains title, release, target chapter and CC-BY-4.0 attribution.
Fresh checkouts obtain the exact same source with:

```sh
python3 scripts/fetch-riscv-specification.py
```

The fetcher verifies existing and downloaded bytes and refuses to replace a
mismatched cache. Source identity is fixed; memory-map, decoder and environment
implementation gates remain open.

Implement all 40 base instructions, including precise ECALL/EBREAK outcomes,
legal HINTs and conservative FENCE behavior. Keep `x0` zero while still performing
loads and faults whose destination is `x0`. Effective addresses wrap modulo
2^32. JALR clears target bit zero before alignment checks; untaken branches do
not raise target-alignment faults. FENCE reserved fields need their specified
conservative handling, rather than blanket illegal-instruction rejection.
These requirements come from the [RV32I chapter](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html).

The following are project execution-environment choices, to be encoded explicitly:

| Concern | First implementation contract |
| --- | --- |
| Core | Single hart, multicycle, serialized memory access; polling peripherals |
| Reset | PC and integer registers zero; clear pending control and terminal status; preserve memories |
| Initialization | Program/image and initialized-data coverage are explicit loader assumptions |
| Address space | Distinct executable/readable code ROM and readable/writable nonexecutable RAM; no truncation aliases; freeze capacities and peripheral windows with the memory map |
| Data representation | Little endian; signed and unsigned byte/halfword loads; byte-masked stores preserve other bytes |
| Misalignment | Precise fatal data-access trap, checked before mapping; no partial store |
| Unsupported encodings | Precise terminal illegal-instruction event, while accepting legal base HINT/FENCE encodings |
| ECALL and EBREAK | Distinct terminal events with faulting PC; no implicit syscall ABI or privileged trap handler |
| Access failures | Explicit address/access-kind event; no destination-register write or partial memory/device effect |
| Scope | No privileged modes, interrupts, caches, speculation, CSRs or optional ISA extensions |

The code ROM is loaded only while execution is quiescent. Self-modifying code
and instruction-cache synchronization are outside this first environment;
[FENCE.I belongs to Zifencei](https://docs.riscv.org/reference/isa/v20260120/unpriv/zifencei.html).
TransferRange's nonwrapping admission rule must not replace ISA address arithmetic.

## Reuse and missing library contracts

Reuse typed `Expr`/`Circuit`, complete interfaces, register banks, whole-word RAM
implementations, request/response accounting, reset preservation, hierarchy,
`Implementation`, and imported RTL correspondence.

`Memory.ByteAccess` now supplies pure little-endian word operations, raw
size/alignment classification, sign extension and byte-preservation/readback
proofs. It has no bus effects or memory-map assumptions. Add a transactional
byte-access adapter with size, byte mask, completion/fault, exactly-once
effects and reset flushing. A RAM read-modify-write implementation requires
exclusive ownership and must not be reused blindly for MMIO. GPIO, timer and
UART need separate observable-effect contracts and frozen address windows.

Keep `Timed.Refinement` for RTL-to-cycle-model equality. `Timed.Events` now
supplies the generic event-path refinement for internal cycles, fixed extraction,
finite-prefix safety, initial coverage and a separate finite service-count bound.
The transfer example checks actual memory effects and completion/abort markers;
it does not establish the CPU-specific architectural relation. Events must expose
actual reads, writes, device effects, retirement, traps, reset and environment
changes. Fixed extraction from observations, initial-state coverage, instruction
accounting and architectural-state agreement prevent a vacuous retirement proof.

A store or device effect may not be hidden until a later retirement pulse. Align
irreversible effects with architectural commit in the first implementation, or
prove a separate linearization theorem with a pending-instruction abstract state.
Reset between effect and notification must preserve the already-performed effect.
Timer ticks occur during CPU stalls too; simultaneous sampling and ticking need
an atomic edge specification or a proved equivalent ordering.

Finite event-prefix safety and progress are separate theorems. Progress targets
instruction retirement or trap, not merely a timer event. It needs a decreasing
internal rank plus independently stated memory-service assumptions; bounded
service yields a cycle bound.

## Implementation gates

1. Freeze the specification hash, instruction decoder, execution environment,
   memory map, fault priorities and reset/effect ordering.
2. Prove byte-access preservation, fault atomicity, decoder coverage and the
   executable architectural instruction semantics.
3. Construct the core and prove structural, architectural and conditional-progress
   refinements, including arbitrary-state reset recovery.
4. Differentially replay architectural effects against pinned
   [Sail](https://github.com/riscv/sail-riscv) or
   [Spike](https://github.com/riscv-software-src/riscv-isa-sim), with an explicit
   environment adapter; run applicable [architecture tests](https://github.com/riscv/riscv-arch-test)
   and record exclusions.
5. Extend RTL replay and artifact correspondence through memory effects,
   retirement and reset. Include actual corruptions of sign extension, `x0`
   access handling, JALR alignment, byte stores, duplicate effects and stale responses.
6. Run loaded polling programs using the peripheral contracts and compare synthesis
   with a straightforward independent implementation under matching constraints.

No processor correctness, ISA compliance, physical timing or fabrication result
is established by this plan.
