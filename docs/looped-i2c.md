# Explicit I²C versus a reusable byte loop

Implementation record: **2026-09-13**. The explicit [79-instruction write](compiled-i2c.md) now has a counted-loop alternative. Both run in Lean and have universally identical fetched instructions and complete engine states. The loop stores **15 instruction templates, two repeat descriptors, and two data bytes**. The follow-up [PWL v0 format](binary-images.md) now encodes the two forms in 715 and 205 bytes respectively, with codec and decoded-execution proofs. No extended circuit, area estimate, or new RTL has been produced.

## What is actually reused

The stored program has this structure:

```text
qualify bus; START
repeat 2 bytes:
    repeat 8 bits:
        setup selected bit; wait for SCL; guarded high; low hold
    ACK setup; wait for SCL; guarded high/capture; low hold/continuation
STOP low; wait for SCL; guarded STOP setup; bus-free hold; halt
```

The address byte is `address << 1`, with the write-direction bit zero; the other byte is the payload. They live in a separate two-byte data bank. The code depends on timing configuration, not the address or payload. During the inner loop, a pin expression selects a bit from the byte named by the outer loop. During ACK, the outer index selects sample 0 or 1. Only the address ACK branches to STOP on NACK; the data ACK proceeds to STOP for either result, as in the explicit baseline.

| Stored templates | Purpose |
| --- | --- |
| 0–1 | Bus qualification and START. |
| 2–5 | One bit body, used sixteen times across the two bytes. |
| 6–9 | One ACK body, used once per transmitted byte. |
| 10–13 | STOP and bus-free hold. |
| 14 | Halt. |

This reuses the same stored body, rather than just sharing a Lean helper that emits duplicated instructions. `Counted.Code.locate` selects a template and loop indices. `Template.eval` substitutes its pin, capture, and successor operands. The fetch adapter requests only individual instructions; runtime execution never creates a 79-slot expansion or calls the I²C controller. The explicit image is used by proofs and validation as the oracle.

## Where the loop counter went

This first alternative is a **counted instruction store**, rather than a conventional jump-back ISA with separate counter-update instructions. The existing seven-bit program counter is an execution address: it already encodes which byte, bit, and phase is active. Sequential execution advances that address, while fetch maps successive iterations back to the same stored templates. Branch targets remain execution addresses, so the address-NACK branch still targets STOP at address 74.

For execution addresses 2–73, subtract 2, select one of two 36-address byte regions, and select a four-phase bit or ACK body within it. The decoder derives the loop indices from that address. In this I²C layout, choosing the second region can use a compare/subtract; bit-phase selection uses the low two bits. This is a proposed structural simplification of the generic Lean lookup, not an implemented circuit or a measured timing result.

No separate loop-index registers were added to `Reactive.State`. There are no load, shift, decrement, or jump-back cycles between pin phases. The two byte values add 16 bits of program data; physical storage could be memory or registers. Fetch adds template selection, byte/bit selection, optional polarity and output-field selection, ACK sample selection, and a loop-index comparison for the successor. A decoder must meet the existing same-edge entry/capture contract. A smaller store does not automatically make that path faster or the chip smaller.

## Supported bounds and honest storage accounting

| Resource | Explicit candidate | Counted-store candidate |
| --- | --- | --- |
| Populated instructions/templates for this write | 79 | 15 |
| Byte data | Encoded in literal pin instructions | Two 8-bit values |
| Additional loop syntax | None | Two repeat nodes |
| Sequence syntax | Implicit consecutive addresses | Fourteen sequence nodes in the current tree |
| Full stored syntax for this write | Vector image | 31 nodes, including the 15 templates |
| Execution address width | 7 bits | 7 bits |
| Phase/wait counters, samples, pin registers | Existing reactive state | Exactly the same state |
| Main extra selection logic | Direct instruction lookup | Loop/template, byte/bit, sample, and successor selection |
| V0 example serialized image | 715 bytes, including bank padding | 205 bytes, including layout and data |
| Synthesized area | Not established for the extended engine | Not established |

The typed counted format admits at most **128 execution slots, 64 syntax nodes, two nested loops, eight iterations per loop, and two data bytes**. Sample slots remain eight, observed inputs two, and output value/enable pairs three. Timed durations and wait budgets remain 1–256 cycles. A successor allows at most one loop-index comparison; its branches select sequential execution, a jump, or a sample-dependent branch.

A loop operand can read either of the two nesting depths; initial environment values are zero. Data selections outside the two-byte bank fail fetch and fault on entry, restoring idle commands. `next` targets cannot wrap beyond address 127, and dispatch still checks the per-program last address. Padding fetches halt, while ordinary sequential exhaustion faults as before. The typed format enforces its tree bounds; the [V0 decoder](binary-images.md) now validates encoded input before reconstructing the typed program. A physical loader remains separate work.

The **15-versus-79 count excludes descriptor fields, operand selectors, and data bits**. The tree's sequence nodes also need representation or a proved lowering into a flat layout. Multiplying either count by the original hardware's 16-bit word width is invalid: that older encoding cannot express the reactive operations or these templates. V0 now provides exact serialized byte accounting for this tree. The evidence supports pursuing compressed storage; it does not settle physical memory allocation or ASIC area.

## Proof and executable evidence

`Engine/FetchProofs.lean` proves that a functional instruction store agreeing with an explicit bank has identical entry, continuation, dispatch, one-step, and run behavior. This includes arbitrary starting states. Keeping the existing interpreter intact supplies a comparison baseline for the adapter.

`Compile/I2CLoopProofs.lean` proves `fetch_eq` for every timing configuration, address, payload, and all 128 execution addresses, including padding. It separately proves write-address bit selection. `I2CLoopCorrectness.lean` composes the store proof into:

- Complete-state equality at every execution edge, including pin commands, timers, program counter, samples, and stop reason. There are no extra bookkeeping cycles in the Lean semantics.
- One-step equality with the explicit engine for arbitrary reset/start requests and input values.
- Pin, busy, and decoded-result correspondence with the I²C reference for arbitrary sampled input histories during an uninterrupted run.

The reference run theorem still excludes reset/reload. Engine reset clears status; the reference exposes `resetAbort`. Loop-to-explicit one-step equality covers reset, but does not erase that distinct reference interface. The proofs do not establish unconditional liveness, electrical validity, or implementation delay. The new audit covers **16 public theorems** and permits only the existing standard Lean axioms; no unfinished proofs or custom assumptions remain.

The same independent bus target and wire monitor now accept either execution backend. In loop mode, the suite additionally compares the complete state with the explicit engine at each cycle. It passes **4,224 transactions and 822,896 observed cycles**, with unchanged 255-cycle quiet and 282-cycle stretched examples. The sampled error forks exercise all four input values near wait, guard, and capture boundaries. The original three capture/branch negative variants are retained; five loop-specific variants corrupt byte selection, bit order, the final-bit boundary, ACK destination, and NACK continuation. All are rejected.

Generic tests pass **6,144 two-byte serial loops** across all byte values, both bit orders, both polarities, and all three pins' value/enable fields. They check invalid data/targets, no-wrap behavior, terminal capture before a failed jump, reset, and stopped/busy loading. A single fetch machine also passes UART → SPI → looped I²C → changed-data looped I²C → UART replacement. Those mixed I²C runs use address-NACK/STOP; the full transaction matrix separately covers payload transmission and all ACK outcomes.

```sh
python3 scripts/check-compiled-i2c.py --looped
python3 scripts/check-compiled-i2c.py
python3 scripts/check-reactive.py
```

Only the pinned Lean toolchain and Python are required. Loop-mode coverage, trace, theorem audit, logs, and source/artifact hashes are written under ignored `build/looped-i2c/`. A success receipt is removed before each run and recreated only after all checks pass. The library build now has 42 jobs. Hardware evidence remains tied to its earlier source snapshot.

## Decision and subsequent hardware evidence

Keep the explicit image as the correctness baseline. The counted representation demonstrates instruction reuse without modeled timing changes, and [PWL V0](binary-images.md) measures its load-image savings.

The subsequent [E64 decision](execution-records.md) resolves counted operands during loading and deduplicates literal records. It avoids executing the syntax tree on each edge. Explicit and counted V0 write files produce identical E64 words. The [hardware comparison](execution-hardware.md) now measures direct and indexed stores with matching ports, writable contents, and independent RTL validation. It does not measure a dedicated runtime counted-loop decoder.

The indexed store uses fewer bits and generic cells, with greater lookup depth and a limit of 64 distinct records. Carry it into the structural reactive scheduler integration while retaining direct storage as a baseline. Atomic loading, technology-mapped timing/area, conventional register-counter loops, arbitrary-length streams, and data writes during execution remain separate work.
