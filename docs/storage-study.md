# Cheaper storage study

The objective is lower complete-machine area while preserving pin timing, input
capture, and atomic replacement of a committed program. Count both staging and
active storage, selection/read logic, validation, and additional execution state.
The 64-entry atomic machine remains the reference.

## Sequence and decision gates

1. Freeze the reference measurements and determine compiler dictionary demand.
2. Prove, simulate, and map a separate 32-entry dictionary variant.
3. Cache the current instruction to remove one combinational store read; prove
   the cache invariant across entry, branches, reset, and replacement. Measure it
   separately before combining it with the smaller store.
4. Overlay mutually exclusive E64 fields in a dense physical record. Retain the
   complete instruction semantics and validate the codec before measuring it.
5. Build one bounded hardware repetition experiment for the existing two-byte
   I²C write. Include templates, descriptors, payload, staging, and selection logic.
6. Check actual CMOS5L SRAM/latch options and the scheduling requirements of
   synchronous reads. Recommend the next architecture from the evidence.

A candidate advances only with correspondence evidence and independent RTL checks.
An area reduction alone does not justify a timing change or loss of supported
protocol behavior. Physical placement/routing and external serial loading follow
this study. Local validated milestones are committed separately.

## Capacity and the 32-entry candidate

`Storage.lower32` returns either a dictionary/address image with a kernel-checked
lookup equality certificate, or rejection. The certificate covers every accepted
image. It does not establish that every possible compiler configuration fits.

The executable sweep covers 198,656 configurations: UART/SPI each cover all 256
payload bytes at four timer values; I²C write/read each cover all address/payload
pairs at fixed timing and all timer/budget pairs at a fixed payload. The maximum
unique E64 records are respectively **3, 11, 14, and 25**. Payload and timing
sweeps are separate; their full Cartesian product was not enumerated. A deliberately
over-capacity image is rejected.

The experimental physical machine retains 256 execution addresses and both
atomic image banks. Each bank has 32×64 dictionary bits, 256×5 address-map bits,
and 14 metadata bits. Including the controller and scheduler gives **6,745
flip-flops**, compared with **11,353** in the 64-entry reference.

The host stream remains 322 words for direct comparison with the reference.
Dictionary slots 32–63 must contain canonical halt padding and map entries must
be below 32. Violations reject without cursor advance. Those upper slots are
logical constants, not physical registers. The original format and 64-entry
machine retain their capacities; selecting this experimental backend is explicit.

Lean proves structural next-state correspondence, arbitrary-run correspondence,
capacity preservation, and equality between the reconstructed smaller machine
and the reference transition with the explicit capacity check. Thus projection
cannot silently discard upper-slot writes or index bits.

| Atomic design | Corner | Cell area, µm² | FF bits | ABC combinational delay, ps |
|---|---|---:|---:|---:|
| 64-entry reference | Typical | 1,055,247.9336 | 11,353 | 9,976.44 |
| 64-entry reference | Slow | 1,062,866.5992 | 11,353 | 13,199.27 |
| 32-entry candidate | Typical | 636,055.9884 | 6,745 | 9,983.56 |
| 32-entry candidate | Slow | 639,525.1212 | 6,745 | 13,063.13 |

The candidate passes 20,408 independent host/protocol edges and 12,506,408 storage
observations (including logical halt padding), with two added capacity rejection
cases. The existing suite covers UART, SPI, stretched I²C write/read, interrupted
uploads, malformed words, and reset/commit/start priorities.

These are standard-cell sums and ABC combinational estimates under the same
[CMOS5L mapping constraints](technology-mapping.md), not routed chip area, full
static timing analysis, or a fit claim. The result demonstrates a substantial
area saving and little change in the slow combinational path.

Reproduce with the pinned Lean toolchain on PATH:

```sh
lake build Pinwheel.Hardware.Storage.Emit
lake env lean --run test/StorageCapacity.lean
python3 scripts/check-storage.py
```

The capacity sweep writes `build/storage/capacity.json`. The implementation runner
writes its proof audit, independent traces, generated RTL, mapping logs/netlists,
and source hashes under `build/storage/`, with `report.json` written only after
success. Reference evidence is in `build/loader/report.json` and
`build/technology/report.json`; these are distinct evidence snapshots.

## Current-instruction cache

The cache adds 64 register bits and removes the current-PC combinational read
from the active store. The successor port remains combinational. During a wait
or countdown the current word is held; when starting or changing PC it is loaded
from the successor read. A self-branch can retain the word because the active
program is immutable while busy. Idle cache contents are irrelevant; starting
always loads the new entry, including after reset or commit.

Eighteen audited Lean theorems establish the cache invariant, its preservation,
arbitrary-run correspondence to the atomic reference, and structural circuit
next-state correspondence. The emitter uses named component boundaries and
remains independently checked rather than formally verified.

| 64-entry design | Corner | Cell area, µm² | FF bits | ABC combinational delay, ps |
|---|---|---:|---:|---:|
| With current-word cache | Typical | 978,426.2376 | 11,417 | 7,109.94 |
| With current-word cache | Slow | 978,972.3720 | 11,417 | 9,952.98 |

The cache reduces mapped area despite adding registers, and improves the measured
combinational path. Lean and emitted RTL pass **21,342** independent oracle edges,
with **13,107,904** storage observations in RTL. Added cases cover consecutive
one-cycle actions, self-branches, both outcomes of a terminal-capture branch, and
successor entry overwriting that captured slot. RTL checks the cache invariant
on every busy edge; a cache held at halt is rejected by the same oracle.

Reproduce the cache experiment after generating the baseline loader vectors:

```sh
lake build Pinwheel.Hardware.Storage.CacheEmit
lake env lean --run test/Storage.lean
lake env lean -DwarningAsError=true test/StorageCacheAxioms.lean
python3 scripts/measure-storage-variant.py cached --ff 11417
lake env lean -DwarningAsError=true --run test/StorageCache.lean
```

The cache measurements are isolated from the 32-entry capacity change. Receipts,
logs, mutation, and generated artifacts are under `build/storage/cached/`.
