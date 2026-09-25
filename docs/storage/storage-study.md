# Cheaper storage study

The objective is lower complete-machine area while preserving pin timing, input
capture, and atomic replacement of a committed program. Count both staging and
active storage, selection/read logic, validation, and additional execution state.
The 64-entry atomic machine remains the reference.

**Completed:** the general 32-entry, dense, cached candidate reduces typical mapped
cell area from 1.055 to 0.562 mm² (46.8%). The separate two-byte I²C repetition
prototype reaches 0.192 mm² with narrower protocol scope. The final primitive
review identifies concrete SRAM and latch options, each requiring a new timing
contract. Physical feasibility and RTL translation equivalence remain open.

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
unique E64 records are respectively **3, 11, 13, and 25** (14 for the write before the 2026-09-17 [STOP revision](../input-latency.md)). Payload and timing
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
[CMOS5L mapping constraints](../physical/technology-mapping.md), not routed chip area, full
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

## Dense physical records

A 55-bit record retains the low 17 bits (kind, pin commands, duration). Its upper
38 bits hold either the qualify budget/check (12 bits, padded) or the other
operations' check/captures/finish/targets (38 bits). Expansion reconstructs the
original E64 word, including its reserved zero bit. The external accepted E64
language is unchanged; malformed E64 words are checked before compression.

Lean proves exact round trips for every typed operation and every accepted E64
word, structural codec and store correctness, and the dense atomic machine's
one-step and arbitrary-run correspondence. The physical store holds its old
55-bit value when not writing; it does not repeatedly canonicalize unknown or
inactive storage. Both instruction images and their metadata remain staged.

The independent codec oracle passes **104,642** raw input pairs in Lean and RTL,
including **45,778 valid E64 round trips** and random noncanonical 55-bit inputs.
A corrupted expansion input is rejected. The complete 64-entry dense variant
passes **21,667** atomic/protocol edges, including a program with more than 32
unique records. Both combined 32-entry variants pass **21,409** edges, including
the additional capacity rejections, and **13,151,052** storage observations.

| Design | Corner | Cell area, µm² | Mapped FF bits | ABC combinational delay, ps |
|---|---|---:|---:|---:|
| Dense, 64 entries | Typical | 955,962.9450 | 10,201 | 9,960.46 |
| Dense, 64 entries | Slow | 961,192.0458 | 10,201 | 12,536.90 |
| Dense, 32 entries | Typical | 598,358.4642 | 6,169 | 9,939.01 |
| Dense, 32 entries | Slow | 602,012.6658 | 6,169 | 12,497.57 |
| Dense, 32 entries, cached | Typical | 561,587.4558 | 6,226 | 7,703.55 |
| Dense, 32 entries, cached | Slow | 561,952.1502 | 6,226 | 9,951.14 |

The combined design has 6,233 declared register bits; synthesis retains 6,226.
The logical cache is 64 bits, but synthesis eliminates seven declared bits in
this combination. Use the measured count rather than assuming every logical
cache bit becomes a new register.

The density saving survives the extra codec logic, though the raw cell count
increases. The combined result is **46.8% lower mapped area** than the reference
at the typical corner. Keep the distinction between proved transformations and
the tested combined serializer/RTL boundary; the emitted combined RTL has not
been formally equated to the circuit model.

```sh
lake build Pinwheel.Hardware.Storage.DenseEmit
lake env lean --run test/Storage.lean
python3 scripts/check-dense-codec.py
python3 scripts/measure-storage-variant.py dense --ff 10201
python3 scripts/measure-storage-variant.py small-dense --ff 6169
python3 scripts/measure-storage-variant.py small-dense-cached --ff 6226
```

`check-storage.py` audits all 38 public storage theorems present at this milestone
and retains the isolated 32-entry regression. Codec and per-variant receipts are
separate snapshots under `build/storage/`.


## Bounded runtime repetition

This experiment implements a flat runtime layout for the existing two-byte I²C
write. It reuses the same reactive scheduler and preserves its external edges.
It is not a general implementation of the counted syntax tree, and does not
replace the UART/SPI/I²C-read candidate above.

Each bank stores 15 literal E64 templates (960 bits), two payload bytes (16 bits),
four descriptor bytes (32 bits), and idle/last metadata (14 bits): **1,022 bits**.
Both banks, the 12-bit loader controller, 49-bit scheduler, and 64-bit current-word
cache total **2,169 declared bits**; synthesis retains **2,163 flip-flops**.
Descriptors specify body start 2, byte span 36, serial-bit span 32, and STOP 74.
The execution address selects a template, byte, bit, and phase; the reader patches
SDA enable, ACK capture destination, and the second ACK successor. There are no
extra loop-control cycles. Changing the two payload bytes retains the templates.

For comparison, loading still uses 322 host words: slots 0–14 contain templates,
15–16 payload bytes, 17–20 the four validated descriptors, 21–319 canonical halt
padding, and 320–321 metadata. Padding consumes upload time but no storage bits.
Atomic staging, rejected values without cursor advance, and busy-write rejection
remain part of the measured machine.

`Repetition.lower` returns an image with a kernel-checked certificate that all
256 fetched words equal the explicit compiler image, or rejects it. Lean proves
lookup agreement and arbitrary-input-run equality for accepted images. It also
proves the structural reader, host-layout checks, physical writes, and active-bank
preservation. These component proofs do not constitute a new monolithic proof of
the emitted atomic repetition machine; its complete integration is independently
checked. The emitter/CIRCT translation remains outside the formal proof boundary.

The certificate matrix passes **32,777 images**: all 32,768 address/data pairs at
one timing configuration plus nine timer/budget boundary combinations at a fixed
payload. This is not a universal theorem that lowering succeeds for all settings.
An independent literal-program peer, native Lean components, and emitted RTL
agree on **19,525 edges**, covering 50 wire transactions, all ACK/NACK outcomes,
stretching, timeout, changed payload, busy commit, and 39 interrupted uploads.
There are 322 rejected upload-value cases and **9,324,174** RTL storage/padding
observations. Five deliberate cache/descriptor/byte-selection corruptions fail.

| Bounded I²C design | Corner | Cell area, µm² | Mapped FF bits | ABC combinational delay, ps |
|---|---|---:|---:|---:|
| Runtime repetition, cached | Typical | 192,057.0372 | 2,163 | 8,225.99 |
| Runtime repetition, cached | Slow | 192,655.7892 | 2,163 | 11,526.70 |

The complete mapped design includes both banks, descriptors, payload, decoder,
loader, scheduler, and cache. Repetition saves area but its slow-corner path is
longer than the general combined candidate's. Its narrower scope prevents treating
these figures as an interchangeable implementation comparison.

```sh
python3 scripts/check-repetition-storage.py
```

This runner audits all **48 public storage theorems**, checks the certificate
matrix, generates independent traces, evaluates Lean components, simulates and
maps RTL, and rejects the mutants. It writes `build/storage/repetition/checked-report.json`
only after success, with source/RTL hashes and individual logs. The default
`lake build` now includes the storage study through `Pinwheel.Hardware.Storage`.

## Decision and remaining work

The [primitive-feasibility review](../storage-primitives.md) pins actual SRAM views
and records latch cell costs. Synchronous SRAM reads require successor prefetch
and a worst-case schedule; transparent latches require a phase-aware write
contract. Neither is a drop-in implementation of the current store semantics.

The **32-entry dense cached flip-flop machine** has now entered the separate
[physical validation milestone](../physical/physical-validation.md). Retain the 64-entry backend for capacity overflow and the
bounded repetition backend as research into reusable templates and payload data.
The first diagnostic routes the general core within a supported 6×4 rectangle,
at 736,821 µm² before filler insertion, with zero router DRC and antenna
violations. The implemented netlist passes the functional regression. Extracted
slow-corner setup misses the 20 ns target by 6.254 ns; slew, capacitance, and
fanout violations also remain. The missing official 8×4 floorplan, timing and
electrical closure, and translation equivalence remain open. External serial
loading and the physical wrapper remain subsequent integration work. The area
sums and ABC estimates in this study are separate from that routed evidence.
