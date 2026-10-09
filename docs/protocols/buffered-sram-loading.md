# Initialized buffered SRAM loading and execution

Decision, 2026-10-07: derive the execution premises from actual accepted uploads,
starting from arbitrary controller registers, instruction arrays and responses.
Development continues on `codex/buffered-sram-fetch`. The existing SRAM controller,
serial frontend, image format and host remain unchanged.

The new kernel theorem establishes the binary resident execution boundary of
`pinwheel-buffered-shared-branches32-sram64-v1`. This supports programmability:
a newly uploaded image supplies the instructions consumed by the same engine,
without assuming cleared or equal startup memories. Universal source compiler
correctness and serial packet delivery composition remain subsequent gates.

## What the theorem says

Let an arbitrary actual controller/two-array state take an edge with
`initialize = 1`. Then allow any finite command history. If its last state has
`VALID = 1`, the independently tracked accepted-upload ledger determines a
nonempty resident image with at most 64 rows. Both instruction replicas, live
metadata, all sixteen dictionary descriptors and the row-zero START mirror
agree with that image. Both actual registered responses satisfy candidate
readiness after count projection; dead-address raw Q may remain stale.

From that cut, every finite fixed-image runtime prefix has the same complete
reference state as the existing full-register `Reactive.circuit`, evolved
independently with the same inputs. Every public output also agrees for
`SharedBranches.Runtime` observation queries, including
pin levels/enables, TX consumption, RX prefix, retained outcome and ownership
counters. `initialized_to_execution` proves state equality;
`initialized_to_execution_observe` proves observation equality.

The reference begins with the **actual cut's nonword core state** and the
independently tracked accepted image. It then evolves independently. This is
not a theorem about a separately specified source-language loader establishing
all core/cache/generation fields during loading. The source-language execution
and lowering relation must still be composed with this binary boundary.

The loading history may include partial, duplicate or out-of-order uploads,
rejected commands, warm or cold reset, replacement and complete transfers.
The subsequent runtime prefix excludes initialization, row/table writes,
COMMIT and reset: command values 0, 3, 4 and reserved 5 are allowed. Runtime
START, polling, retained-result reads and matching RELEASE share the same
proved engine. New uploads require a new valid cut.

## How the premises are established

| Stage | Kernel evidence |
| --- | --- |
| Actual hardware state | `SramState.step` applies `Sram.circuit.step` and `Memory.Sram.step` to the actual requests; arrays and Q have arbitrary initial values. |
| Accepted upload knowledge | `SramLoading.Ledger` records actual accepted row and dictionary writes. Unknown storage remains unknown; reset does not pretend to clear physical arrays. |
| Current image coverage | `SramCoverage` proves actual row/dictionary mask provenance, valid/count preservation and COMMIT admission. Initialization clears the coverage epoch. |
| Resident image | `resident_of_coverage` derives both live instruction banks, metadata, dictionary and START mirror. Default ledger values never stand in for uninitialized live storage. |
| Response readiness | Actual prospective-core read addresses renew both responses at valid edges. COMMIT supplies readiness; immediate START uses the mirror without a bubble. |
| Complete entry and runtime | `SramExecution` relates the selected word, metadata and dictionary expansion to the full-register entry. Nonword state and all public outputs follow; resident storage/readiness are preserved across the runtime suffix. |

COMMIT requires every live row and all sixteen descriptors. It establishes
storage completeness, not a canonical source program or semantic validity of
uploaded opcodes. A malformed resident instruction may fault; the binary
reference has the same behavior.

The count projection masks the compact 92-bit tail **before** dictionary
expansion. A dead expanded 144-bit row may still contain descriptor-zero branch
bits; the proof does not assert that the entire expanded tail is zero. The
existing entry bounds check prevents execution there.

`SramExecutionSupport` constructs ordinary dependency proof terms for the
shared expression graph. Lean's kernel checks those terms. The proof does not
use `native_decide`, unchecked evaluation, custom axioms or proof placeholders.
Executable memo evaluators and emitters retain their separate finite validation
boundaries.

## Validation

The source-pinned gate checks the whole-library axiom audit and interpreted/native
parity for fifteen independently seeded cases. Directed histories exercise
partial/duplicate loading, dictionary last-write wins, missing rows/descriptors,
full-to-short replacement, immediate COMMIT/START, rejected active/retained
writes and warm/cold owned reset. Actual and independent full-register reference
banks and Q start separately poisoned. Ordinary actual `SramState.step` checks
cover initialization, COMMIT and immediate START boundaries.
An additional robustness witness corrupts Q before immediate START and verifies
the row-zero mirror. The universal history theorem derives Q from actual macro
edges.

Three distinct kernel counterexamples show why the premises matter:

- Forged startup VALID and complete masks do not establish initialized upload knowledge.
- VALID with empty masks can satisfy vacuous coverage but lacks admitted live coverage.
- Resident banks with stale Q can dispatch a different instruction from the reference when readiness is absent.

The test replays these three scenarios beside each startup seed, recording nine
premise checks. Fifteen additional finite mutations independently alter a
physical instruction replica, independent reference word, metadata, dictionary
or START mirror.

| Canonical source/independent peer witness | Resident rows | Decoded RX result | Execution edges |
| --- | ---: | --- | ---: |
| Four-byte SPI | 4 | Four bytes, `a6 9b 42 e1` | 260 |
| Seventeen-bit JTAG | 20 | 17 bits, `0x142e1` | 228 |
| One-byte I²C register read | 42 | 8 bits, `0x96`, qualified STOP | 588 |

Each protocol image is strictly admitted from the existing source lowering,
then replayed against both typed engines for all three startup seeds. The I²C
peer verifies two STARTs and 24 consumed TX bits. Twelve source-image tamper
controls change one of instructions, controls, dictionary indices or descriptors
and must be rejected. These are finite source/peer witnesses, separate from the
universal binary theorem.

Fresh loading run `initialized-loading-02` passes in 669.971 seconds from
source commit `91eb337`. Interpreted/native statistics agree: 15 cases / 4,476
edges, 156,660 core checks, 116,376 public-output checks, 463,932 known-row
checks, 134,694 dictionary checks, 1,050 complete entry records, 7,092 candidate
checks and 3,546 resident-premise checks. All nine source/peer result checks,
fifteen equality mutations, nine premise checks and 39 ordinary actual-state
boundaries pass. Report SHA-256 is
`1c4221ed3457a126dd3ed13b55fd88fa20fcf0c7fb579e8e3e487e29319ff037`.
The first run retains its passing interpreted witness log and gate reporting
rejection; it is development evidence.

Normal and optimized Python each pass 1,123 tests with two platform-specific
skips (48.222 and 50.965 seconds). The optimized log is retained; the normal
result was observed from the command output.

Portable foundation `buffered-sram-loading-foundation-01` passes in 2,018.372
seconds: 294 modules, 57 executable suites and one kernel suite. Its new directed
loading suite checks six cases / 798 edges. The whole-library audit checks
26,145 declarations and 14,093 theorem constants with standard axioms only and
rejects the injected custom axiom. Foundation report SHA-256 is
`2cd143ef6f5e0c6d91156781b91cd77e48593cf2e15a4f825ba44247a53e3977`.

The joint [acceptance manifest](../../physical/experiments/buffered-sram-loading-results.json)
binds both reports, 430 frozen inputs and 83 accepted artifacts. All 211 prior
serial artifacts, 639 preserved predecessor files and the prior serial manifest
remain intact (851 combined pins). Of the 722 previous frozen inputs, 720 are
unchanged; only the root proof import and foundation suite list extend them.
The manifest records both historical hashes and the intentional extensions.
It also verifies all 163 prior serial development files and retains nine files
from the first narrow run separately from acceptance. No new CAD or hardware
measurement is claimed.

## Reproduce

From the repository root, with the pinned Lean toolchain and Python 3.12+:

```sh
python3 -B scripts/check-buffered-sram-loading.py --tag <fresh-loading-tag>
python3 -B scripts/check-foundation.py --tag <fresh-foundation-tag>
python3 -B -m unittest discover -s test -p 'test_*.py'
python3 -B -O -m unittest discover -s test -p 'test_*.py'
```

Fresh tags preserve earlier runs. The loading gate emits canonical source
images, raw-input fixtures, logs, a copied project static library and native
executable, then freezes source/artifact hashes. No CAD tools or predecessor
build directory are needed to rerun this formal/finite gate.

## Source and remaining obligations

| Source | Role |
| --- | --- |
| [SramState.lean](../../Pinwheel/Hardware/Buffered/SramState.lean) | Actual closed-loop controller and two digital SRAM arrays |
| [SramLoading.lean](../../Pinwheel/Hardware/Buffered/SramLoading.lean) | Accepted-upload knowledge, coherence and current coverage |
| [SramCoverage.lean](../../Pinwheel/Hardware/Buffered/SramCoverage.lean) | Actual masks, VALID and count admission |
| [SramExecutionSupport.lean](../../Pinwheel/Hardware/Buffered/SramExecutionSupport.lean) | Kernel expression dependency proofs |
| [SramExecution.lean](../../Pinwheel/Hardware/Buffered/SramExecution.lean) | Entry, runtime state/output correspondence and prospective Q renewal |
| [SramCorrespondence.lean](../../Pinwheel/Hardware/Buffered/SramCorrespondence.lean) | Initialized loading-to-execution composition |
| [BufferedSramLoading.lean](../../test/BufferedSramLoading.lean) | Directed/canonical replay and kernel counterexamples |
| [check-buffered-sram-loading.py](../../scripts/check-buffered-sram-loading.py) | Source-pinned acceptance gate |

The next formal gate should connect the common `BufferedProgram` semantics and
source lowering to the admitted resident binary image. That makes new protocol
programs the unit of the proof. Serial request delivery and owned receipt
composition can then connect that theorem to the host interface.

This result uses the existing digital `Memory.Sram` contract. It does not prove
universal native evaluation, emitter/RTL refinement, electrical SRAM timing,
serial sampling/CDC, placement/routing or package power. The accepted hardware
and host bytes are unchanged; prior hardware measurements retain their original
scope. Local artifact hashes establish integrity rather than durable backup
custody.

The [bounded SPI continuation](buffered-spi-source.md) now connects a typed
four-leaf source to its accepted resident image and composes the binary runtime
observations. The [source-execution continuation](buffered-source-execution.md)
proves decoded-image interpreter agreement; its packed circuit state relation
remains open. The [Program to pins explorer](../explorer/index.html#session) follows
finite source/image/actual-model evidence, payload reuse and replacement.
