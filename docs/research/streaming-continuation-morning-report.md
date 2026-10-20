# Streaming continuation campaign report

**The mandatory goal and all three ordered stretches are qualified,
2026-10-18 00:02 UTC.** Long streaming SPI/JTAG, reactive I²C, autonomous UART
and universal correspondence for the new mapped device each passed fresh
committed-source gates and immutable evidence export. The final mapped stage
also closes the earliest public-BUSY UART proof. Physical signoff remains open.

Campaign: 2026-10-17 15:30:35 UTC to at most 2026-10-18 03:30:35 UTC.
Branch: `codex/streaming-continuation`.
Baseline: `31816bb86aa5154c2671a8d479650c7b063d93aa`.
Mandatory source/producers: `dcce3312b8634d97536e997e672e06f094ba567a`.

## Result

The new opt-in `pinwheel-streaming-quad-v1` can execute a **4 KiB duplex SPI
transfer** and a **4,097-bit JTAG scan**, each with one START and one owner.
Both use the same emitted circuit at queue depths two and four. The host uploads
different small programs and repeatedly services bounded queues through public
pins. It does not restart the engine at chunk boundaries or store the complete
message in device registers.

The program bank is fixed at 64×64 bits. Each TX/RX FIFO has two or four 32-bit
slots with valid-bit counts. Complete declared device state, including the
program, frontend, staging, CRC, replay and retained receipt, is **6,039 / 6,195
bits** at the two depths. Source transcript lists are proof ghosts.

The existing target and its historical artifacts are preserved. The new target
has its own interface contract; this is not a project-wide version replacement.

## Validation

| Gate | Exact committed-source result |
| --- | --- |
| Full continuation | PASS; `streaming-full-dcce331-20261017-01` |
| Public-pin peers and controls | 1,007,046 physical edges; both long workloads, both depths, frame/CRC/replay/custody/staging controls |
| Complete generated proof audit | 36,531 declarations, 24,121 theorems; standard axioms only; injected private axiom rejected |
| Required native theorem interfaces | All 18 boot/runtime/custody/reset/fair-service APIs checked at both depths |
| Python discovery | PASS; 1,344 tests, eight explicit fixture/platform skips; `streaming-python-dcce331-20261017-01` |
| Foundation | PASS; 564 modules, 65 executable suites, two kernel suites, 73 commands; `streaming-foundation-dcce331-20261017-01` |
| Immutable evidence export | PASS; `streaming-export-dcce331-20261017-01`; accepted receipts, source membership, retained artifacts and intake patch rechecked |

The full gate starts with separate fresh source and producer Git archives and
an empty build cache. It checks actual emitted raw RTL equations for every
register/output, actual package and Tiny Tapeout wiring, and distinguishing
stored-state/output/wiring/clock mutations. It then runs independent resolved-pin
peers against the certified RTL and maps those exact sources. Archive, source,
tool/runtime, generated-input and artifact hashes are checked at closeout.

The foundation's separate whole-library audit accepted 39,595 declarations and
22,232 theorems. The compact [evidence manifest](evidence/streaming-continuation-20261017/manifest.json)
retains hashes and compressed copies of all three accepted receipts, the generated
boot/runtime theorem interfaces, and the positive and negative audit summaries.
The large generated artifacts remain at their recorded retained build paths.

The eight Python skips concern unavailable archived CAD/functional-model/export
fixtures and Linux-only process observations. They do not stand in for RTL or
mapping qualification; the separate full gate actually runs the pinned Icarus,
Yosys, ABC and native Lean tools.

## Sustained host service and timing

Read-only analysis of the final clean SPI public-pin traces found **246–248
engine clocks between ordinary EXCHANGE starts**. Each response can retire up
to 32 RX bits; 32 default cells take 288 engine clocks. This observed service
schedule leaves 40 clocks of margin per full RX chunk. The single 4,343-clock
interval contains the intentional 4,096-clock host pause; the engine parks LOW
until credit returns. This is measured headroom for the qualified schedule,
not a universal throughput guarantee. Reducing the half-period to three gives
224 clocks per chunk, so this host schedule can induce LOW credit stalls.

The two analyzed `wire.bin` hashes are
`f23b3c973d897c27ff9e516405aeeb3d2d8567b4c542b7dace02b6d239aef99c`
(depth two) and
`292dae199e5d9261f3e64fd14b10a01132a6f167c16435022ac398f48f57b152`
(depth four), under the accepted full receipt's `worker/wire/` directory.
The request-to-response-close spans were 245–247 clocks over 1,198 / 1,195
EXCHANGEs respectively. The extraction uses CS, SCK, MOSI, MISO and READY;
it does not read internal queue state.

The public helper requires a half-period of at least three. A separately
labelled development sweep deliberately bypassed that helper to probe periods
one through four with peer output delays zero and one. It produced 20 safe
passes and 12 expected RX failures; TX remained correct. That probe illustrates
the two sampler stages and does not expand the qualified default timing claim.

## What the proofs establish

Concrete sampled-pin uploads derive initialization from arbitrary power-up
registers. Loader acceptance, coverage, VALID and image binding are conclusions,
rather than supplied agreement premises. SPI/JTAG boot witnesses include every
request, CRC-work clock and exact response read.

An actual admitted START establishes source bounds and reached custody. The
proofs track accepted/consumed TX, captured/popped RX, the frontend's actual
retained bytes and exact acknowledgment interval. RELEASE requires complete
drain/acknowledgment; a later START cannot erase a prior receipt.

Weak fairness of the actual reached feedback session permits arbitrary finite
credit stalls and proves finite arrival at completion **or fault**. It assumes
eventual credit at reached boundaries and gives no wall-clock bound. HIGH timing
is exact; queue stalls extend the parked LOW phase. A separate LOW/stable-input
proof accounts for both sampler stages and arbitrary initial sampler contents.

Installed runtime excludes cold/warm reset and loader WRITE/COMMIT commands,
including rejected loader commands. Warm cancellation has its own all-register
theorem: it returns to an uninstalled state, retaining words, idle configuration
and allocation IDs while clearing validity, coverage and runtime custody.

See [source/boot review](streaming-source-boot-review.md),
[timing boundary review](streaming-timing-boundary-review.md), and the
[wire/ISA contract](../protocols/streaming-continuation.md).

## Bugs found and repaired

- A finishing SPI pulse briefly released and reasserted chip select before HALT.
  The suffix now holds CS low throughout; HALT performs the sole release.
- A retained TX offer could retire an RX acknowledgment before being rejected.
  New retained TX offers are refused before acknowledgment effects.
- A busy-admitted TX reservation could cross the terminal edge and then fail
  staging. The core now permits those already reserved beats under the same
  retained owner. Unused TX stays owned and blocks RELEASE until explicit reset.
  Eight public-edge-aligned HALT/FAULT cases at both depths distinguish the fix
  from the earlier source revision.

## Complete matched cost

All four rows use the pinned typical CMOS5L Liberty and identical mapping,
drive/load, flattening and no-retiming settings. Area is summed standard-cell
area, not a placed footprint. These targets have different instruction sets;
the older target also supplies wait/qualification/branch features.

| Package/model | Declared bits | Mapped FF bits | Cell area µm² | ABC delay ps |
| --- | ---: | ---: | ---: | ---: |
| Streaming depth 2 | 6,039 | 5,786 | 514,743 | 4,001.76 |
| Streaming depth 4 | 6,195 | 5,942 | 527,510 | 4,292.01 |
| Older macro-excluded logic | 3,540 | 3,520 | 310,151 | 6,429.51 |
| Older complete register-backed digital memory | 11,860 | 11,840 | 990,614 | 8,073.36 |

The macro-excluded row additionally omits **8,192 memory-array bits and 128
synchronous output bits**, whose macro area/delay are not included. The full
digital row includes them as flip-flops. The new program bank is entirely
register-backed and fully counted.

ABC delay is a combinational Liberty estimate with sequential/macro boundaries
cut, buffer-2 drive, load 10 fF and no wire-load model. It excludes clock-to-Q,
setup, clock trees, placement, routing and parasitics. It establishes no guaranteed
Fmax or timing signoff. Each mapping uses a fresh isolated native temporary
directory; generated SCL/scripts/BLIF are retained, with no global SCL cache use.

## Remaining work and claim limits

The mandatory finish line and all ordered stretches are closed, including
universal correspondence for the new proof-oriented mapped hierarchy. The
mandatory streaming target and its evidence remain unchanged; sampled-ready
behavior has its own opt-in target and receipts.

The kernel proofs concern two-state digital semantics and the interpreted
emitted artifacts. Finite peers are separate protocol evidence. Standalone
Python image validation does not launch Lean; the fresh qualification worker
automatically kernel-checks its concrete images before wire I/O. The new mapped
artifact has a kernel-checked functional correspondence certificate; the earlier
globally optimized cost netlists still have no such certificate. The restricted
JSON/Liberty interpretation, Lean/native runtimes and host system remain trust
boundaries. Physical SRAM, CDC/metastability, electrical/board behavior, delay,
Fmax, placement/routing and silicon signoff are not proven. UART remains a
single-frame contract, and I²C still excludes immediate NACK branching,
repeated START and arbitration.

Only local commits are authorized. No push, PR, publication, paid service,
fabrication or provider message has been performed. Both intake-dirty documents
remain byte-identical to their recorded campaign hashes.


## Reactive I²C stretch checkpoint

Source and producers: `063d538410c1754e4c29fa14955e97b530f373a2`.
The separately named `pinwheel-streaming-ready-cell64-v1` adds sampled-input
WAIT and guarded HIGH capture without adding source register bits or ports.
A bounded wait tests the pre-edge second sampler; readiness wins on the last
permitted poll. Exhaustion faults and preserves the exact captured RX prefix.
Unused accepted TX remains owned and blocks RELEASE until warm cancellation.

One seven-row image performs either a 64-byte read or write at address `0x52`,
including address/ACK slots: 585 slots under one START. The same emitted circuit
at each depth accepts both operations. The peer drives resolved SCL/SDA from
public edges and enforces timing independently of the compiler/source model.

| Gate | Exact committed-source result |
| --- | --- |
| Full Ready gate | PASS; `streaming-ready-full-063d538-20261017-01`; 659.566 seconds |
| Public-pin peers | 20 I²C cases plus six deadline/sampler/guard controls at both depths; 212,612 edges |
| Complete generated proof audit | 40,709 declarations, 26,895 theorems; standard axioms only |
| Required native theorem interfaces | All 14 source/boot/runtime/custody/progress APIs at both depths |
| Python discovery | PASS; 1,461 tests, eight explicit fixture/platform skips; `streaming-ready-python-063d538-20261017-01` |
| Foundation | PASS; 606 modules, 65 executable suites, five kernel suites, 76 commands; `streaming-ready-foundation-063d538-20261017-01` |
| Foundation proof audit | 42,838 declarations, 24,410 theorems; injected untrusted axiom rejected |
| Immutable evidence export | PASS; `streaming-ready-export-063d538-20261017-01`; all exported bytes and raw/compressed receipt hashes rechecked |

The [Ready evidence manifest](evidence/streaming-ready-continuation-20261017/manifest.json)
records the source archives, exact producers, retained artifact hashes, proof
closures, command intent/input freezes, actual mutation sources/executables and
pinned technology library. The exporter independently verified 12,778 retained
files and twelve raw-certified-to-wire/cost source equalities. Earlier mandatory
checkpoint evidence remains byte-identical to its committed version.

The default LOW/HIGH profile is 4/4 clocks with a 31-poll budget and a tested
28-clock target stretch. The last permitted poll succeeds; a later release
faults with the precise prefix retained. A timeout after 50 captures preserves
one 32-bit chunk plus an 18-bit partial chunk. Accepted but unused TX remains
owned. The actual sampler-stage bypass and guard bypass RTL mutations are
rejected by completed native runs, independently of the private-axiom control.

This stage exposed and repaired an asymmetric STOP timing error: using HIGH for
both STOP-preparation halves shortened LOW when LOW was larger. The repaired
source/compiler preserves the declared LOW half. A 16/3-clock development case
failed before the repair and passed afterward against the same strict peer;
the accepted fresh gates include the repair and exact source/word checks.

| Ready package | Declared bits | Mapped FF bits | Cell area µm² | ABC delay ps |
| --- | ---: | ---: | ---: | ---: |
| Depth 2 | 6,039 | 5,797 | 517,708.5354 | 4,272.89 |
| Depth 4 | 6,195 | 5,953 | 531,565.6752 | 4,363.05 |

The guard extension costs eleven mapped FF bits at either depth compared with
the mandatory streaming circuit; the two older comparison rows reproduced their
previous matched costs. These are complete mapped cell costs and combinational
Liberty estimates, with the same timing/signoff limits stated above.

The I²C source theorem composes concrete cold boot, arbitrary source-legal
runtime, reached custody and generic fair completion. The generic progress API
still takes its explicit fairness structure; bounded I²C guards require no
readiness fairness, while eventual host credit remains an assumption. It does
not implement immediate NACK branching, repeated START, arbitration or an
electrical I²C qualification. See [Ready contract](../protocols/streaming-ready.md).


## Autonomous UART stretch checkpoint

Source and producers: `0425b03a8c997b0a3c89f3f950a1511d91f6610f`.
A nine-row 8N1 receive program runs on the same Ready circuit used for I²C,
SPI and JTAG, with no new register bits or UART-specific ports. One START
receives one frame while the host remains deselected. All protocol outputs
are released; held-HIGH input waits until a falling edge or cancellation.

| Gate | Exact committed-source result |
| --- | --- |
| Full UART gate | PASS; `streaming-uart-full-0425b03-20261017-01`; 1,155.889 seconds |
| Public-pin peers | 5,481,898 edges: 4,573,680 UART, 181,702 I²C, 30,910 I²C controls and 695,606 long SPI/JTAG edges |
| UART corpus | 1,560 cases: every byte at quarter-periods 4, 12 and 128, both depths, framing and sampling-window controls, actual sampler RTL mutations |
| Complete generated proof audit | 41,305 declarations, 27,314 theorems; standard axioms only |
| Required native theorem interfaces | All 22 source/boot/runtime/custody/UART APIs at both depths |
| Python discovery | PASS; 1,535 tests, eight explicit fixture/platform skips; `streaming-uart-python-0425b03-20261017-01` |
| Foundation | PASS; 625 modules, 65 executable suites, eight kernel suites, 79 commands; `streaming-uart-foundation-0425b03-20261017-01` |
| Foundation proof audit | 43,410 declarations, 24,809 theorems; injected untrusted axiom rejected |
| Immutable evidence export | PASS; `streaming-uart-export-0425b03-20261017-01`; all 15 exported file hashes and all raw/compressed receipts independently rechecked |

The [UART evidence manifest](evidence/streaming-uart-continuation-20261017/manifest.json)
binds the exact committed sources and retained artifacts. Its exporter
independently checked the source and producer archives, 9,957 full-gate retained
artifacts, 5,180 frozen inputs, native process records and twelve raw-certified
source-to-wire/cost equalities. The historical mandatory and Ready evidence
remain byte-identical. Matched cell costs reproduce the Ready rows above.

Universal source proofs cover all quarter-periods Q from 4 through 128, either
RX input selector and arbitrary eight-bit payloads. Physical peers exercise
Q=4, 12 and 128 on RX0. After a raw falling edge F, the default source samples
the start at F+2Q+2, data bit i at F+(6+4i)Q+2, and stop at F+38Q+2. Good
completion is observed at F+38Q+3. The two sampler stages are explicit.

The checkpoint proves the stated terminal prefix N=38Q+4 for a good frame,
N=38Q+3 for a bad stop and N=2Q+3 for a false start. These counts begin at
the armed HIGH-wait state with the falling edge at source input zero; public
edge numbering is F+N−1. A universal proof that every earlier prefix remains
BUSY was not part of this checkpoint. The finite native peers already enforced
the first BUSY drop.
The later mapped checkpoint below closes the universal earlier-prefix result
and its initialized mapped public-BUSY corollaries separately.

A false start faults without RX data. A bad stop retains the eight captured
payload bits while reporting an invalid frame. The raw MSB-first capture word
is the bit-reversed UART payload; the checked host projection reconstructs the
LSB-first chronological byte. Cold reset, all nine WRITE requests, COMMIT,
START and MARK clocks derive the armed state from arbitrary startup contents.

Bypassing one actual sampler stage advances the first BUSY drop by one edge.
It can preserve the same payload and captured bit count; the control therefore
checks the timing error directly. This is digital single-frame reception under
explicit timing assumptions; continuous back-to-back reception, clock drift,
metastability, electrical UART behavior and board qualification remain outside
this checkpoint. See the [UART contract](../protocols/streaming-uart.md).


## Mapped correspondence and earliest-BUSY checkpoint

Final source and producers: `7715ba61c9a837aa96916e823f65c8e7b6a653d9`.
This stage connects the same programmable Ready device through an actual
standard-cell mapping, package connections and Tiny Tapeout pad gates. It adds
no protocol-specific RTL, pins or host commands. The component equations hold
for every Boolean input and every packed register prestate, including all
**6,039 / 6,195 physical FF bits**. Concrete cold/upload/START proofs derive
installation from arbitrary startup contents.

The new mapping deliberately preserves source word boundaries and every state
bit. Its certificate interprets actual mapped module bodies and pinned Liberty
functions; module names and operation descriptors supply no assumed function.
All **176 word certificates**, the frontend, both cores and the complete
package/pad joins are kernel-checked. Proofs use structural reasoning and small
`decide +kernel` checks, with no `bv_decide`, `native_decide`, admitted proof or
custom axiom. Private declarations are included in the axiom audits.

| Gate | Exact committed-source result |
| --- | --- |
| Full mapped gate | PASS; `streaming-mapped-full-7715ba6-20261017-01`; 3,521.367 seconds |
| Complete-device native peers | 28 closed processes, 56 journal events and 1,025,364 wire edges; 513,297 / 512,067 at the two depths |
| Required native theorem interfaces | All 50: 44 initialized/session APIs plus six earliest-BUSY APIs |
| Complete generated proof audit | 59,755 declarations, 38,632 theorems; only `propext`, `Classical.choice`, `Quot.sound`; injected private axiom rejected |
| Python discovery | PASS; 1,682 tests, eight explicit skips; `streaming-mapped-python-7715ba6-20261017-01`; 101.548 seconds total |
| Foundation | PASS; 638 modules, 65 executable suites, eight kernel suites and 79 commands; `streaming-mapped-foundation-7715ba6-20261017-01`; 2,785.370 seconds total |
| Foundation proof audit | 43,823 declarations, 25,060 theorems; intended untrusted-axiom control rejected |
| Immutable evidence export | PASS; `streaming-mapped-export-7715ba6-20261017-01`; all 25 exported file hashes and all three raw/compressed receipts independently verified |

Each depth runs 24 selected UART cases, both long SPI/JTAG workloads and ten
I²C cases against the complete mapped device. The UART cases cover four payloads
at Q=4,12,128, framing/held-HIGH behavior, sample windows and an actual one-FF
sampler-pin mutation. This finite mapped corpus is distinct from the earlier
exhaustive UART byte corpus. Every native process records intent before launch,
its selected executable, successful closure and actual trace hash. Independent
reviews reconstructed both complete hierarchies and checked every trace's
20-byte edge records and consecutive cycle numbers.

The source earliest-terminal theorem covers every Q from 4 through 128, either
RX selector and arbitrary eight-bit payloads under its quiet-host/sample-center
premises. From the armed frame suffix with raw LOW at input zero, first terminal
prefix N is **38Q+4** for a good frame, **38Q+3** for a bad stop and **2Q+3**
for a false start. Every earlier prefix remains BUSY. An input falling at public
edge F therefore first drops BUSY at F+N−1. The mapped corollaries include actual
cold/upload/START initialization, RX0 and Q=4,12,128 at both depths, observing
public output bit 5 with the chip active and the host deselected. The six timing
APIs establish the first BUSY drop; frame data, fault prefixes and retained
custody remain separate checked session results.

| Complete proof-oriented package | Declared / physical FF bits | Combinational cells | Total cells | Cell area µm² | Unweighted gate depth |
| --- | ---: | ---: | ---: | ---: | ---: |
| Depth 2 | 6,039 / 6,039 | 28,415 | 34,454 | 717,340.9194 | 127 |
| Depth 4 | 6,195 / 6,195 | 28,909 | 35,104 | 733,797.5274 | 127 |

These larger, fully retained mappings are separate from the optimized cost rows
above. No equivalence claim transfers to those earlier netlists, and their ABC
delay numbers do not describe this mapping. Here area is the exact sum of
pinned Liberty cell areas; gate depth has no time unit. The standalone cost
receipts correctly keep `mapped_equivalence_proved=False`: the separate kernel
certificates establish correspondence. Neither artifact establishes Fmax or
physical qualification.

The [mapped evidence manifest](evidence/streaming-mapped-continuation-20261017/manifest.json)
records 25 exported file hashes. Its evidence directory contains 26 files
(4,895,486 bytes), including the manifest, 21 compact proof/log/cost/process
artifacts, the intake patch and three compressed accepted receipts.
Its SHA-256 is
`d50a079ef12df6ab4882266aeab676c2962c62bbed736e428f2612cfc286b6f4`.
The exporter independently rechecked 1,056 retained mapped artifacts, 15,425
first-use input hashes, 269 command records and a 350-module final proof closure,
plus the fresh partial raw stage, source archives and native inputs. The 64
earlier evidence files and both intake documents remain byte-identical.

Selected CAD archive membership is now verified for 1,360 CIRCT/OSS runtime
paths, including three exact relative library aliases. The old broader
`installed_payload_archive_membership_proved=False` remains false. Lean, Lake,
Python, the operating system and 12,428 other identity files have no membership
claim in those CAD archives.

Two full attempts were preserved as failures: `ed997b0` lacked built transitive
session imports, and `c60331d` exposed a global syntax collision when joining
otherwise accepted component audits. The fixes build the complete library,
preflight the 14 actual session imports and run audits without exported custom
syntax. A third attempt at `a175d1f` was stopped after read-only artifact review
found an exporter tuple/list JSON-boundary mismatch. The final repair compares
the complete canonical JSON structures while preserving types, order and all
fields; mutation controls cover meaningful changes. Failed and stopped runs
remain unqualified. All three final gates and the exporter were rerun from
`7715ba6`; no historical receipt was promoted or rewritten.

See the [mapped contract and reproduction commands](../protocols/streaming-mapped.md)
for the exact interpretation boundary, theorem inventory and fresh-run commands.
