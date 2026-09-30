# Refine the established protocols

Authorized direction, 2026-09-29: deepen UART, SPI and I²C before adding another
protocol. The first selected capability is **SPI modes 0–3 and one- or two-byte
transfers under continuous chip select**. The completed
[local iteration continuation](local-iteration-continuation.md) remains useful
infrastructure; an activity/power bound is no longer the next local work item.

## First milestone: a wireable SPI transaction

The original SPI compiler supports one byte in mode 0. Its simulation peer
supplies MISO independently of the output driver, although the original package
maps both MISO observation and MOSI drive to `uio0`. On a physical bidirectional
pad those are the same wire. That harness establishes behavior under independent
input snapshots, but does not establish a wireable full-duplex connection.

The new digital candidate keeps logical inputs on `uio0–1` and moves the three
logical outputs and their enables to `uio2–4`. Serial upload and host-result
controls retain their existing pins. This is a fixed mapping, without a new
protocol selector, instruction or configuration register.

| Protocol | Package wiring |
| --- | --- |
| UART | TX=`uio2`, RX=`uio0` |
| SPI | MOSI=`uio2`, SCLK=`uio3`, CS_N=`uio4`, MISO=`uio0` |
| I²C | Join SCL drive `uio2` to sense `uio0`, and SDA drive `uio3` to sense `uio1`; both joined nets need pullups |

The two I²C joins are explicit board connections; open them for SPI and UART.
Their cost buys one fixed generic chip pin contract for all three protocols.
The demonstration changes its external board fixture between workloads while
keeping the RTL unchanged. Input pads and unused pads must
never be enabled by the chip. Tests resolve chip and peer drivers on actual
SystemVerilog nets and reject contention; supplying an independent input value
is insufficient for this gate.

The SPI transaction contract is MSB-first, with one or two payload bytes and
one continuous CS_N interval. Half-periods remain 1–256 logical engine edges.
For `N=8` or `16` bits, acceptance starts a half-period of setup, followed by
`2N` clock transitions and a final half-period of hold. Completion is at
`(2N+1)H`, so the respective durations are `17H` and `33H`.
CPHA=0 samples on leading edges; CPHA=1 samples on trailing edges. CPOL selects
the idle clock level. These mode meanings follow the
[Microchip transfer-mode table](https://onlinedocs.microchip.com/oxy/GUID-F5813793-E016-46F5-A9E2-718D8BCED496-en-US-15/GUID-0E901CC4-8D8D-458D-8FF5-8898F0C41259.html).
The setup/hold durations and result interface are Pinwheel choices.

## Completion criteria

| Evidence | Required result |
| --- | --- |
| Lean contract and compiler | Universal waveform, sampling and completion agreement for all modes, both lengths, all payloads and arbitrary consumed input histories; no custom axioms or unfinished proofs |
| Canonical program and upload | Existing E64 only; no more than 256 positions, 32 distinct records and 16 captures; kernel-checked paired upload certificates |
| Resolved package simulation | Independent transmit/receive values in all eight mode/length forms; continuous CS, correct sample edges, result ordering and mailbox retention; existing UART and I²C examples still pass |
| Fault controls | Old overlapping SPI assignment fails; conflicting drivers are rejected; meaningful program/RTL/proof corruptions are rejected |
| Fresh RTL meaning | Emit current core/package and check their interpretation, session correspondence and standard-axiom audits against the changed pin contract |

Logical half-periods do not establish a physical SPI frequency. The chip's
two-stage sampler observes older wire values. Resolved-peer tests must declare
their response delay and chosen half-periods; the compiler theorem over arbitrary
consumed histories is not a universal external-peripheral timing theorem.

## Next capabilities and stopping boundaries

SPI, bounded I²C recovery/write and the UART supervisor/buffer milestone are
delivered below. The next formal gate composes continuous initialized paired
package execution from the active UART-image, supervisor and SRAM premises.
Two-byte I²C reads need a separate result-ownership decision: retaining 16 data
bits plus three ACK flags needs 19 slots, exceeding the present 16-slot capture
contract. New capability scope remains within established protocols.

New protocols, SPI peripheral role, arbitrary-length bursts, FIFOs, CRC logic,
new opcodes and concurrent protocol ownership are outside this milestone.
Publication and new physical analysis retain their own action boundaries.

## Candidate identity

Local work is on `codex/spi-transaction-refinement`, based on checkpoint
`8ba6b4f` (the delivered replay/interpretation/power-request continuation).
The new package wiring creates a **new digital candidate**. Historical physical
A, its source snapshot and its manifests remain unchanged. The
[current-A replay](current-a-replay.md) deliberately rejects a different current
source inventory; use its frozen snapshot for historical replay. A new digital
receipt cannot inherit old routing, timing or electrical results by association.
No placement, route or extraction is allocated here. SRAM qualification,
compatible fast-corner conditions and package power remain the three physical
acceptance requirements, and the larger A/B design iteration remains unfinished.

## Delivered checkpoint — 2026-09-29

The first milestone is delivered locally. The
[SPI study](../protocols/spi-transactions.md) owns the timing, proof chain,
commands and limits. The additive
[manifest](../../physical/experiments/established-protocol-results.json) binds
the implementation, exact interpreted/wire-tested chip bytes, successful
receipts and preserved unsuccessful attempts.

| Gate | Recorded result |
| --- | --- |
| Lean foundation | 233 imported modules, 17,096 declarations and 8,924 theorems audited with standard axioms only; 33 executable suites, one kernel pin-map suite and the untrusted-axiom rejection pass. All 320 frozen inputs remain unchanged; 1,489.273 s. |
| Resolved SPI/package wires | Twenty SPI cases, receive-delay positive and negative controls, wrong capture-slot rejection, active-transfer reset/recovery and nine legacy cases pass. Thirty-three valid uploads have fresh kernel certificates; the malformed upload is a separate rejected control. All 253 frozen inputs and consumed copies/artifacts match; 547.180 s. |
| Fresh RTL meaning | 1,082 equalities, component/initialized-session proofs, standard-axiom audits, two unchanged controls, six RTL corruptions and two axiom injections pass. All 254 frozen inputs match; 429.635 s. Chip MLIR and RTL equal the wire gate byte-for-byte. |
| Python regression | 623 tests: 621 pass and two platform skips. All 39 focused optimized controls pass; 213 frozen inputs match; 20.584 s. |

Receipt paths and SHA-256 digests:

- `build/validation/spi-foundation-01/report.json`:
  `9fb646b2d8e33be6c647215eea65a957534cadce64c128829392bce2d90cdd10`.
- `build/host/spi-capabilities-five-pad-02/report.json`:
  `b162c9e1d3feac2ebcb5504931d21a4513fb668930223d37e8f2981c830dba96`.
- `build/validation/spi-source-readback-01/report.json`:
  `b884ea77f0e94b2e855cb5a72e31d2c86247485014e674922e4d41a78df45c6f`.
- `build/validation/spi-python-final-02/report.json`:
  `56bbec519aff5be2f51a1cb7d4c22130c9b0f7ebaaa17972a0fd758dad8e1293`.

The largest checked SPI image uses 34 positions and 20 distinct records.
The position bound is universal; dictionary capacity and paired lowering are
checked for the twenty fixtures and again per actual upload. The new reference
and compiler proofs cover uninterrupted accepted transfers. Package reset and
recovery have a separate finite RTL control. External-delay coverage remains
the declared finite peer cases, rather than a universal bound for every mode.

Failed/debug probes, an interrupted wire gate and a metadata-only regression
wrapper failure remain recorded in the
[journal](journal.md#2026-09-29--four-mode-spi-and-a-resolved-package-interface)
and manifest. The successful reruns preserve those directories. The historical
current-A replay refuses the new source inventory as intended.

All **216 preexisting manifest/fixture artifacts** match base `8ba6b4f`
byte-for-byte. Only their catalog README receives an additive documentation row.
This work adds **zero CAD seconds and zero routes**; campaign use stays at
8,843.120 seconds, with three A routes used and two B routes reserved. Generated
receipts and the portable bundle remain ignored local dependencies; tracked
hashes do not create a durable remote backup. The next capability is bounded
I²C recovery and two-payload-byte writes.

## Second delivered checkpoint — 2026-09-29

Bounded I²C recovery and one/two-payload-byte writes are delivered locally on
`codex/i2c-capability-refinement`, based on SPI checkpoint `2837d3e`. The
[I²C study](../protocols/i2c-capabilities.md) owns contracts, proof names,
commands and limits; its [manifest](../../physical/experiments/i2c-capability-results.json)
binds the exact receipts and unchanged chip artifacts.

| Gate | Recorded result |
| --- | --- |
| Lean foundation | 240 imported modules, 18,070 declarations and 9,589 theorems audited with standard axioms only; 35 executable suites, one kernel suite and untrusted-axiom rejection pass. 329 frozen inputs match; 1417.024 s. |
| Resolved I²C package wires | 11 write and 12 bus-clear cases pass, including every first-NACK position, release on pulses 1–9, stuck SDA, bounded stretching and stuck-SCL timeout. Two guarded-high fault controls, active-write reset/reload and clear→write without an intervening chip reset pass. 33 fresh kernel certificates cover 29 positive/control uploads and four canonical altered programs rejected for the intended reasons. 264 frozen source inputs, tools, models, consumed copies and generated artifacts match; 458.911 s. |
| Fresh RTL meaning | 1,082 equalities, component and initialized-session proofs, standard-axiom audits, two unchanged controls, six RTL corruptions and two axiom injections pass. 261 frozen inputs match; 361.618 s. Emitted chip MLIR/RTL equal both the wire gate and the prior SPI checkpoint byte-for-byte. |
| Python regression | 648 tests: 646 pass and 2 platform skips. All 47 focused optimized tests pass; 218 frozen inputs match; 19.764 s. |

Recovery remains an explicitly loaded program. A successful clear is consumed
before a separately loaded write starts on the same host/engine; no intervening
chip reset or automatic partial-write retry occurs. First NACK stops before any
later payload and gets its own raw ACK flag. The universal recovery bound is
nine controller release attempts, with exactly nine observed wire rises checked
under the cooperating peer assumptions.

All 217 preexisting physical manifests and fixtures match the SPI base commit.
No physical CAD or routes are added. The next local milestone is UART supervisor
and one-entry result-buffer circuitry, preserving explicit result ownership.

## Third delivered checkpoint — 2026-09-29

UART repeat supervision and explicit one-entry result ownership are delivered
locally on `codex/uart-supervisor-refinement`, based on I²C checkpoint `855fd94`.
The [UART study](../protocols/uart-supervisor.md) owns controls, delayed mailbox
phase, proof premises, commands and limits; the
[manifest](../../physical/experiments/uart-supervisor-results.json) binds exact bytes.

| Gate | Recorded result |
| --- | --- |
| Lean foundation | 243 imported modules, 18,852 declarations and 9,893 theorems audited with standard axioms only; 37 executable suites, 1 kernel suite and untrusted-axiom rejection pass. 336 frozen inputs match; 1453.859 s. |
| Resolved UART/package wires | 30 resolved UART stream cases, 148 actual-mailbox RTL vectors, 8 session controls, terminal modes 6/7, three disabled legacy protocols and 5 semantic corruptions pass. 23 fresh upload and 18 sufficient-clock certificates are kernel checked. 269 source inputs and consumed tool/model/generated bytes match; 371.490 s. |
| Fresh RTL meaning | 984 local equalities connect fresh core/package RTL to the typed circuit for all represented state and inputs; exhaustive state/output proofs and standard-axiom audits pass. Two unchanged controls, eight RTL corruptions and two axiom injections behave as expected. 555 frozen source inputs match; 1098.455 s. Wire/readback chip MLIR and RTL are byte-identical. |
| Python regression | 703 tests: 701 pass and 2 platform skips. All 89 focused optimized tests pass; 224 frozen inputs match; 23.563 s. |

Receipt paths and SHA-256 digests:

- `build/host/uart-stream-supervisor-01/report.json`: `af4a463714e1370bb200c3207c82b48e81713b16c99db3ef95c2b6c7ebcae88a`.
- `build/validation/uart-source-readback-03/report.json`: `1f3989a082e70df6ca441602bbbcbd90646e2c195ee2b22027cec94b133c2f28`.
- `build/validation/uart-foundation-01/report.json`: `c743215b04dcbef09317ad4a2138e4d4eda509b2f397f8c812324d6a46e4066c`.
- `build/validation/uart-python-final-03/report.json`: `766280a1de4331d634ff4a6bf617fc82bce42095f310bb7726a6516591b230cd`.

The old mailbox is reused with exact formal refinement. A result arrives one
edge after receiver completion; quiet automatic START on that edge reads the
old samples before clearing execution state. An unread slot preserves its old
packet and reports dropped arrivals through sticky overrun. Serial STOP/reset
retain the mailbox; external reset flushes it. Equal and unequal clock coverage
is a declared finite digital wire gate, with separate sufficient timing proofs.
The new circuit adds one enabled bit and changes chip bytes; historical physical
A does not qualify it. All 218 old manifests/fixtures match base, with zero new
CAD/routes. Universal initialized continuous-package composition remains the
next formal gate; two-byte I²C reads retain their separate capture-capacity decision.
