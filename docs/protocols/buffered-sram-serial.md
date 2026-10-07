# Buffered SRAM serial command and result interface

Decision, 2026-10-07: keep the buffered SRAM programming and ownership layer and
carry its commands over a separately versioned serial boundary. Development
continues on `codex/buffered-sram-fetch`. The complete local digital acceptance
passes; initialized source/package refinement and physical qualification remain
separate.

The target remains
[`pinwheel-buffered-shared-branches32-sram64-v1`](buffered-sram-hardware.md).
SPI, JTAG and I²C programs share the same image admission, sixteen-descriptor
limit, owned TX/RX buffers and retained completion. Serial delivery changes the
host transport rather than adding protocol-specific execution hardware.

## Framing

The interface uses sampled `csn`, `sck`, `mosi` and returned `miso`, plus
`ready` for an unread command receipt. The engine clock continues during every
request and response bit. Raw protocol inputs go directly to the existing
two-stage engine sampler. Physical initialization also resets the serial
receiver; SRAM contents do not require a physical clear.

Assert CS with SCK low. Shift most significant bit first, one bit per sampled
rising SCK edge. Held high samples never repeat a bit. Close each transaction
by deasserting CS. A request contains exactly 160 bits:

| Bits | Meaning |
| --- | --- |
| 159..144 | `0xA710 \| operation`: request magic, ABI version 1, operation |
| 143..128 | Host request sequence, 16 bits |
| 127..0 | Operation payload, with all unused bits zero |

Row upload carries the complete address, instruction and metadata in one
request. An incomplete frame therefore cannot leave staged row fragments.
Wrong-length, wrong-header, unknown-operation and reserved-payload frames
never deliver a command to the engine. A complete request delivers at most
one command, after CS closes.

When `ready` rises, a separate CS transaction shifts a 192-bit response:

| Bits | Meaning |
| --- | --- |
| 191..176 | `0x5A10 \| code`: response magic, ABI version 1, receipt code |
| 175..160 | Echoed request sequence; zero for a wrong-length request |
| 159..0 | Frozen engine observation; upper five bits zero |

Receipt codes are 0 accepted, 1 wrong frame length, 2 wrong header/version,
3 unsupported operation or reserved payload, and 4 engine rejection. The
engine's combinational rejection is captured on its command delivery edge.
The remaining fields are snapshotted immediately afterward. An engine can
continue running while that receipt is being shifted out.

The whole response stays unchanged until an exact 192-bit read closes.
Aborted or overlong reads retain it for retry. While a receipt is pending,
all serial transactions read that receipt and cannot issue another command.
There is one request in flight and one held receipt. There is no automatic
START retry or automatic result release.

## Commands

Payload fields are packed from the least significant bit at the stated offset.
The header operation must match the full versioned header exactly.

| Operation | Payload |
| --- | --- |
| 0, observe/read bit | `read_index`: 5 bits at 0 |
| 1, write row | `word`: 64 bits at 0; `control`: 24 at 64; branch index: 4 at 88; `address`: 6 at 92 |
| 2, commit image | `count`: 7 bits at 0; `virtual_span`: 11 at 7; `idle_levels`: 3 at 18; `idle_enabled`: 3 at 21 |
| 3, START | `tx_data`: 32 bits at 0; `tx_length`: 6 at 32; `rx_capacity`: 6 at 38; `expected_generation`: 16 at 44 |
| 4, release | `expected_generation`: 16 bits at 0; `expected_transfer`: 16 at 16 |
| 6, write dictionary | `branch`: 56 bits at 0; `address`: 4 at 56 |
| 7, warm reset | Zero |
| 8, cold core initialization | Zero |

Operation 5 and operations 9–15 are unsupported. A cold core initialization
request preserves its own receipt. Physical initialization clears the receiver
and any pending receipt as well as initializing the engine.

This target has 32-bit TX and 32-bit RX capacity. Accepted `tx_length` and
`rx_capacity` values are 0–32; their six-bit wire fields also represent 33–63,
which the engine rejects. Host image admission checks those capacity bounds
and the declared successful data demands before upload.

The response payload packs the 26 existing engine outputs in their declared
Lean order, least significant field first: `valid`, `busy`, `retained`,
`pending`, `rejected`, `mode`, `pc`, `remaining`, `levels`, `enabled`,
`tx_consumed`, `rx_length`, `rx_data`, `read_valid`, `read_bit`, `generation`,
`transfer`, `exhausted`, `stage1`, `stage2`, `virtual_pc`, `env0`, `env1`,
`phase`, `wait_left`, `scratch`. This is 155 bits. The receipt's rejection field
uses the latched command-edge value.

## Ownership and reset

A host reconstructs and admits the canonical SRAM image before any upload I/O.
The first accepted dictionary/row write invalidates the resident image. COMMIT
requires every resident row and all sixteen dictionary slots to have been
written, including unused dictionary slots. Busy and retained transfers reject image
changes and further STARTs. Matching RELEASE frees the retained result while
keeping the loaded image available for another transfer.

Indexed reads do not consume or release the result. Completion identities,
outcome, valid RX prefix, consumed TX count and scratch diagnostics remain
stable across slow or repeated reads. Warm reset cancels the image and transfer,
advances the generation unless it is already saturated, and preserves the
transfer counter. Cold initialization clears the counters and advances the
host's software epoch, invalidating old handles.

The host reads the complete valid RX prefix from one frozen response, along
with its identity, outcome, consumed TX count and scratch diagnostics. The
indexed bit selector remains available in the wire ABI. Reading that snapshot
does not release the result.

Serial status observations cost many engine clocks. The serial host therefore
names its wait budget `timeout_polls` and reports physical edge and transaction
counts separately. A short transfer can finish before its START receipt reaches
the host. A wait timeout or uncertain transport delivery preserves the pending
owner; the host must inspect/recover that owner or explicitly reset it.

## Host API example

The backend supplies `tick(**pins)` and physical `cold_reset()`. A tick reports
the MISO value before the engine edge and READY afterward. Running this example
requires the serial package and a connected SPI peer. With `scripts` on the
Python import path:

```python
from buffered_counted_hardware import compact_spi
from buffered_sram_serial import BufferedSramSerialHost, BufferedSramSerialTransport

transport = BufferedSramSerialTransport(backend)
host = BufferedSramSerialHost(transport)
host.initialize()

loaded = host.load(compact_spi(byte_count=1, half_cycles=4))
pending = loaded.submit(tx=b"\x96")
pending.wait(timeout_polls=100)
result = pending.read()
assert pending.read() == result  # A second read keeps the same owner and result.
pending.release()

print(result.identity, result.payload, transport.physical_edges)
```

The same host operations accept JTAG and I²C `BufferedProgram` sources and
canonical SRAM images. `load` checks source/image admission before transport
I/O. `submit` establishes the generation/transfer owner; `read` takes the valid
RX prefix and completion diagnostics from one frozen receipt; `release` uses
that owner's identity. `loaded.run(tx=..., timeout_polls=...)` combines submit,
wait, read and release when the caller does not need to retain the owner.
If that convenience operation loses the RELEASE acknowledgement, its
`BufferedHardwareTransportError.result` preserves the already-read immutable
result, alongside the pending handle used for explicit recovery.

A `BufferedHardwareWaitTimeout` keeps its `pending` handle. A
`BufferedHardwareTransportError` also carries the pending handle when START
delivery is uncertain. `pending.recover()` reads the outstanding serial receipt
and checks that identity; it never resends START. After successful recovery, continue with
the same wait/read/release operations. Recovery of a known accepted RELEASE
finalizes the local owner and permits another submit on the resident image.
If a complete response was consumed but failed validation, explicit recovery
can request a fresh status observation after establishing an idle serial
boundary. It never repeats the uncertain command. An unread receipt must be
recovered or cleared by explicit initialization before another request begins.
An incomplete request or unprovable owner fails closed: recovery does not
authorize another START. Explicit initialization abandons that owner.

## Source map

| Source | Role |
| --- | --- |
| [Serial.lean](../../Pinwheel/Hardware/Buffered/Serial.lean) | Actual typed frontend expressions, register/port ABI and emitted module |
| [SerialModel.lean](../../Pinwheel/Hardware/Buffered/SerialModel.lean) | Independent Boolean/natural-number record description |
| [SerialProofs.lean](../../Pinwheel/Hardware/Buffered/SerialProofs.lean) | Local kernel laws for the actual frontend expressions |
| [BufferedSramSerial.lean](../../test/BufferedSramSerial.lean) | Ordinary typed register/port comparisons and framing/retention fixtures |
| [BufferedSramSerialExport.lean](../../test/BufferedSramSerialExport.lean) | MLIR, assembly and sampled-pin/status vector export |
| [buffered_sram_serial.py](../../scripts/buffered_sram_serial.py) | Versioned codec, transport, pending-owner recovery and host lifecycle |
| [buffered_sram_serial_reference.py](../../scripts/buffered_sram_serial_reference.py) | Independent wire schedule and frozen-receipt reconstruction |
| [buffered_sram_serial_wrapper.sv](../../physical/buffered_sram_serial_wrapper.sv) | Frontend, unchanged SRAM controller and two-macro composition |
| [buffered_sram_serial_rtl.py](../../scripts/buffered_sram_serial_rtl.py) | Public sampled-pin backend and independent protocol peers |
| [check-buffered-sram-serial.py](../../scripts/check-buffered-sram-serial.py) | Source-pinned frontend/package acceptance gate |
| [buffered_sram_serial_mapping.py](../../scripts/buffered_sram_serial_mapping.py) | Saved frontend mapping comparisons with explicit state projections |

## Recorded digital checks, 2026-10-07

Full hardware run `buffered-sram-serial-02` passes in 1,981.385 seconds from
source commit `9284120`. The [tracked acceptance manifest](../../physical/experiments/buffered-sram-serial-results.json)
binds it to the portable foundation, 722 frozen inputs, 211 generated artifacts
and 639 unchanged predecessor files. The experiment index intentionally gains
this study; its prior content remains bound to its Git blob. Report hashes and detailed command logs
belong to that manifest. Artifact hashes identify locally retained evidence
without establishing durable backup custody.

The portable foundation run `buffered-sram-serial-foundation-01` passes in
1,784.866 seconds: 288 reachable modules, 56 executable suites and one kernel
suite. Its audit checks 25,596 declarations and 13,690 theorem constants using
only the standard allowed axioms, and rejects the injected custom axiom. These
counts include generated declarations, rather than counting only named proofs.

The new serial suite compares 16,269 ordinary typed edges with the independent
record model, checking all thirteen registers and seventeen core inputs. It
includes 224 independently seeded represented states. Seventeen named local
kernel laws concern the actual frontend expressions; the complete initialized
trace theorem remains open.

The emitted frontend replay compares 69 cases and 53,775 sampled edges after
POR, including all operations, versions, framing boundaries, saturation,
backpressure and held-response retry. The native/interpreted export comparison
is byte-for-byte on one case / 1,111 edges. Complete package protocol peers pass 21
cases: nine SPI, three JTAG and nine I²C, including NACK, stretching and stuck-bus
outcomes. Their independent wire oracle checks 283,623 physical edges,
153,200 response-bit observations and all 26 fields of 400 fully read receipts.

The distinction between declared typed state and optimized mapped state is
explicit. The frontend declares thirteen registers / 389 bits. Both saved
mappings retain 370 physical FFs: fourteen declared coordinates are constants,
four are additional aliases, and the top response bit is absent from the
optimized named wire. The checked quotient accounts for every coordinate and
physical Q. SAT compares all nineteen outputs and all 370 physical next-state
bits at that optimized source boundary. It does not prove equality for all
arbitrary 389-bit typed register valuations.

The final lifecycle replay checks 262,140 physical edges, 140,581 response-bit
observations and all 26 fields of 365 completely read receipts. One additional
captured receipt is deliberately cancelled by POR before reading, and its
unobserved fields are excluded from the count. Coverage includes malformed
frames, partial/overlong reads, upload completeness, replacement, busy/retained
reset, rejected owner changes and lost START/RELEASE acknowledgements. Recovery
witnesses verify exactly one actual command delivery and resident-image reuse.

Both additional startup patterns pass three independent protocol cases and
107,064 oracle-checked physical edges each. These fixtures vary both macro
arrays and output registers before initialization; they inject no expected
response values.

| Saved frontend | Cells | Physical FF bits | Cell area, µm² |
| --- | ---: | ---: | ---: |
| Generic | 2,359 | 370 | — |
| Typical CMOS5L | 2,046 | 370 | 32,545.9134 |

The typical sequential cells contribute 18,125.8560 µm². Adding that frontend
cell area to the predecessor's 294,546.1050 µm² controller and 100,978.2656 µm²
of macro footprints gives a 428,070.2840 µm² allocation screen. The complete
mapped package has 3,521 FF bits and two 64×64 instruction arrays. These sums
exclude pads, clock tree, interconnect, placement/routing and electrical timing.

Both saved mappings pass the optimized-state SAT comparison, reject inverted
MISO and changed alias/constant controls, then pass the full 69-case frontend
replay. Each complete mapped package also passes three independent protocol
cases and 107,064 physical edges against the unchanged typed SRAM oracle.
Saved binding checks all seventeen core inputs, 26 status wires, direct raw
input passage, common clocks and both exact seventeen-port macro instances.
Driver/owner/read-index alias corruption controls reject.

Normal and optimized Python each pass 1,123 tests with two platform-specific
skips. The 64 focused serial tests include framing, codec, recovery, immutable
result preservation, public-pin I/O failure, wire oracle and binding controls.

Development receipts retain the initial compiler-output capture failure,
optimized-width/alias intake failures and the first full gate's peer-changeover
fixture failure. The accepted fixture samples one real idle edge after removing
an external peer, before the next peer interprets the bus. The SRAM controller
and execution equations stay at their accepted predecessor bytes. Exact sources
are asserted only where individual development receipts captured them.

## Reproduction

Use a fresh run tag for each gate invocation. The serial gate requires the
pinned local CIRCT/CAD tools, macro views and accepted buffered SRAM predecessor
artifacts described in [the SRAM study](buffered-sram-hardware.md). It preserves
the sampled-pin transcripts, independently reconstructed commands, frozen
receipts, source hashes and tool logs needed to inspect each comparison.

```sh
lake build Pinwheel.Hardware.Buffered.SerialModel Pinwheel.Hardware.Buffered.SerialProofs
lake env lean --run test/BufferedSramSerial.lean
python3 scripts/check-foundation.py --tag serial-foundation-local-01
python3 scripts/check-buffered-sram-serial.py --tag serial-local-01
```

## Evidence boundary

The kernel laws concern the actual typed frontend expression trees. They
establish local field decodes, command suppression, CS-close deactivation,
dispatch/capture staging, POR clearing and held-response retention under their
stated edge hypotheses. There is no universal theorem identifying every
frontend trace with the independent record model, or proving the complete
initialized serial/controller/SRAM package refinement.

Executable comparisons have a separate scope. The record fixtures compare
ordinary `Circuit.step` and `Circuit.observe` with the Boolean/natural-number
description at every sampled edge. The acceptance gate compares native and
interpreted exports, emitted frontend registers/ports after physical
initialization, and complete macro-bound sampled-pin sessions. An independent
wire schedule reconstructs delivery and snapshot edges; the unchanged typed
SRAM exporter supplies all engine fields and protocol drivers at those edges.
Independent SPI, JTAG and I²C peers check the resulting protocol traffic.
These are finite replay claims, including the exercised reset, upload and
retained-result lifecycle cases.

Saved frontend mappings use Yosys's optimized source state representation.
Their SAT comparisons cover every public output and surviving next-state
coordinate for arbitrary defined inputs and represented current state, with
omitted, pruned and derived coordinates recorded explicitly. This does not
establish equality over every arbitrary declared typed register valuation.
Post-POR typed/RTL replay and initialized package sessions address different
boundaries. New frontend mapping measurements must also be distinguished from
the predecessor controller's saved area and timing estimates.

The fixed-width sampled-pin interface assumes bits arrive as sampled. It has
no checksum and makes no claim to detect every corrupted payload. Version,
length, operation and reserved-bit checks enforce this ABI. Electrical serial
timing, clock-domain crossing and pin sampling qualification, SRAM timing,
routing and package power remain separate gates. Pinned behavioral macro
simulation establishes digital model behavior; it does not establish
electrical macro setup, clock-to-Q or interconnect timing. This serial package
has its own public ABI and has not been qualified against the older routed
chip's pad map or physical implementation.
