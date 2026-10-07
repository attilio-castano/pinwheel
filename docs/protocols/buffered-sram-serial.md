# Buffered SRAM serial command and result interface

Decision, 2026-10-07: keep the buffered SRAM programming and ownership layer and
carry its commands over a separately versioned serial boundary. Development
continues on `codex/buffered-sram-fetch`. This document initially records the
interface contract; acceptance measurements will be added after validation.

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
| 159..144 | `0xA710 | operation`: request magic, ABI version 1, operation |
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
| 191..176 | `0x5A10 | code`: response magic, ABI version 1, receipt code |
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
requires complete upload coverage. Busy and retained transfers reject image
changes and further STARTs. Matching RELEASE frees the retained result while
keeping the loaded image available for another transfer.

Indexed reads do not consume or release the result. Completion identities,
outcome, valid RX prefix, consumed TX count and scratch diagnostics remain
stable across slow or repeated reads. Warm reset cancels the image and transfer
while preserving generation/transfer counters. Cold initialization clears the
counters and advances the host's software epoch, invalidating old handles.

Serial status observations cost many engine clocks. The serial host therefore
names its wait budget `timeout_polls` and reports physical edge and transaction
counts separately. A short transfer can finish before its START receipt reaches
the host. A wait timeout or uncertain transport delivery preserves the pending
owner; the host must inspect/recover that owner or explicitly reset it.

## Evidence boundary

The fixed-width sampled-pin interface assumes bits arrive as sampled. It has
no checksum and makes no claim to detect every corrupted payload. Version,
length, operation and reserved-bit checks enforce this ABI. Electrical serial
timing, pin sampling qualification, complete initialized package refinement,
SRAM timing, routing and package power remain separate gates.
