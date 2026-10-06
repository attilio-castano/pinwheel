# Finite transfers own their data and result

Decision, 2026-10-06: use one bounded, preloaded transaction before adding a
live stream. The host copies outgoing bits into a TX slot and reserves RX
capacity. Accepted START freezes the descriptor and transfers data access to
the engine. Terminal data stays readable until matching release.

This is an implemented **reference model**, target `buffered-reference-v1`.
It does not extend the current paired chip's eight-bit START operand or
sixteen capture bits. Existing hardware hosts reject these programs before
I/O. The [ordinary transaction workflow](transaction-workflow.md) retains its
existing circuit, upload formats, capabilities and evidence.

## Ownership contract

| Phase | Permitted operations |
| --- | --- |
| Free | Prepare a complete copied TX value and bounded RX reservation. |
| Preparing | START with matching identity and program generation. TX is already immutable. |
| Running | Engine consumes TX bits and appends RX bits. No read, release or replacement. |
| Completed, unread | Repeated host reads return frozen descriptor, status and RX prefix. No engine mutation or replacement. |
| Released | Storage is free; a later prepare allocates a different identity. |

Admission validates exact program TX demand, declared RX reservation and model buffer
capacities before execution. Low-level capacity, identity, phase, exhaustion
and generation rejections do not change any stored value. A reserved RX limit
is a maximum, not a statement that every bit was received. The engine turns
runtime TX underflow or RX overflow into a retained fault.

Lengths count bits. Protocol frontends choose byte/wire order; the generic data
path only takes the next TX bit and appends a sampled RX bit. RX data is distinct
from scratch/control captures. In particular, the current compact I²C frontend
reuses capture slots for ACK observations; those failure samples cannot be
promoted to a received-data prefix.

Python handles contain a per-slot namespace, reset epoch and sequence. This
rejects wrong-device handles as well as stale releases after reuse/reset. The
Lean model is scoped to one slot and proves local epoch/sequence provenance.
Both use nonwrapping model integers. Finite counter widths, wraparound, host
reconnection and reset persistence need a separate hardware/transport contract.

The low-level preparing phase has no abandon operation in this version; reset
is its explicit escape. Normal `submit` combines preparation and START without
an intervening caller action. Program replacement is blocked until release.

## Host API and result lifetime

Run from the repository with `PYTHONPATH=scripts`, or put `scripts/` on the
Python import path:

```python
from buffered_engine import buffered_spi
from buffered_peers import BufferedSPIPeer
from pinwheel_buffers import BufferedModelHost

host = BufferedModelHost(tx_capacity_bits=32, rx_capacity_bits=32)
loaded = host.load(buffered_spi(byte_count=4, half_cycles=4))
tx, reply = b'\xa6\x53\x81\x00', b'\x96\xa5\x55\x3c'
result = loaded.run(tx=tx, peer=BufferedSPIPeer(tx, reply))
assert result.payload == reply
assert host.slot.state == 'free'
```

`submit(tx=..., rx_limit=..., peer=...)` returns a pending handle. TX accepts
bytes, bytearray or memoryview and is copied before acceptance. The handle's
`wait(timeout_cycles=...)`, `read()` and `release()` separate execution,
inspection and storage reuse. `read` does not consume anything. `run` waits,
copies/decodes an immutable result, then releases storage. A decode error
preserves the unread completion. Returned bytes and diagnostic bits survive
later slot reuse.

`BufferedResult` carries transfer identity, program key/generation, protocol,
terminal outcome, TX bits consumed, RX valid bit count, successful payload or
`None`, and raw diagnostic RX bits. **TX consumption is not proof that a peer
clocked or accepted those bits.** SHIFT consumes on entry, before a possible
later peripheral clock edge. Protocol ACKs and external effects need their own
observations.

Failure and recovery rules:

- A `HostWaitTimeout` contains `.pending`. It stops waiting, leaving the same
  engine, peer, data and identity intact. Call `.pending.wait()` again; no
  automatic START, reset or replay is issued.
- Engine fault/timeout returns no normal payload, but retains the exact RX
  prefix and its count. Reading or copying a diagnostic result does not imply
  that external partial writes can be rolled back.
- A `BufferedExecutionError` carries `.pending` and `.cause`. A fixture failure
  while running ends the local engine with a retained fault. If the callback
  fails after completion was already published, that completion remains
  immutable; the raised observation error is separate from engine outcome.
  Such a run is not accepted wire evidence.
- Reset flushes the slot and invalidates all old loaded and pending handles.
  There is no execution-cancel/cleanup instruction in this first model.

## Generic programs and independent witnesses

`BufferedProgram` is immutable and hashes its target, protocol interpretation,
wire order, idle profile and every instruction field. Its generic timed
operations drive pins, consume a TX bit, preserve outputs, append a sampled
input bit, or finish. The engine has no protocol cases. The
[shared reactive continuation](buffered-reactive.md) now adds waits/guards,
scratch branches, qualification and compact counted schedules to this same
Python engine and composes the effects with Reactive/Fetch in Lean. The SPI/JTAG
programs below retain their linear schedules and wire timing. Circuit encoding
and integration remain separate.

| Frontend | Data and timing contract |
| --- | --- |
| `buffered_spi(byte_count=4, half_cycles=4)` | Mode 0, bytes in request order/MSB first, one continuous CS assertion. Four bytes take 260 modeled wire edges. |
| `buffered_jtag(bit_count=32, half_cycles=4)` | Reset, navigate to Shift-DR, LSB-first scan, last-bit exit, Update-DR and idle. Thirty-two bits take 348 modeled wire edges. |

For JTAG, a scalar uses little-endian byte carriers:
`value.to_bytes((bit_count + 7) // 8, 'little')`. Non-byte scans reject nonzero
unused carrier padding and send no padding clocks. The independent target
fixture assumes a DR of the requested width selected by reset; it is not a
general IR selector, scan-chain discovery tool or IDCODE implementation.

Independent peers see only resolved physical pads and integer edge counts.
The fixture maps outputs to pads 2–4 and inputs to 0–1, applies peer drives on
the next edge and samples through two registers. The receive timing premise
is `half_cycles >= peer_tco + 3`. Default H4/tco1 meets it. These are explicit
digital fixture delays, not a qualified physical clock frequency.

Tests move sampling late, release CS between bytes, remove final-bit TMS and
change bit order. These must fail the independent oracle even when a mutated
program has a valid descriptor or reaches engine completion.

## Evidence and reproduction

```sh
python3 -B scripts/check-buffered-transfers.py --tag buffered-model-01
python3 -B scripts/check-foundation.py --tag buffered-foundation-01
```

Choose fresh tags on subsequent runs. The buffered gate builds current source,
audits axioms, runs the Lean ownership suite, compares actual Lean-exported
transitions with Python, runs all Python tests normally and under `-O`, then
records independent SPI/JTAG wire witnesses. It checks source hashes again
before publishing a success report. The foundation includes `test/Transfer.lean`.

`TransferProofs` proves per-step and arbitrary finite-history bounds and identity
provenance, exact consumption/append, immutable completed records, rejection,
matching release, reuse and reset. These are ownership proofs; `.complete`
is engine testimony, not a theorem about protocol success. Differential
execution establishes agreement on its finite vectors, not a universal Python
refinement theorem. The [result manifest](../../physical/experiments/buffered-transfer-model-results.json)
binds accepted reports and preserves the earlier hardware evidence.

## Hardware continuation and cost

The first model uses 32 TX and 32 RX bits: **64 data bits before metadata,
counters, selection, readback and control**. This is a storage floor, not a
mapped area estimate. Capacity is a parameter, not a selected silicon size.
Retained RX would remain in place; the completion would describe it rather than
copying an entire buffer into a second mailbox.

The existing single-port 512×64 SRAM allocates all 512 rows to two atomic program
banks and supplies an instruction response each execution edge. Borrowing it
requires an explicit partition and proved access schedule. Dedicated data
registers avoid that contention but add storage and selection cost. Neither
option has been synthesized or routed for this model.

The next implementation should connect ownership admission, TX consumption,
RX append and indexed readback to the retained programmable engine, with a
versioned encoding. All eight current instruction kinds and the serial
receiver's three-bit command space are occupied. Merely widening capture slots
also spends distinct parameter records; an RX cursor avoids a parameter per
data bit. New START admission must protect unread RX storage in hardware: the
current mailbox preserves an old copied packet while permitting later core
execution, whereas a retained buffer must also preserve the bytes it names.

A small first circuit discriminator is dedicated 32-bit TX/RX storage with the
existing instruction SRAM schedule preserved. A separately versioned token
grammar could reuse currently reserved token bits 30–31 for RX-append enable
and input selection, retaining SHIFT as TX consumption and the existing timing
fields. Current validators require those bits zero; this is a proposed new ABI,
not an admitted existing image. Framed host subcommands also need a real receipt
pulse; the core's ordinary no-command value cannot double as a delivered frame.
Compare mapped cost and exact entry effects before choosing this organization.

The current unrolled two-byte I²C program uses 196 positions; two more byte/ACK
groups in that schedule would reach 268, exceeding 256. The
[reactive continuation](buffered-reactive.md) implements reusable counted bodies
in the reference model, with stored syntax distinct from virtual positions.
Hardware still needs an encoding and lookup implementation for that schedule.
Live streaming, concurrent transfers and double buffering remain separate
throughput decisions.
