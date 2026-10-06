# Reusable programs and bounded register reads

The protocol engine can keep one UART transmitter or SPI controller program
resident while each accepted `START` supplies a new byte. A named Python
builder exposes the existing action, wait, capture, guard, branch, SHIFT and
KEEP instructions. A separate Lean frontend compiles one/two-byte I²C register
reads into the same paired engine.

This advances the [competition goal](../competition.md) of programming new pin
behavior after fabrication: protocol code, payload and target circuitry have
separate interfaces. No controller, emitter or pad circuitry changes in this
checkpoint. The current five-pad mapping still limits available simultaneous
signals. Timings are chip edges; a board transport must establish sampling and
electrical assumptions separately.

## Program an unchanged chip

From the repository root:

```python
import sys
sys.path.insert(0, "scripts")
from pinwheel_host import Host, PAIRED_FORMAT
from pinwheel_program import resident_uart, resident_spi, resource_report

host = Host(transport, image_format=PAIRED_FORMAT)
host.reset()
program = resident_uart(bit_cycles=4)
print(resource_report(program))
host.upload(program)
for byte in (0x00, 0xff, 0xa6, 0x53):
    host.start(payload=byte)
    result = host.read_result()  # reads and consumes the retained result

host.upload(resident_spi(half_cycles=4))
host.start(payload=0xa6)
reply = host.read_result()
```

`transport` implements the existing `advance(ui, cycles, rst_n=...)` interface.
[`pinwheel_sim.py`](../../scripts/pinwheel_sim.py) provides the RTL transport.
UART uses 8N1/LSB first, 40 execution edges at this timing. Resident SPI uses
mode 0/MSB first, eight rising/eight falling edges and 68 execution edges. Its
raw receive slots are in MSB-first wire order, so bit reversal decodes the byte.
The established [SPI transaction compiler](spi-transactions.md) continues to
provide modes 0–3 and fixed one/two-byte transfers.

An upload uses `pinwheel-resident32-v1` source records and lowers to the existing
290-word paired hardware ABI. Canonical `pinwheel-e64-v1` and
`pinwheel-paired32-v1` retain their previous grammar. SHIFT and KEEP are admitted
only in the resident source format; the legacy hardware rejects this format.
`start()` still defaults to zero. Payloads must be integers 0..255 and a nonzero
payload requires paired hardware.

The host checks result ownership before `start`: consume the previous result
first. A raw START during execution does not replace the owned payload. A raw
START with an unread result can run and set the existing sticky overrun; the
core has no new hardware mailbox backpressure. Incomplete START frames cannot
begin a transfer. A rejected staged upload requires explicit ABORT before
continuing; `Host.upload` handles this recovery.

## Name pins, captures and control flow

```python
from pathlib import Path
import sys
sys.path.insert(0, "scripts")
from pinwheel_program import ProgramBuilder, resource_report

builder = ProgramBuilder(
    outputs={"pulse": 0}, inputs={"ready": 0}, captures={"decision": 0})
builder.wait("ready", True, budget=32)
builder.checked(2, terminal_capture=("ready", "decision"),
                branch=("decision", "emit", "done"))
builder.label("emit").action(4, high=("pulse",), enabled=("pulse",))
builder.label("done").halt()
program = builder.build()
print(resource_report(program))
output = Path("build/trigger.json")
output.parent.mkdir(parents=True, exist_ok=True)
program.write(output)
```

Run this custom image in the RTL transport with a ready input:

```sh
python3 scripts/pinwheel-host.py run --backend paired-stream \
  --program build/trigger.json --incoming 1 --tag trigger-ready
```

It returns capture slot 0 set and a completed result. With `--incoming 0`, the
bounded wait instead returns timeout with no captures. Both use the same image.

Output names map to three
logical drive pins; input names map to two sampled inputs. They are not package
pad numbers. Captures name sixteen slots. Durations/budgets are 1..256 chip
edges. Labels resolve at build time, and the complete image is validated before
I/O. The resource report gives actual position, source-record, parameter and
capture usage. Paired resident programs have 256 positions and 32 parameter
records; the resident source does not borrow E64's 32-record dictionary bound.

SHIFT takes the pre-shift operand's selected LSB/MSB, installs it on one output,
and shifts once on instruction entry. Held edges preserve operand and output.
KEEP replaces the declared literal output bits while preserving bits selected
by its mask; its optional input capture executes on entry. Both use existing
paired circuitry.

## Two-byte I²C result policy

[`RegisterReadTransaction`](../../Pinwheel/I2C/RegisterReadTransaction.lean)
specifies a 7-bit address, an 8-bit register and one/two received bytes. The
compiler sends address+W, register, repeated START, address+R, receives data,
ACKs the first byte of a two-byte read, NACKs the final byte and emits STOP.
Each of the three prefix NACKs takes a qualified STOP path.

The success result uses all sixteen capture bits for payload. Prefix ACKs
temporarily reuse slots 0..2, which are overwritten only after all prefix ACKs
succeed. `.completed` means payload; `.timeout` means the bounded wait expired;
`.fault` means NACK or guarded bus fault. The NACK path ends with a sequential
instruction past `last`, deliberately producing structural fault after STOP.
An exact NACK stage remains in the reference diagnostics, not the public result.
The earlier precise-ACK [one-byte frontend](../../Pinwheel/Compile/I2CRead.lean)
is unchanged.

```python
from protocol_results import i2c_read_result

decoded = i2c_read_result(raw_result, byte_count=2)
if decoded.outcome == "success":
    first, second = decoded.payload
```

Supply the byte count of the committed read program. On success, slots 0..7 and
8..15 are the first/second byte in MSB-first wire order. On every failure the
decoder discards all captures; partial data or ACK flags cannot become payload.
Overrun/rejection remain explicit. There is no automatic retry.

Both sizes occupy 196 positions, including their alternative paths. The checked
fixture images use 32 canonical E64 records and 23 paired parameters, including
padding. Do not infer unused dictionary reserve from the 60 unused positions.

## Evidence and reproduction

Use pinned Lean on PATH and the bundled CIRCT/Icarus packages and pinned SRAM
behavioral models described in [development](../development.md).

```sh
python3 -m unittest discover -s test -p 'test_*.py'
python3 scripts/check-foundation.py --tag reusable-foundation
python3 scripts/check-resident-image.py --tag reusable-images
python3 scripts/pinwheel-host.py resident-demo --backend paired-stream --tag reusable-pins
python3 scripts/check-i2c-read-transactions.py --tag read-pins
python3 scripts/check-paired-readback.py --mode fresh --tag reusable-readback
python3 scripts/check-stream-readback.py --tag reusable-stream-readback --proof-timeout-seconds 1800
```

Tags must be fresh. Each package gate freezes source/tool/model inputs, certifies
its actual uploads in the Lean kernel, emits a chip, observes resolved package
pins and checks unchanged custody at closeout. Failed probes retain diagnostics
and cannot produce an accepted report. The [tracked checkpoint](../../physical/experiments/reusable-protocol-results.json)
binds the final receipts and artifact identities.

### Recorded checkpoint — 2026-10-06

| Gate | Result |
| --- | --- |
| Foundation | 261 modules, 20,800 declarations and 11,224 theorems audited with standard axioms only; 41 executable suites, one kernel suite and the untrusted-axiom rejection pass. |
| Python | 740 passes and two Linux-only skips; 34 new tests also pass with assertions disabled. |
| Resident source and nodes | Two positive source certificates and eight proved corruption rejections; 4,608 SHIFT and 640 KEEP typed graph cases, including periods 1, 4 and 256. |
| Resident package | All 256 UART and 256 SPI payloads, 19 control cases, two certified semantic negatives and five upload certificates pass. The actual CLI carries `0xa6` through the same UART image and chip bytes. |
| Named program | One four-position ready/branch/pulse image completes with capture 1 when ready is high and times out with capture 0 when low, through the actual CLI. |
| I²C package | Sixteen one/two-byte scenarios, all three first-NACK stages, stretching, timeout, reset/reload and guard loss; four certified semantic negatives and 23 upload certificates pass. Success uses 36/45 clocks; prefix NACK uses 9/18/27. |
| Paired RTL interpretation | 1,082 local equalities, complete core/package proofs, standard-axiom audits and corruption controls pass on a fresh source emission. Its chip MLIR/RTL match the I²C package gate byte-for-byte. |
| Stream RTL interpretation | 984 local equalities, complete core/package proofs, standard-axiom audits and corruption controls pass on a fresh source emission. Its chip MLIR/RTL match the resident package and CLI gates byte-for-byte. |

The final closeout rechecks 601 source inputs across ten reports and preserves
all 231 historical physical files. The interrupted source-freeze attempts and
the failed 600-second stream proof are retained separately; the accepted fresh
stream run uses a recorded 1,800-second per-module compilation bound. Increasing
that bound changes neither generated proofs nor acceptance checks.

`PairedResidentImage.checked_trace` proves the raw source's dispatch sequence
matches its certified paired image for every finite successor-choice history.
`PairedResidentEffects` proves local START/SHIFT/KEEP node behavior in the actual
graph under its equation premises. These do not yet compose a universal
initialized resident UART/SPI lifecycle theorem. Package tests cover all 256
UART/SPI payloads and ownership/reset/mutation controls. The I²C compiler has
universal reference/engine/E64 refinement; package scenarios cover declared
reply bytes, each first-NACK stage, timing, stretching, timeout and guard loss.

Physical A remains blocked on SRAM qualification, compatible fast timing and
package power. These software capabilities do not qualify the five-pad digital
candidate or inherit retained A's route. The next flexibility experiment can
use a JTAG waveform to test generic sequencing and capture without adding
protocol circuitry, followed by a new independent pin peer. Longer resident
payloads require a separate buffer/ownership design decision.
