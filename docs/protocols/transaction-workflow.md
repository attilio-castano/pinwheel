# One transaction workflow on the paired engine

The transaction API gives supported protocols one request → compile → load →
run → decode path. A transaction binds its program to named pin requirements,
timing parameters, START payload limits and result interpretation. Protocol
compilation changes writable instructions; it does not regenerate the circuit.

This is the next layer above the [named program builder](reusable-programs.md).
The builder remains available for custom, explicitly timed sequences. Independent
Lean protocol specifications and the existing hardware translation path retain
their separate responsibilities, described in [architecture](../architecture.md).

## Supported requests

From the repository root, import factories from
[`pinwheel_transactions.py`](../../scripts/pinwheel_transactions.py):

Use pinned Lean and the local runtimes described in [development](../development.md).
Prepare the production Lean imports before compiling fixed SPI or I²C requests:

```sh
lake build Pinwheel.Program.Requests
```

```python
import sys
sys.path.insert(0, "scripts")
from pinwheel_transactions import (
    compile_transaction, uart_tx, spi_transfer, i2c_register_read, jtag_scan)

uart = compile_transaction(uart_tx(bit_cycles=4))
spi = compile_transaction(spi_transfer(half_cycles=4))
fixed_spi = compile_transaction(spi_transfer([0xa6, 0x53], mode=3, half_cycles=4))
read = compile_transaction(i2c_register_read(0x50, 0x17, byte_count=2,
                                          phase_cycles=4, wait_cycles=32))
scan = compile_transaction(jtag_scan(half_cycles=4))
print(scan.inspect())
```

| Factory | Compiled request | START payload | Successful result |
| --- | --- | --- | --- |
| `uart_tx(bit_cycles=...)` | UART 8N1 transmitter | One changing byte | Empty tuple |
| `spi_transfer(half_cycles=...)` | Resident mode-0 SPI controller | One changing byte | One received byte |
| `spi_transfer(payload, mode=..., half_cycles=...)` | Fixed one/two-byte SPI transfer, modes 0–3 | Zero | Received bytes in transaction order |
| `i2c_register_read(address, register, byte_count=..., phase_cycles=..., wait_cycles=...)` | Fixed 7-bit address, 8-bit register, one/two-byte combined read | Zero | Received bytes in transaction order |
| `jtag_scan(half_cycles=...)` | Reset/navigation/eight-bit data-register scan | One changing byte | One received byte |

Durations and wait budgets are integer chip-edge counts in 1–256. SPI payload
bytes and START payloads are integers in 0–255; booleans are rejected. I²C
addresses are 0–127, registers are 0–255, and the byte count is 1 or 2. Request
objects have an exact schema and reject missing, extra and incorrectly typed
fields. Constructing a request performs no compiler or chip I/O.

Resident UART/SPI and JTAG use the Python builder and existing SHIFT/KEEP
instructions. Fixed SPI and I²C use the production
[Lean request exporter](program-export.md), which calls their existing compilers.

Construct transactions with `compile_transaction` or `Transaction.from_bytes`.
The returned object carries a private compiler-owned binding stamp for its
exact request and program. Direct construction or replacing either field with
unrelated data is rejected before chip I/O. Loading checks that stamp without
running the compiler again. This prevents accidental API mismatches; private
Python state is not a security boundary.

The public UART factory currently covers transmit. UART reception, continuous
supervision and its proved [initialized session](uart-session.md) remain available
through the [existing Host interfaces](uart-supervisor.md); they are not factories
in this transaction API.

## Load once and run with ownership

The following function accepts a transport implementing the existing
`advance(ui, cycles, rst_n=...)` interface. It keeps one UART image resident:

```python
import sys
sys.path.insert(0, "scripts")
from pinwheel_host import Host, PAIRED_FORMAT
from pinwheel_transactions import compile_transaction, uart_tx

def send_uart_bytes(transport, payloads):
    host = Host(transport, image_format=PAIRED_FORMAT)
    host.reset()
    transaction = compile_transaction(uart_tx(bit_cycles=4))
    loaded = transaction.load(host)
    return [loaded.run(payload=byte) for byte in payloads]
```

[`pinwheel_sim.py`](../../scripts/pinwheel_sim.py) supplies the RTL transport.
[`transaction_package.py`](../../scripts/transaction_package.py) constructs one
emitted paired-stream package, records source/tool/model custody and certifies
its compiled uploads. A future board transport must establish its clock,
sampling and electrical assumptions separately.

`load` requires a paired Host and commits the program. Its returned session
stores both the committed image and the Host's program generation. Reset,
low `rst_n`, raw COMMIT/RESET commands and later commits invalidate that session;
even loading byte-identical code creates a new generation. A stale session fails
before any transport operation. Rejected staging before COMMIT preserves the
previous committed image and generation. External programming through another
host is outside this software ownership tracker.

`run(payload=..., timeout_cycles=...)` validates the payload before I/O, starts
one transfer and shares a remaining wait budget between busy polling and result
readback. Fixed-data transactions reject a nonzero START payload before I/O.
The underlying Host also refuses a start while busy or while an old result is
unread. A host timeout leaves execution and retained-result ownership intact;
it does not cancel or retry the transaction.

Result decoding happens before consumption. Successful decoding consumes the
retained result and returns `TransactionResult(protocol, outcome, payload,
overrun, rejected)`. A decoding error leaves the raw packet unread for explicit
inspection with `host.read_result(consume=False)`. Retrying START cannot replace
that unread packet through this API.

UART success has `payload=()`. SPI and JTAG success return byte tuples and hide
capture-slot bit order from the caller. I²C success returns one/two bytes;
`timeout` and `nack_or_bus_fault` discard every capture, including prefix ACKs
and partial payload. Other protocols return `timeout` or `fault` with no payload.
Overrun and rejection flags remain explicit. The compact I²C result cannot
identify the exact NACK stage; [its policy](reusable-programs.md#two-byte-i²c-result-policy)
intentionally aggregates NACK and guarded bus fault.

## Compile and rebind artifacts

Requests use schema `pinwheel-protocol-request-v1`. Compiled transaction
artifacts use `pinwheel-transaction-v1` and contain exactly `schema`, `request`,
`program` and `description`. The description includes pin requirements,
payload/result widths, result layout, actual program resources and timing units.

```python
from pathlib import Path
import sys
sys.path.insert(0, "scripts")
from pinwheel_transactions import Transaction, compile_transaction, jtag_scan

output = Path("build/scan-transaction.json")
output.parent.mkdir(parents=True, exist_ok=True)
transaction = compile_transaction(jtag_scan())
transaction.write(output)
rebound = Transaction.from_bytes(output.read_bytes())
print(rebound.inspect())
```

Reading an artifact validates the request and source grammar, recompiles its
request and compares the complete program and description. It rejects request,
program and metadata mismatches, duplicate JSON fields and booleans substituted
for integers. `inspect` therefore performs compilation and admission checking;
it does not simply print saved labels. Artifact rebinding establishes agreement
with the current frontend, while kernel certificates and protocol proofs supply
their separate guarantees.

For the CLI, create `build/uart-request.json` with this request:

```json
{
  "schema": "pinwheel-protocol-request-v1",
  "protocol": "uart-tx",
  "bit_cycles": 4
}
```

Then use the same workflow:

```sh
python3 scripts/pinwheel-transaction.py compile \
  --request build/uart-request.json --output build/uart-transaction.json
python3 scripts/pinwheel-transaction.py inspect \
  --transaction build/uart-transaction.json
python3 scripts/pinwheel-transaction.py run \
  --transaction build/uart-transaction.json --payload 0xa6 --tag transaction-uart-01
python3 scripts/pinwheel-transaction.py demo --tag transaction-demo-01
```

Tags must be fresh. `run` recompiles inside the frozen package session, checks
artifact agreement, uploads and returns a decoded result. Its `--incoming 0..3`
option supplies constant external inputs; it supplies no protocol target or
independent waveform verdict. For I²C, high means release on the declared linked
open-drain wire. `demo` instead attaches independent UART/SPI/I²C/JTAG peers to
the actual resolved package wires. Reports are published only after successful
source/tool/model and generated-artifact closeout; failed attempts retain
diagnostics without an accepted report.

The standalone run's `host_run_edges` includes START framing, polling, result
readback and consumption. Protocol wire duration is measured separately by
the demo's independent peers.

## Pins, timing and bounded JTAG

Names refer to logical outputs 0–2 and sampled inputs 0–1. The current package
maps them to drive pads 2–4 and sense pads 0–1. SPI has independent MOSI/MISO;
I²C requires external drive/sense links for SCL and SDA, open-drain low/release
commands and pull-ups. See the [external interface](../engine/external-interface.md).

All timing values are chip edges. Two sampled-input registers introduce a
declared digital delay. The JTAG peer changes TDO after a falling TCK edge and
checks TDI/TMS on rising edges, following the [AMD interface convention](https://docs.amd.com/r/en-US/am011-versal-acap-trm/JTAG-Controller-Interface-Pins).
Its receive envelope is `half_cycles >= tco + 3`, including one callback edge
and two sampler edges; default half period 4 and target delay 1 meet it. This
fixture envelope does not establish a board frequency or analog sampling bound.

The scan helper drives TDI0/TCK1/TMS2 and samples TDO0. Five reset clocks recover
the TAP, followed by navigation to Shift-DR, eight LSB-first data clocks, a
final-bit TMS exit, Update-DR and idle. It takes 19 clocks, 39 half periods,
40 program positions and 9 paired parameter records. Slot 0 receives bit 0;
the decoded result is already the received byte. The target fixture assumes an
eight-bit DR selected by reset. Instruction selection, chains and 32-bit IDCODE
reads are outside this frontend.

The 39-half-period bound describes the observed wire sequence and final hold.
The public session separately requires a terminal result within its host wait
budget; the JTAG peer does not prove busy clears at that exact wire edge.

The hardware has an eight-bit START operand and sixteen capture slots. The
current JTAG frontend admits exactly eight outgoing and eight captured bits:
`jtag_scan(captured_bits=16)` is a frontend capability rejection, while a
32-bit dynamic operand or captured result exceeds the declared hardware width.
These errors are reported before chip I/O. Longer resident payloads need an
explicit data-buffer and ownership decision; sixteen captures alone do not
provide a general long-transfer API. The [finite-transfer reference model](buffered-transfers.md)
now implements that decision with separate TX/RX and retained completion,
including four-byte SPI and 32-bit JTAG witnesses. It targets a different model
interface; this paired hardware workflow retains the widths above.

## Evidence boundaries

The [accepted manifest](../../physical/experiments/unified-workflow-results.json)
binds the fresh foundation, Python, package and public CLI reports to their
source hashes and the unchanged chip artifacts.

The [package gate](../../scripts/check-transaction-programs.py) exercises all 256
resident UART/SPI/JTAG payloads on unchanged images, all sixteen initial TAP
states, fixed SPI modes/lengths, and one/two-byte I²C success, stretching, each
first NACK, timeout and guard loss. Its canonical semantic negatives distinguish
successful image certification from correct protocol behavior. The standalone
CLI's constant-input run has a narrower boundary than that gate.

Canonical SPI/I²C programs retain their reference/compiler/E64 proofs.
The typed [`Program.Resident`](../../Pinwheel/Program/Resident.lean) model combines
ordinary reactive instructions with the owned eight-bit operand.
[`ResidentProofs`](../../Pinwheel/Program/ResidentProofs.lean) covers canonical
encoding, SHIFT/KEEP entry effects, held state, ordinary-program compatibility,
reset priority and ignored busy START. Parameter capacity remains a per-image
admission check.
`PairedResidentImage.checked_trace` certifies resident source/image dispatch;
`PairedResidentEffects` proves local START/SHIFT/KEEP behavior under the actual
graph's equation premises. These local results do not compose a universal
initialized resident UART/SPI/JTAG protocol lifecycle theorem. The package peers
exercise finite declared wire scenarios independently of instruction words.

This workflow adds frontend and host interfaces without changing circuit,
emitter, SRAM, mailbox or pad logic. It does not qualify the digital pad mapping,
inherit retained physical routes or close SRAM, fast timing and package-power
gates. [Research status](../research/status.md) owns those decisions.
