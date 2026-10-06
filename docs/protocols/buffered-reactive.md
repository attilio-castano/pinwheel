# One execution model for timed and reactive buffered programs

Decision, 2026-10-06: compose buffered data effects with the existing Reactive
execution rules and a compact counted schedule. Protocols supply programs;
the engine has no SPI, JTAG or I²C dispatch cases. The
[finite-transfer ownership contract](buffered-transfers.md) still governs
preparation, execution, retained completion, release and reset.

This implements the next programming abstraction. Its target remains
`buffered-reference-v1`; it has no encoding or transport for the current chip.
The current paired hardware's operand, capture and program capacities retain
their existing contracts.

## What is shared

`Program.Buffered` normalizes its instructions into a `Reactive.Fetch.Store`
and delegates control transitions to `Reactive.Fetch.start` and `advance`.
That preserves timed holds, wait readiness, guarded actions, terminal scratch
capture, conditional successors and consecutive qualification. Owned data
effects wrap instruction entry; `Transfer` owns the TX/RX storage and completion.

The generalized `Counted.Schedule` stores emit, sequence and bounded repeat
nodes. It locates the current virtual instruction without constructing an
expanded bank. The old two-byte counted grammar embeds into this schedule;
Lean proves equal span and address lookup. Buffered instructions consume the
next owned bit instead of selecting data from the old two-byte array.

The same Python `BufferedProgram` and `BufferedEngine` now execute both the
existing linear SPI/JTAG programs and reactive counted programs. Independent
resolved-pad peers observe the waveform; they do not read programs, descriptors
or data cursors. Finite actual Lean exports are compared with this Python engine
at entry and after every represented edge. This is finite differential evidence,
not a universal Python refinement theorem.

## Entry, failure and result rules

- An instruction entry applies scratch capture, TX consumption, then RX append.
  Timed holds and blocked waits do not repeat those effects. A self branch is
  a new entry even if the numerical PC does not change.
- SHIFT can select a driven level or a drive-enable bit, with optional inversion.
  This supports push-pull data and open-drain low/release. Preservation masks can
  retain selected levels and enables across reactive phases.
- A checked action tests its guard before terminal capture or dispatch. Its
  terminal scratch capture feeds that edge's branch decision. WAIT observes
  readiness on the following edge; readiness wins at the timeout boundary.
- RX append uses the pre-edge second input-sampler register. Control scratch
  samples occupy sixteen separate slots and never enter the received-data array.
- Malformed fetch or normalization faults before entry effects. An invalid
  chosen successor faults at dispatch, preserving the current instruction's
  entry and terminal scratch effects. TX underflow faults before RX append.
  RX overflow after a successful TX consumption retains
  that consumed-bit count, restores idle and freezes the diagnostic prefix.
- Engine fault/timeout preserves the observed RX prefix and returns no decoded
  application payload. Host waiting timeout preserves the running handle.
  HALT is engine testimony; host successful decoding additionally requires the
  exact declared TX consumption and RX length. A short completion remains
  retained if decoding rejects it.

Reactive programs declare full-path TX demand, successful RX length and maximum
RX reservation separately. The host validates and copies the exact TX value and
reserves the maximum RX capacity before accepting execution. Branches can end
early with a fault and a shorter diagnostic prefix. These declarations are
admission/decoding contracts, not a theorem that an arbitrary program meets them.

## Four-byte I²C discriminator

`buffered_i2c_read` generates a combined register read: address-W, register,
repeated START, address-R, reply bytes, controller ACKs followed by final NACK,
then STOP and bus-free qualification. The loaded program is independent of the
three TX control bytes and target reply. The receive byte count is selected when
building the program, from one through eight; it is not a runtime length operand.

The default four-byte program uses:

| Quantity | Count | Meaning |
| --- | ---: | --- |
| Stored instruction leaves | 50 | Reusable pin/control/data instructions |
| Stored control descriptors | 55 | Sequence and repeat nodes |
| Total stored syntax nodes | 105 | Includes all represented control descriptors |
| Repeat nodes / nesting | 6 / 2 | Reusable byte and bit bodies |
| Virtual execution positions | 270 | Includes repeated iterations and failure cleanup |
| Quiet modeled wire edges | 993 | Observed successful fixture duration |
| TX / RX data | 24 / 32 bits | Three control bytes and four received bytes |

These are reference syntax and execution counts, not hardware word widths or
mapped area. The reference schedule permits at most 1,024 virtual positions,
256 stored syntax nodes, two nesting levels and one through eight repetitions
per repeat node. The current 256-position paired image does not accept it.

Run with `PYTHONPATH=scripts`:

```python
from buffered_i2c import buffered_i2c_read, register_read_tx
from buffered_i2c_peer import BufferedI2CReadPeer
from pinwheel_buffers import BufferedModelHost

host = BufferedModelHost(tx_capacity_bits=32, rx_capacity_bits=32)
program = buffered_i2c_read(byte_count=4)
loaded = host.load(program)
reply = b'\x96\xa5\x55\x3c'
peer = BufferedI2CReadPeer(0x53, 0xa6, reply)
result = loaded.run(tx=register_read_tx(0x53, 0xa6), peer=peer)
assert result.payload == reply
assert host.slot.state == 'free'
assert program.storage()['stored_nodes'] == 105
```

Control-byte NACKs branch through a lawful STOP sequence before publishing fault.
Clock stretching waits on the resolved clock input. A permanently held clock
can time out after a partial receive, release the controller's outputs and retain
the prefix; it does not establish STOP or bus recovery. STOP itself must qualify
both resolved lines high. A target holding SDA low can therefore retain all
32 data bits while the transfer still ends with timeout and no normal payload.

The independent peer checks open-drain ownership, board links, START/repeated
START/STOP timing, all data and ninth ACK/NACK clocks, controller final NACK,
and exact received wire prefixes. Its one-edge callback and two sampler stages
are explicit digital assumptions; no physical I²C speed grade is qualified.

## Evidence and next implementation gate

```sh
python3 -B scripts/check-buffered-reactive.py --tag <fresh-tag>
python3 -B scripts/check-foundation.py --tag <fresh-tag>
```

The focused gate builds pinned Lean, audits axioms, executes ownership and
buffered suites, compares actual exported execution states, runs all Python tests
normally and with optimization, and checks independent SPI/JTAG/I²C fixtures.
Source hashes must remain unchanged throughout the run. The
[accepted manifest](../../physical/experiments/buffered-reactive-model-results.json)
binds reports and preserves the preceding physical evidence.

The typed Lean I²C frontend is also bound to the independently wire-checked
Python factory: every virtual instruction, idle profile, demand and stored
geometry must agree, including cleanup paths that a success case does not take.
This binding covers seven scenarios for the default four-byte program with
four-cycle phases and a 32-cycle wait budget.

The Lean safety statements cover composed buffer bounds and local identity
provenance over arbitrary represented input histories. Directed and differential
tests cover timing, entry, branch and failure behavior. Independent wire checks
establish the declared finite protocol fixtures. Neither those checks nor the
ownership proofs establish emitted buffered RTL or physical timing.

The next lower layer is a versioned digital engine implementation: owned TX/RX
storage, data entry effects, counted address lookup, admission and indexed result
readback. Compare dedicated registers with an explicit SRAM partition/access
schedule, preserve exact pin and fault traces, and measure mapped cost. Live
streaming, concurrent transfers and runtime loop-count operands remain separate
extensions.
