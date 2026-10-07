# Reactive counted programs in buffered hardware

Decision, 2026-10-06: extend the owned counted programming contract to reactive
control before selecting its memory backend. The opt-in target is
`pinwheel-buffered-reactive32-v1`, implemented by `Hardware.Buffered.Reactive`.
SPI, JTAG and I²C are uploaded programs in the same circuit. The prior
[linear](buffered-hardware.md) and [timed counted](buffered-counted-hardware.md)
circuits retain their source and evidence.

This advances the [Jane Street protocol-emulator goal](https://blog.janestreet.com/protocol-emulator-asic-competition/):
firmware can change pin timing, direction and decisions after fabrication.
Reactive input decisions make the abstraction useful for ACK/NACK and clock
stretching. Measuring the complete implementation makes the cost of that
flexibility visible before a memory or chip decision.

## Programming and ownership

The host accepts the shared immutable `BufferedProgram`: emit, sequence and
bounded repeat, with up to 64 stored leaves, 256 syntax nodes, two nested
loops and 1,024 virtual positions. Repeats have one through eight iterations;
durations and wait budgets have one through 256 edges. DRIVE, SHIFT, KEEP,
WAIT, CHECKED, QUALIFY, HALT and FAULT all execute through generic circuitry.
SHIFT can consume a bit into a level or an enable, with inversion for open
drain. Preserved level and enable masks apply after that shift. Scratch capture
uses 16 independent control bits; RX appends use the separate owned RX buffer.

Branches mean that successful TX/RX demands cannot be inferred by adding all
source leaves. The frontend declares TX, successful RX and maximum RX demand.
All fit 32 bits; submission copies exact TX and reserves at least maximum RX.
Successful decoding requires exact successful TX consumption and RX length.
Fault and timeout expose immutable raw prefixes and scratch, without a decoded
payload. A timeout during STOP can therefore retain all 32 reply bits while
still reporting failure.

```python
from buffered_reactive_hardware import BufferedReactiveHardwareHost, compact_i2c_read
from buffered_i2c import register_read_tx

host = BufferedReactiveHardwareHost(transport)
host.initialize()
loaded = host.load(compact_i2c_read(byte_count=4, phase_cycles=4, wait_cycles=32))
pending = loaded.submit(tx=register_read_tx(0x53, 0xa6))
pending.wait(timeout_cycles=200_000)
result = pending.read()       # outcome, payload or raw prefix, scratch_bits
pending.release()
```

The same host loads `compact_spi` or `compact_jtag`. Loaded handles are reused
across payloads; each START owns its copied TX, reserved RX and retained
completion. Indexed reads preserve ownership. Host wait timeout retains the
pending handle; hardware timeout is a terminal result. Matching RELEASE frees
the slot. Reset invalidates handles, and finite identities saturate rather than
wrap. Active and retained transfers block WRITE, COMMIT and START.

Images contain the entire immutable source tree. Import re-lowers every word,
loop descriptor and absolute destination, and checks source/image identities,
geometry and demands before transport I/O. Raw parallel COMMIT checks coverage
and bounds; it does not certify a complete syntax tree. Local circuit checks
reject malformed entries before their scratch or data effects.

## Stored representation and branch timing

Each of 64 allocated rows contains a 64-bit instruction, the existing 24-bit
loop descriptor and a 56-bit branch descriptor: 144 bits per row. WRITE supplies
all three atomically. The loop descriptor keeps the
[counted layout](buffered-counted-hardware.md#source-image-and-execution).
Rollover still enters the next leaf on the dispatch edge.

| Instruction bits | Meaning |
| --- | --- |
| 2:0 | DRIVE 0, SHIFT 1, KEEP 2, HALT 3, FAULT 4, WAIT 5, CHECKED 6, QUALIFY 7 |
| 5:3 / 8:6 | Levels / enables |
| 16:9 | Duration minus one |
| 19:17 / 28:26 | Preserved levels / enables |
| 21:20 | SHIFT destination output |
| 23:22 | RX append: none 0, input0 1, input1 2; 3 invalid |
| 24 / 25 | SHIFT changes enable / inverts the consumed bit |
| 34:29 / 40:35 | Entry / terminal scratch capture |
| 42:41 / 44:43 | Check mask / value |
| 45 / 46 | WAIT input / expected level |
| 54:47 | Wait or qualification budget minus one |
| 55 | Explicit FAULT reports timeout |
| 63:56 | Reserved zero |

Capture fields encode enable bit0, input bit1 and scratch slot bits5:2.
Disabled capture fields are zero. Unused fields are canonical zero; terminal
words are exactly HALT, FAULT or timeout FAULT.

| Branch bits | Meaning |
| --- | --- |
| 1:0 | Sequential 0, absolute jump 1, scratch branch 2; 3 invalid |
| 5:2 | Scratch selector |
| 29:6 / 53:30 | True/jump endpoint / false endpoint |
| 55:54 | Reserved zero |

An endpoint uses NEXT bit0, virtual PC bits10:1, physical row bits17:11, outer
index bits20:18 and inner index bits23:21. NEXT is exactly 1. Absolute targets
are derived from the source schedule, restoring row and loop indices together.
Physical row64 is the canonical invalid absolute sentinel. Selecting it faults
after the current terminal capture. At virtual1023, any CHECKED branch arm
containing NEXT fails normalization before entry effects, even if unselected.
At smaller final source positions, falling off faults when selected instead.
Terminals may occur before later cleanup code or inside repeats.

WAIT first observes readiness on the edge after entry. Readiness wins on its
last budget edge. CHECKED tests its guard on every held edge before terminal
capture; at its terminal edge, the fresh capture feeds the branch immediately.
QUALIFY requires a consecutive ready interval, resets that interval when
blocked, and replenishes its blocked-wait budget when ready. Self branches
enter again even when physical and virtual PCs do not change. Bounded syntax
does not guarantee termination: branches may cycle, and alternating readiness
may keep QUALIFY active indefinitely. Its budget is not an overall transaction
watchdog; a host wait timeout keeps the pending transfer owned.

Entry scratch precedes TX consumption and RX append. Underflow retains that
scratch without appending; overflow retains consumed TX and the preceding RX
prefix. Held edges never repeat entry data effects. Fault/timeout restores
the program idle profile and retains the result until release. Both samplers
continue on every hardware clock, including upload and retained reads.

| Uploaded example | Leaves | Virtual positions | Uploaded bits |
| --- | ---: | ---: | ---: |
| Four-byte mode0 SPI | 4 | 66 | 576 |
| 17-bit JTAG DR scan | 20 | 58 | 2,880 |
| Four-byte I²C register read | 50 | 270 | 7,200 |

The I²C frontend has 105 total syntax nodes, sends three control bytes and
receives one through four reply bytes. NACK selects the fault STOP sequence;
clock timeout releases pins without claiming a STOP. It does not add retries
or recovery. JTAG retains its reset-selected DR assumption.

## Circuit cost and acceptance

| Declared state owner | Bits |
| --- | ---: |
| 64 packed rows | 9,216 |
| Coverage mask | 64 |
| Owned TX / retained RX | 32 / 32 |
| Other control, loop, scratch, identity and sampler state | 255 |
| Total | 9,599 |

Inline destinations give a simple upload and same-edge fetch contract. They
make this first reactive target larger than the 3,860-bit timed target.
Uploaded size is separate from allocated storage; syntax compression alone is
not an area claim. A shared destination table and SRAM are future comparisons,
with their added lookup, coverage and timing obligations included.

The target-local native emitter memoizes expression objects before traversing
their children, retaining references to prevent address reuse. Its logical
fallback remains the existing safe emitter. Small expression graphs compare
both implementations; actual typed-circuit states, emitted RTL and saved-gate
comparisons remain required. Neither emitter is universally verified. The gate
compiles the unchanged typed exporter natively and compares vectors, circuit
text and register metadata byte for byte with an interpreted five-case, 83-edge
fixture before full export; the original interpreted full export timed out and
its receipt is preserved. Scalar terminal-capture forwarding avoids constructing
the full captured scratch word
inside every branch lookup; a local Lean equality preserves the selected bit.

The [accepted manifest](../../physical/experiments/buffered-reactive-hardware-results.json)
binds hardware run `buffered-reactive-hardware-02` (1,759.371 s) and foundation
run `buffered-reactive-foundation-02` (1,534.043 s). Forty-two named local
lemmas accompany a whole-library audit of 24,105 declarations and 12,893
theorems, with standard axioms only and an injected custom axiom rejected.
The foundation builds 276 modules and passes 48 executable suites and one
kernel suite.

Actual typed reference/Python execution agrees on 143 cases and 12,240 edges.
Actual circuit states and RTL agree on all 26 public fields for 222 command
cases, 7,427 edges and 5,951 independent state expectations, including 64 raw
input histories. Emitted RTL passes 1,027 SPI, 242 JTAG and 1,042 I²C wire cases:
1,509,697 source observations, 1,366,449 active lookup/environment checks and
1,515,012 independent sampler checks. I²C fixtures cover three NACK stages,
last-budget stretch, held-clock partial RX and failed STOP qualification.
Each saved mapping passes all 222 command cases and 58 SPI/JTAG/I²C wire
cases, with 47,077 independent sampler checks. Normal and optimized Python
each discover 999 tests: 997 pass and two Linux-specific checks skip on this host.
Sampler-age, input-selection, rollover, endpoint-environment, stale-scratch,
disabled-guard, timeout-priority and mapped-output mutations are rejected.

| Complete target | Retained state bits | Generic cells | Typical cells | Summed cell area (µm²) |
| --- | ---: | ---: | ---: | ---: |
| Timed counted baseline | 3,860 | 23,638 | 20,674 | 350,479.332 |
| Reactive counted | 9,599 | 57,639 | 51,602 | 876,881.3004 |

Reactive sequential area is 470,243.4912 µm². The matched-library complete-target
area is 2.502 times the timed target's; wider packed rows account for 5,632 of
5,739 added state bits. This census includes the allocated writable bank and
ownership machinery. It does not establish routed area, clock timing or fit.

The gate binds all 270 typed I²C factory positions, including untaken fault
cleanup, to the independent frontend. It compares actual typed reference states
and circuit states, then all 26 public RTL fields. Additional fixtures cover
source-derived branch environments and pre-START input selection. Resolved-wire
SPI/JTAG/I²C peers receive only pad observations and edge numbers. The wire gate
derives an independent sampler FIFO from bridge preclock inputs on every edge.
The START model receives that pre-edge history before applying entry effects.
Stopped reference samplers are excluded from the active-engine relation;
hardware sampler state continues to be checked against the independent FIFO.

Saved generic and typical CMOS5L artifacts undergo exact state intake and
arbitrary represented-state SAT comparison of all public outputs and surviving
next-state bits. Mutation checks must reject sampler age, input selection,
rollover, branch environments and mapped outputs. These checks are local
universal equations and finite execution witnesses, without a complete
initialized compiler/package refinement or physical acceptance claim.

## Reproduction and continuation

```sh
python3 -B scripts/check-foundation.py --tag <fresh-foundation-tag>
python3 -B scripts/check-buffered-reactive-hardware.py --tag <fresh-hardware-tag>
```

The hardware gate needs the pinned Lean, CIRCT, OSS CAD and CMOS5L library/models.
`--pdk-root` accepts a standard-cell directory with `lib/` and `verilog/`.
Fresh tags preserve previous attempts. The tracked manifest binds inputs,
reports, generated artifacts and all 417 preceding hardware/physical files.
Exact generated artifacts live under ignored `build/`; retain accepted run
directories beside the tracked manifest for replay.

Next, select a memory implementation against the established entry deadlines:
one-cycle instructions, CHECKED branches, WAIT release and nested-loop exits.
Then expose versioned serial loading and retained result operations. SRAM,
FPGA/board execution, physical pads, routed timing, component qualification and
package power each retain their own evidence gate.
