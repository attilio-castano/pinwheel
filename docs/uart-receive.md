# One-byte UART receive

Implemented 2026-09-15. UART now has a receive model and a compiler for the shared
reactive engine, alongside the existing [transmitter](uart-model.md). The first
receive contract is one 8N1 byte: eight data bits, no parity, one stop-bit sample.
It reuses existing instructions, storage, and loading interfaces.

## Interface and timing

`UART.Rx.Config` selects an input (`Fin 2`) and an integer bit period `B` from
8 through 6656 engine cycles. This is a digital timing parameter; it does not
qualify any physical clock frequency or baud rate. The receiver takes one sample
at each designated center, with no majority voting.

1. `start` arms the receiver and clears all samples. That edge consumes no input.
2. Observe high, then low on a later edge `d`. An initially low line stays armed
   until a high observation followed by a low observation occurs.
3. At `d + H`, where `H = floor(B / 2)`, confirm that start is still low. A high
   observation rejects the candidate and returns to waiting for high.
4. Capture eight data bits, least significant first, then sample stop.
5. Complete at the stop sample and retain the result until reset, rearm, or an
   accepted replacement program. Completion does not wait for the end of stop.

| Observation | Engine edge | Sample slot |
| --- | --- | --- |
| Idle/start search and start confirmation | Search edges, then `d + H` | 8 |
| Data bit `k`, for `k = 0..7` | `d + H + (k + 1) × B` | `k` |
| Stop | `d + H + 9 × B` | 9 |

Slots 10–15 remain untouched by receive instructions. Every instruction releases
all three outputs; receive mode does not drive the transmitter pin high.

`Compile.UARTRx.result` interprets completed samples as either `Outcome.byte value`
or `Outcome.framingError value`. A low stop sample produces the latter while
retaining the eight sampled data bits. The existing RTL exposes the sample bank
and completion state; this change adds no dedicated byte FIFO or status port.

Reset aborts reception and overrides start. Start and load attempts while busy
are ignored/rejected under the existing engine/loader contracts, including on
the completion edge. A stopped start clears the preceding result and rearms.
There is no wait deadline: an absent sender leaves the receiver busy indefinitely
until reset. A low line does not repeatedly complete zero-valued frames.

## Timing premise and error boundary

The input is an already sampled, two-state digital signal. `SamplesFrame` requires
each designated data/stop observation to equal the transmitted bit. Start detection
and midpoint confirmation have separate premises. The full armed theorem also
requires a sampled high prefix before the detected low edge.

Transmitter and receiver periods may differ if those sampling premises hold. The
tests use fractional sender edges and differing periods and explicitly check the
sample windows. They do not establish a universal percentage tolerance, jitter
budget, metastability bound, or physical input latency.

The subsequent [UART link milestone](uart-link.md) derives these sample premises
from the actual TX waveform, independent clock parameters, and a bounded digital
observation-age contract. It proves sufficient timing bounds and composes through
both compilers. Physical satisfaction of the age contract remains a separate
obligation.

A candidate is rejected when its start midpoint is high; this is not a guarantee
against every possible glitch. Only the stop sample is validated, not the entire
stop interval. Arming in the middle of another frame does not guarantee immediate
framing recovery: a data transition can resemble a start edge.

## Repository integration

| Owner | Responsibility |
| --- | --- |
| [RxSpec.lean](../Pinwheel/UART/RxSpec.lean) | Configuration, independent frame/event specification, sample times, byte assembly, outcome |
| [Rx.lean](../Pinwheel/UART/Rx.lean) | Protocol phases and a whole-symbol countdown, independent of instruction addresses |
| [RxProofs.lean](../Pinwheel/UART/RxProofs.lean) | Start detection, countdown/sample boundaries, byte recovery, reset and request contracts |
| [UARTRx.lean](../Pinwheel/Compile/UARTRx.lean) | Compiler to `Reactive.Program 255 15` |
| [UARTRxProofs.lean](../Pinwheel/Compile/UARTRxProofs.lean) | Exact state/step/run correspondence, including split delays and control requests |
| [Hardware/UARTRx.lean](../Pinwheel/Hardware/UARTRx.lean) | E64 words and certified 32-record lowering; decoded execution correspondence |

Search uses one-cycle `checked` instructions with terminal capture and a branch
on slot 8. Existing terminal-capture forwarding supplies the branch's current
observation. Timing uses `action` chunks followed by a `checked` capture; a short
first chunk and subsequent 256-cycle chunks preserve the exact total duration
without adding boundary cycles. A halt completes the byte. No new opcode, engine
register, scheduler, or circuit is introduced.

The largest accepted period uses 250 of 256 addresses, including halt. The finite
capacity sweep covers **all 13,298 configurations** (6649 periods × two inputs):
every image encodes canonically, survives the 55-bit dense roundtrip, and lowers
to the existing 32-record dictionary with a certificate for all 256 lookups.
The maximum observed dictionary size is **16 records**. The compiler's address
bound is also proved symbolically. Period 6657 would require too many addresses
under this layout, so it is rejected at configuration construction.

The receive program uses the wide E64 path. PWL version 0 retains its existing
128-address/eight-sample limits and cannot directly represent this program.
The atomic loader continues to accept synchronous host words; application-byte
reception does not turn UART into a program-loading transport.

TX, RX, SPI, and I²C share one execution stream and can replace one another when
stopped. TX and RX are separate programs. Simultaneous independent TX/RX requires
an explicit scheduling/resource design. Continuous receive additionally needs
result buffering and overrun semantics; host rearming of this one-byte program
does not guarantee lossless back-to-back reception.

### Constructing a program

```lean
import Pinwheel

def receiveConfig : Pinwheel.UART.Rx.Config :=
  ⟨434, by decide, by decide, 0⟩

def receiveProgram := Pinwheel.Compile.UARTRx.program receiveConfig
def receiveImage := Pinwheel.Hardware.UARTRx.compact receiveConfig
```

For runtime parameters use `UART.Rx.Config.ofCycles`, which rejects unsupported
periods. `compact` returns an optional image carrying lookup equality; callers
must handle rejection using the same load-time capacity boundary as other programs.

## Proofs and executable checks

The central protocol theorem, `UART.Rx.armed_frame_correct`, recovers the byte
from the armed interface under the stated start and sample premises.
`Compile.UARTRx.byte_correct` carries that result through compiled execution.
`step_simulation` and `run_simulation` establish complete state equality with the
independent receiver for well-formed states and arbitrary input observations;
`step_simulation` includes reset/start requests. The decoded-store theorems compose
with the existing fetch and storage proofs. They do not prove the emitter or CIRCT.

```sh
lake build
lake env lean -DwarningAsError=true --run test/UARTRx.lean
python3 scripts/check-uart-rx.py
```

[UARTRx.lean](../test/UARTRx.lean) covers every byte at periods
8, 9, 16, 255, 256, 257, and 434 on both inputs (3584 frames), decoded and dense
compact execution at representative and maximum periods, fractional sender timing,
all-byte framing errors, initial-low and false-start cases, reset/rearm/replacement,
and arbitrary reset/start/input histories. Four corrupted programs must fail the
waveform/result checks: wrong delay, reversed data destinations, missing stop
capture, and swapped input. The Python checker consumes only compiled E64 images;
its independent sender and interpreter check 64 good/bad-stop frames across four
periods and both direct/indexed stores, including 5208 and 6656 cycles.

The [foundation gate](validation.md) includes this suite, the Python oracle,
whole-library import reachability, and the standard-axiom audit. Detailed counts
and source identities belong to its fresh tagged receipt and the receive reports
under `build/uart-rx/`.

### Core, loader, and default storage

The existing mixed-protocol fixtures now exercise nine receive scenarios after
I²C on the same loaded instance, covering both inputs, split delays, rearm, false
starts, framing errors, and ignored busy writes/commands. The focused runner
regenerates fixtures and structural components, then simulates direct, indexed,
atomic indexed, and the default **32-record dense cached** RTL. It also checks the
default cache invariant and requires a held-cache mutation to fail.

```sh
python3 scripts/check-uart-rx-hardware.py --tag receive-first-check
```

This requires the [pinned hardware tools](development.md). An existing local tool
directory can be selected with `--tools /absolute/path/to/build/tools`. A fresh
tag retains source hashes, copied fixtures, generated RTL, logs, and a success
receipt under `build/uart-rx/hardware/<tag>/`. Run hardware fixture generators in
one checkout sequentially: their shared `build/loader` and `build/reactive-core`
locations are overwritten before being copied into the tagged receipt.

This runner establishes finite structural/RTL integration evidence. It performs
no synthesis or routing and does not replace the frozen timed-contract comparison
fixtures. The existing physical timing failure and wrapper obligations remain.

### Recorded validation

The portable `uart-rx-01` gate passed all **21 executable suites**, both Python
oracles, import reachability for 108 modules, and the whole-library standard-axiom
audit (9274 declarations, including 4851 theorems). The injected custom axiom was
rejected. Counts include generated declarations. The receive suite passed 3584
exact-clock, 80 backend, 336 fractional-clock, and 768 bad-stop frames; 60 sender
timing combinations were explicitly outside the sampling premise. All four
program mutations were rejected. The gate took 708.568 seconds.

Portable receipt: `build/validation/uart-rx-01/report.json`, SHA-256
`e1604250db30252bb8ef22fe68dce5c058420c2a4857aaef593cb314b6dec1c8`.

The 2026-09-15 `uart-rx-01` hardware run, based on `c133af9` plus the receive
changes, passed with the pinned Lean/CIRCT/Icarus tools:

| Backend | Compared edges | Additional checks |
| --- | --- | --- |
| Direct reactive core | 34,379 total; 34,119 checked states | Structural Lean evaluation and emitted RTL |
| Indexed reactive core | 38,539 total; 38,215 checked states | Structural Lean evaluation and emitted RTL |
| Atomic indexed loader/core | 27,096 | Structural components and RTL; 16,813,480 store observations |
| Default 32-record dense cached loader/core | 27,096 | RTL, cache invariant, and 16,813,480 logical store observations |

Each path includes nine UART RX scenarios within the existing mixed-protocol and
loader/control cases. Direct/indexed setup has an explicitly unobserved interval
before initialization. Small-store observations include the fixed halt padding
for the absent dictionary entries. The held-cache RTL mutation was rejected.
The run took 247.881 seconds, with the portable gate running concurrently.

Hardware receipt: `build/uart-rx/hardware/uart-rx-01/report.json`, SHA-256
`66c7c37dc8d659939dc9666b94c11c7d4130cd34aeb1a0ab357270acf518a496`.
It retains hashes of every relevant source, copied vectors, generated modules,
testbenches, and tool binaries. Ignored artifacts identify this local run; the
commands above regenerate new evidence if those artifacts are unavailable.

## Subsequent receive work

The [UART link proof](uart-link.md) supplies the digital clock/latency relationship
and end-to-end one-byte theorem. A concrete asynchronous-input wrapper must still
justify that contract. The [continuous receive model](uart-stream.md) now adds
successive ideal frames, result ownership, buffering, and overrun through a Lean
supervisor. Its circuit realization and concurrent TX/RX still need implementation
and resource designs with their own evidence.
