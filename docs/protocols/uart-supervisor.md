# UART receive supervisor and retained results

The September 30 [initialized package session study](uart-session.md) now
composes this candidate through actual reset, certified upload, delivered ARM,
resident execution and certified reset/reload boundaries. The circuitry and
September 29 evidence below remain the original supervisor checkpoint.

This local continuation of the [established protocols](../research/established-protocol-continuation.md)
adds an explicit repeat supervisor to the paired controller. Work starts from
the I²C checkpoint `855fd94` on `codex/uart-supervisor-refinement`. The existing
UART receiver, E64 instructions, paired upload format, two-stage pin sampler
and one-entry host mailbox are reused. One new state bit owns the repeat session.

## Control and ownership

Serial host command **6** has two exact payloads. Payload **1** arms and starts
the committed program when the engine is stopped, the image is valid, no upload
is staged and streaming is disabled. An unread mailbox does not prevent arming.
Payload **0** stops, aborts incomplete execution and any staged upload, and
leaves the committed image and unread mailbox intact. Other payloads are rejected. This command does not
infer the loaded protocol: the host must deliberately load a UART receive image.

While enabled, the supervisor reserves the engine through both execution and
the stopped edge between frames. BEGIN, PUSH, COMMIT, ABORT and manual START
are rejected, preserving the image. On a quiet command edge after normal
completion (engine mode 5), it injects an ordinary START with payload zero.
Buffer fullness never delays rearming. Timeout/fault modes 6/7 disarm instead
of retrying. Bad UART stop bits still reach engine mode 5 and therefore rearm;
the host identifies the framing error from captured stop slot 9.

External reset and serial RESET command 7 disarm. Serial reset and STOP reset
execution while preserving the retained result. An accepted COMMIT while
disabled also preserves that result. External `rst_n` resets and flushes the
mailbox through its existing reset/release contract. A serial control command
can delay a rearm edge; uninterrupted frame-timing claims require quiet commands.

| Result event | Buffer action |
| --- | --- |
| Empty, new completion | Retain the new result |
| Unread result, new completion | Preserve the old result, drop the new arrival, set sticky overrun |
| Consume and completion together | Deliver the old result and retain the new arrival |
| Consume an empty slot and completion together | Retain the arrival; no same-edge bypass to the consumer |
| Clear and drop together | The drop sets overrun again |
| External mailbox reset | Flush the pending result and clear flags |

Formal receipts account for each arrival, acceptance, delivery and drop even
when successive bytes have equal values. The circuit exposes one valid slot
and sticky overrun; it has no hardware drop counter. Arbitrary consumer stalls
cannot have a lossless-delivery guarantee.

The physical pins keep the fixed five-pad layout: receive inputs on `uio0–1`,
logical outputs on `uio2–4`. UART RX releases every output. Host serial uses
`ui0–2`, result pages `ui3–4`, consume `ui5` and clear `ui6`; `ui7` remains unused.
Result page 3 keeps marker bit 4 and adds the stream-enabled flag at bit 3.
Disabled pages match the earlier interface. Stream access is explicit in the
Python host; existing one-shot upload/start calls refuse enabled streaming.

## The one-edge observation boundary

The [original stream model](uart-stream.md) records the **newly stepped**
receiver completion in its buffer. The package observer records the **pre-edge**
core output. If the receiver completes on edge `n`, the actual mailbox receives
that result on edge `n+1`, provided no mailbox reset intervenes. With a quiet
host command on that edge, automatic START also rearms the receiver. A nonquiet
command can postpone rearming while the mailbox still retains the result. The
old sample registers are read before a restarted core clears them.

Consumer and clear controls must consequently align with the mailbox arrival
edge. Comparing both buffers at the same edge with an unshifted control history
would be incorrect. Receiver abort and mailbox flush are also distinct events.
The new formal model makes both boundaries explicit. Existing ideal/equal-clock
and [unequal-clock stream bounds](uart-stream-clocks.md) still describe receiver
completion/rearm over the consumed input history. External pin timing additionally
includes the real sampler and the declared digital wire/clock schedule.

## Evidence owners

| Owner | Responsibility |
| --- | --- |
| [PairedStream.lean](../../Pinwheel/Hardware/Storage/PairedStream.lean) | Control policy, actual circuit expressions, wrapped paired graph and package |
| [HostResultBuffer.lean](../../Pinwheel/Hardware/HostResultBuffer.lean) | Exact existing mailbox refinement, accepted order and arrival accounting |
| [BufferedSupervisor.lean](../../Pinwheel/UART/BufferedSupervisor.lean) | Conditional pre-edge UART observer correspondence, canonical E64 step/run and explicit delayed stream receipts |
| [pinwheel_host.py](../../scripts/pinwheel_host.py) | Explicit arm/stop/stream readback and byte/framing-error decoding |
| [uart_stream_peer.py](../../scripts/uart_stream_peer.py) | Independently scheduled external wire and one-entry ownership oracle |
| [check-uart-stream.py](../../scripts/check-uart-stream.py) | Fresh upload certificates, resolved package wires, controls and byte custody |
| [check-stream-readback.py](../../scripts/check-stream-readback.py) | Fresh universal core/package RTL interpretation, exact interface and corruption rejection |

`observer_step` requires correspondence between core busy/mode/samples
and the normal UART receiver result, plus consumed control alignment.
`decoded_step` and `decoded_run` cover canonical E64 execution from a well-formed
receiver and its lifted compiled state, with caller-supplied start/reset inputs.
At this checkpoint, connecting those controls and core correspondence to the
active UART image and paired supervisor remained an integration premise. The
`uninterrupted_delay` and `uninterrupted_receipt` theorems compare the logical
continuous-start model with the existing stream model after one warm-up edge,
shifting consumer and clear histories by one edge. They allow arbitrary initial
buffer contents but require no execution reset or mailbox flush. Interpreting
an older pending packet as a UART result additionally requires its program
ownership. The [initialized session proof](uart-session.md) subsequently
derives the relation, controls, SRAM responses and owned receipt history for
its declared finite lifecycle; this original component study retains its scope.

This adds a new digital candidate. The saved physical A receipts do not qualify
the new control bit or altered logic. SRAM internal qualification, compatible
fast-corner conditions and package power remain separate acceptance requirements.
No placement, route or extraction is allocated. FIFOs, concurrent TX/RX,
flow control, metastability, board timing and new protocol families remain outside
this milestone.

## Delivered checkpoint — 2026-09-29

The opt-in `paired-stream` candidate is delivered locally. The additive
[manifest](../../physical/experiments/uart-supervisor-results.json) binds the
implementation, successful gates, preserved development attempts and unchanged
historical physical artifacts.

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

The wire peer schedules every start/data/stop transition in absolute integer time
quanta before arming. It never uses the DUT's busy, PC or results to choose wire
values. Equal-clock fixtures cover RX periods 8, 9, 16, 257 and 6656 on both input
pins; the largest image uses 250 positions and 14 distinct records. The stream
cases cover zero, all-one, alternating and repeated-equal bytes, bad stop followed
by good reception, a false pulse, held-low start, consumer stalls, consume plus
arrival and clear plus dropped arrival. Period-16 unequal-clock cases use TX
ticks 97/103, RX tick 100 and phases 0/99; the existing two-stage digital sampler
provides the declared two-edge observation age in this simulation. For periods
above 256, the timing certificate represents the same wire period using one TX
cycle with a longer tick. The sufficient timing certificate for the unsafe
8-cycle RX, one-cycle TX with tick 770 against RX tick 100 case is rejected,
while its single-frame bound passes; no universal failure outside the bound is
claimed.

Session checks cover rejected serial commands on the completion and following
stopped edges, serial reset with retained data, active STOP, external reset and
reload. Fault modes disarm. The host refuses an unread one-shot start and validates
a UART packet before consuming it, preserving timeout/fault and noncanonical
packets for raw inspection. The disabled candidate runs UART RX, two-byte SPI and
two-payload-byte I²C on the same emitted chip. A wrong capture-slot program remains
canonical and receives its own image certificate, then fails UART semantic
validation. RTL controls remove rearm/reservation, overwrite an unread result or
clear overrun after a drop; each fails its corresponding oracle.

Fresh RTL is imported with an exact interface, no unknown or initialized state,
and positive-edge two-state semantics. SRAM read response is an independent
input to this component theorem. Imported JSON, source cuts, generated proof
sources and compiled imports, candidate RTL and consumed tool files are frozen before use and checked
again at closeout. Bundled tool identity excludes the system loader/libraries,
shell and Python/Lean runtimes, which remain environment assumptions. This
component result and the finite initialized wire gate do not claim a universal
continuous paired-package theorem.

All **218 preexisting physical manifests and fixtures** match base `855fd94`.
The historical SPI/I²C chip bytes remain untouched; the new UART wrapper differs
from them. No physical evidence transfers to it. This adds **zero CAD seconds
and zero routes**; campaign consumption remains 8,843.120 seconds, with three A
routes used and two B routes reserved. Generated receipts and focused logs
are ignored local dependencies; tracked hashes do not provide a remote backup.

## Reproduce locally

Install the pinned tools and behavioral SRAM models described in
[development](../development.md), then use fresh tags from the repository root:

```sh
python3 scripts/check-foundation.py --tag uart-foundation-fresh
python3 scripts/check-uart-stream.py --tag uart-stream-rtl-fresh
python3 scripts/check-stream-readback.py --tag uart-source-readback-fresh
python3 -B -m unittest discover -s test -p 'test_*.py'
python3 -O -B -m unittest discover -s test -p test_uart_stream.py
python3 -O -B -m unittest discover -s test -p test_stream_readback.py
```

The runners preserve existing run directories and emit fresh certificates and
RTL. `pinwheel-host.py` accepts `--backend paired-stream` explicitly; existing
backends retain their defaults. An actual certified HALT run through that CLI
passed with streaming disabled and emitted the same chip MLIR/RTL as the wire
gate. Its separate receipt is bound in the manifest. The Python client offers `arm_uart_stream`,
`stop_uart_stream`, `stream_status` and `read_uart_result` on a deliberately loaded
UART receive program.
