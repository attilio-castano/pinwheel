# Opt-in streaming continuation contract

This is a separate target/interface contract, named
`pinwheel-streaming-quad-v1`. It does not change the existing target.

## Stored program

The program has 1–64 rows, each a 64-bit word. The supported source form is a
pulse prefix, exactly one stream cell, a pulse suffix, and a halt/fault terminal.
Unsupported shapes are rejected by the compiler before device I/O. START's
16-bit bit-cell count is independent of the number of stored rows. Zero skips
the stream cell. Pulse rows have no FIFO effects.

| Bits (inclusive) | Field |
| --- | --- |
| 0–2 | opcode: pulse 0, stream 1, halt 2, fault 3; others invalid |
| 3–10 | low duration minus one |
| 11–18 | high duration minus one |
| 19–21 | low levels |
| 22–24 | low output enables |
| 25–27 | high levels |
| 28–30 | high output enables |
| 31–32 | TX output selector 0–2; 3 rejected by the source compiler |
| 33 | RX input selector |
| 34 | transmit flag |
| 35 | receive flag |
| 36–38 | last-cell low-level OR mask |
| 39–41 | last-cell high-level OR mask |
| 42 | TX inversion |
| 43 | TX selects output enable instead of level |
| 44–46 | last-cell low-enable OR mask |
| 47–49 | last-cell high-enable OR mask |
| 50–63 | reserved zero |

Pulse fields above bit 30 are canonical zero. Halt/fault words contain only
their opcode. Durations are 1–256 engine cycles. Last-cell masks apply only
when the stream counter is one. TX selects one of three generic outputs;
there is no hardware SPI or JTAG selector.

## Queues and timing

Each direction has `2^addrBits` fixed 32-bit word slots, with configurations
`addrBits = 1` and `2` required for qualification. A chunk has 1–32 valid bits.
TX is left aligned and consumed MSB first; a partial RX chunk is right aligned
and has an explicit valid-bit count. The shifter, assembler, active cell,
frontend staging, and replay cache are additional fixed storage and count
toward the implementation's storage report. Transcript lists are trace ghosts,
never device state.

Admission uses pre-edge credit; there is no empty/full bypass. A stream cell
parks its low pins before waiting, then reserves its TX bit and a free RX word
slot atomically. It never stalls high. The capture uses the pre-edge second
sampler stage on the low-to-high edge. The sampler advances on every engine
edge, including stalls. Each committed stream cell decrements the count once;
TX-consumed and RX-produced counts advance independently according to flags.
For low/high duration fields `L` and `H`, HIGH lasts exactly `H` engine cycles.
An ordinary repeating LOW lasts `L+1` cycles because reservation has its own
edge; credit stalls extend LOW further. Prefix/suffix fetch adds its own parked
interval. The independent peers check physical clock edges and these intervals.
The SPI/JTAG convenience compilers accept half-periods of 3–256 cycles; the
generic ISA's smaller durations have no implied external-peer timing guarantee.

Weak service fairness means that every reached boundary eventually has the
required TX/RX credit. Under ordinary runtime commands, this suffices to reach
completion or fault after finitely many edges, allowing arbitrary finite stalls.
It gives no wall-clock bound or successful-peer guarantee. The separate
continuous-credit theorem gives a numeric bound under its stronger assumption.

A transfer owns its queues and exported receipt until completion/fault and
drain/acknowledgment. RELEASE requires the RX queue/assembler to be empty and
the frontend's exported RX interval acknowledged. Explicit reset cancels the
owner. No cross-cold-boot authentication or persistent epoch claim is made.

## Quad host wire format

Inputs: CSn `ui_in[0]`, SCK `ui_in[1]`, MOSI lanes 0–3 on `ui_in[2,5,6,7]`,
and raw protocol inputs on `ui_in[4:3]`. Outputs: MISO lanes 0–3 on
`uo_out[3:0]`, READY on bit 4, BUSY on bit 5. Protocol outputs and enables use
`uio[2:0]`. This uses the existing pad count in a new wrapper.

Fields and nibbles are transmitted MSB first. A request is a 160-bit logical
frame followed by CRC-16; a response is 192 logical bits followed by CRC-16.
CRC parameters: polynomial `0x1021`, initial `0xFFFF`, non-reflected input/output,
final XOR zero, covering the complete logical frame. This detects the tested
corruptions; it is not authentication or an arbitrary fault guarantee.

Request: header 16, sequence 16, payload 128. Header is `(0xA72 << 4) | opcode`.
Exchange payload: owner tag 32 (generation high 16, transfer low 16), TX bit
offset 16, RX acknowledged bit offset 16, TX data 64. Exchange opcodes select
0, 32, or 64 offered bits. The final chunk uses the remaining expected TX bits;
unused data tails must be canonical zero.

| Opcode | Request payload, most to least significant |
| --- | --- |
| 1 WRITE | address 6, word 64, zero 58 |
| 2 COMMIT | row count 7, idle levels 3, idle enables 3, zero 115 |
| 3 START | generation 16, bit-cell count 16, zero 96 |
| 4 RELEASE | owner tag 32, zero 96 |
| 7 WARMRESET | zero 128 |
| 8 EXCHANGE0 | tag 32, TX offset 16, RX acknowledgment 16, zero 64 |
| 9 EXCHANGE32 | tag 32, TX offset 16, RX acknowledgment 16, data 64 |
| 10 EXCHANGE64 | tag 32, TX offset 16, RX acknowledgment 16, data 64 |

WRITE operates only while free, invalidates the installed image, and marks that
physical row as written. COMMIT requires 1–64 covered rows, pending writes and
an available generation; it latches count/idle pins and increments generation.
The compiler uploads every active row. The hardware written mask accumulates
until reset; COMMIT alone does not certify an arbitrary partial re-upload.
START requires the installed generation and increments transfer; it latches
the count once and clears runtime queues. Generation/transfer and host sequence
numbers refuse exhaustion rather than wrap. WARMRESET cancels ownership,
invalidates the image and clears upload coverage, retaining generation/transfer.

Response: header 16, sequence 16, payload 160. Header is
`(0x5A2 << 4) | result`. Payload from most to least significant field: RX data
64, owner tag 32, accepted TX bit offset 16, RX start bit offset 16, valid RX
bits 7, free TX words 4, queued RX words 4, flags 8, reserved zero 9.
Result codes are accepted 0, bad length 1, bad header 2, bad CRC 3, bad payload 4,
and rejected command 5. Flags bits 0–6 mean valid, busy, retained, fault,
rejected, waiting TX, and waiting RX; bit 7 is zero. Each exchange exports at
most one RX word, so valid RX bits never exceed 32. The 64-bit data field
contains the right-aligned RX word. TX may stage up to two words.

Stop-and-wait uses sequence plus exact request bytes. An identical duplicate
replays the cached receipt without repeated queue effects. A partial or
overlong response read retains that receipt. Detected header/CRC/sequence/offset
errors recover by replaying the exact in-flight request. A malformed frame does
not advance the request sequence. A completed, well-framed in-sequence request
caches its response even when rejected; an identical replay keeps that rejection.
A fresh sequence can retry admission after credits change. Sequence 65535 has
no successor within that session.

Exported RX bits have separate persistent custody state and survive replacement
of the replay cache. An admitted new exchange retires an interval only with its
exact end acknowledgment. Rejected frames and exchanges preserve that custody.
A retained owner rejects any new TX offer before acknowledging RX; a zero-TX
exchange can retire the last RX interval. RELEASE cannot discard an
unacknowledged interval.

An exchange admitted while busy can finish its reserved staging after the
engine completes or faults. The core accepts those beats under the same owner
and the same bit budget. Any unused TX stays in its fixed FIFO and blocks a
drained RELEASE; explicit reset can cancel it. This avoids retiring an old RX
acknowledgment and then rejecting the already reserved TX solely because the
engine reached its terminal edge.

The frontend stages at most one 32-bit TX push and one RX pop per engine edge.
It reserves all required credits before changing either queue. The receipt is
snapshotted only after staging completes. The convenience `StreamHost` supports
duplex images and rejects simplex images before I/O. The generic compiler and
quad transport also expose simplex programs. Python validates the complete
static image on load; concrete Lean image certificates are produced and
kernel-checked separately by the fresh qualification worker before wire I/O.

## Proof and qualification boundary

The source model has fixed bounded queues and ghost transcripts. Its proofs
track accepted/consumed TX, captured/popped RX, the frontend's actual exported
bytes and exact acknowledgment interval. Accepted staging remains owned across
the completion edge. A drained RELEASE consumes every accepted TX bit and
acknowledges every captured RX bit; a new START cannot erase an old receipt.

Cold initialization is separate from installed execution. Concrete sampled-pin
SPI/JTAG upload certificates derive loader acceptance, image binding and a free
joint source session from arbitrary power-up registers. The artifact join lifts
those clocks through the actual Tiny Tapeout and package wiring to every emitted
register and output. A following actual START guard establishes reached custody;
subsequent physical prefixes preserve it. Joint-session fairness uses commands
generated by the actual source frontend feedback, and yields a finite raw state
whose phase is completion or fault. The installed runtime grammar excludes cold initialization,
WARMRESET, WRITE and COMMIT, including rejected loader commands. An explicit
warm-reset theorem covers cancellation back to an uninstalled state, retaining
the program bank, idle configuration and allocation IDs while clearing validity,
coverage and runtime custody. Reloading requires another initialization proof.

The finite peer tests, raw two-state equations, source proofs and technology
mapping provide separate evidence. Matched mapping includes all register-backed
program, queue, frontend and receipt state. ABC's recorded combinational Liberty
delay estimate cuts sequential and macro boundaries and excludes clock-to-Q,
setup, clock trees, wires and parasitics. It establishes no guaranteed clock
frequency, electrical behavior, physical SRAM closure or routed timing signoff.
