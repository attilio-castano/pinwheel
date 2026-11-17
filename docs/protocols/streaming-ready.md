# Sampled-ready streaming target

The opt-in `streaming-ready` target extends the bounded streaming engine with
sampled input guards. Its first application is a 64-byte I²C read or write with
clock stretching. The existing `streaming` target and its receipts remain
separate. This name identifies an instruction contract, not a project release.

## Mechanism

A streaming cell normally drives LOW, captures its input at the LOW-to-HIGH
transition, and holds HIGH for the programmed interval. A guarded cell releases
its HIGH pins at the same transition but enters WAIT. It captures only when the
two-stage sampler satisfies `(sample & mask) == expected`, then starts the HIGH
timer. Thus a target can hold SCL low without creating a phantom received bit.
TX is reserved at the preceding cell boundary; a timeout can leave one reserved
TX bit beyond the captured wire prefix.

`driveWait pins guard` also enters WAIT. A successful test advances to the next
instruction without producing a stream bit. It supports waiting for idle, a
START edge, or a STOP condition using the same generic hardware. Instructions
contain no I²C-specific operation. Host upload, owner tags, the bounded FIFOs,
and the physical quad frontend retain their existing interfaces.

A bounded budget B permits B predicate tests, including the final test. A ready
predicate wins on that final test. Otherwise the final miss faults. Budget zero
explicitly means unbounded; failed unbounded polls hold the represented timer.
The compiler rejects expected bits outside the mask. The raw execution semantics
compares the supplied value directly, including for malformed words.

Both samplers advance on ordinary clocks while the engine waits, while host
service stalls, and on rejected commands. A sampler may already contain a ready
value on entry. Pipeline timing statements specify the initial sampler state
and preceding raw samples; there is no unconditional fixed entry-to-ready delay.

## Instruction representation

Words remain 64 bits. Existing cell fields occupy bits 0–49. Bits 50–51 are the
guard mask; bits 52–53 are the expected value; bits 54–61 are the encoded budget;
bit 62 enables a streaming HIGH guard; bit 63 is reserved zero. Opcode 4 encodes
`driveWait`, whose only nonzero fields may be opcode, LOW pin values/enables,
and guard. The compiler checks canonical unused fields. Old instruction words
retain their old encoding on the original target.

The represented phases are FREE, FETCH, BOUNDARY, LOW, HIGH, COMPLETED, FAULT,
and WAIT. WAIT counts as busy for owner and host-service rules. No additional
register or port is needed: it reuses the cell word, timer, and sampler state.
The two queue configurations have the same program capacity and instruction
contract; they differ only in FIFO depth.

## Timeout and custody

A failed bounded wait drives the idle pins and enters retained FAULT. It does
not capture the failed cell, decrement its remaining count, or fabricate an RX
event. Any existing partial RX word is flushed exactly once into the RX FIFO.
The independently proved credit invariant reserves space for that partial word,
including when a host pop and timeout flush coincide.

The captured prefix remains owned and exportable. Accepted but unused TX also
remains owned. Draining RX therefore does not automatically permit RELEASE;
unused accepted TX can require explicit warm cancellation. The host accepts a
rejected fault reply only when its owner and accepted-TX count remain unchanged
and its export is either the previously retained interval or the canonical
empty interval at the local ACK end. It never appends rejected response data.

## I²C application

One seven-row image supports both 64-byte reads and writes at address 0x52.
The caller supplies a 585-cell external plan: address byte plus 64 payload bytes,
each with its ACK slot. One START allocates one owner. The fixed-depth queues
are repeatedly serviced; neither the image nor the device stores the whole
message. Read data comes from the independent target, while write data is
checked at resolved pads. The host checks address/data ACKs and projects the
raw 585 captured slots into payload bytes.

The standard profile programs LOW=4, HIGH=4, and a 31-poll guard budget. Before
START it checks both released lines; each streaming HIGH waits for sampled SCL;
STOP preparation also waits for sampled SCL. A stationary both-low pulse before
STOP clears stale HIGH sampler history. The external peer can stretch data and
STOP using resolved-edge timers. A last-poll diagnostic explicitly observes the
public SCL output-enable transition to align its deadline; it does not read
private engine registers.

An address NACK invalidates the projected payload. This image continues its
clock sequence through STOP; it has no immediate NACK branch or repeated START.
A timeout at data slot 50 preserves 50 RX bits, including an 18-bit partial word.
A separately aligned one-poll-late control can produce a twelfth physical SCL
rise but only eleven qualified captures: the late wire event is not rewritten
as a successful cell. Fault idle-pin changes may create an aborted short HIGH
or STOP-like transition. The contract describes the captured prefix and custody,
not transaction atomicity after a target violates its deadline.

### 64-byte read proof

The [read theorem](../../Pinwheel/Hardware/StreamingReady/I2CReadSession.lean)
binds the standard image to the initialized package and its public drive
trace. The digital board model resolves each controller/target pair as
open drain. At the programmed START and STOP cuts, the target leaves both
lines released and the controller changes SDA while SCL is high. Each of
the 585 qualified samples comes from the resolved SDA two core clocks
earlier. The peer supplies SDA from its own address-ACK and payload plan.
The [completion theorem](../../Pinwheel/Program/StreamingI2CService.lean)
requires eventual host credit and valid resolved samples at the final
aperture of every bounded wait that reaches its deadline.

The host sends the address, read bit and controller ACK/NACK plan through
the TX queue. On a completed read with an admitted RELEASE, the ordered
acknowledged export decodes to the target's 64 bytes. Decoding checks the
address echo, the target's ACK, and the controller's 63 ACKs and final NACK.

During a data WAIT, raw release at offset 28 reaches the second sampler at
poll 30, the last permitted poll. Release at offset 29 makes public SCL
high while poll 30 still sees the earlier low sample. The proved fault
flushes the partial word and preserves the earlier capture prefix.
The host can acknowledge that prefix while unsent TX remains owned.

Fresh replays of the varying-stretch, last-poll, and one-poll-late read
cases matched byte for byte across 24,584 public-pin clocks on the frozen
8×4 RTL and gate netlist. The late case had 12 resolved data rises and
acknowledged exactly 11 captures. The three cases use the independent
peer and public sampler-window checks of the existing I²C replay.

## Full-duplex SPI

Two four-row images run SPI modes 0 and 2 using the existing streaming
instructions. The mode-0 image retains its original words. Mode 2 parks SCK
high and samples on falling leading edges. The host selects the image with
`spi_image(mode=0)` or `spi_image(mode=2)` and supplies the bit count at
START. The pad assignments are MOSI on `uio_out[0]`, SCK on `uio_out[1]`,
CSn on `uio_out[2]`, and MISO on `ui_in[3]`.

The [package theorem](../../Pinwheel/Hardware/StreamingReady/SPISession.lean)
connects an admitted START to an admitted RELEASE. It proves one uninterrupted
CS assertion with one leading/trailing pair per requested bit. The public MOSI
bits are exactly the host's accepted TX bits. The host acknowledges exactly the
MISO bits in order, using the raw input sampled two core clocks before each
leading edge. The intervening inputs are ordinary runtime commands ahead of
the RELEASE edge.

The theorem also proves that each leading edge starts a full active interval
of the programmed duration. The [clock proof](../../Pinwheel/Program/StreamingSPI.lean)
shows that when TX or RX credit is unavailable, CS stays asserted and SCK
stays at the mode's idle polarity. Eventual credit at each blocked boundary
suffices to complete the transfer.

The frozen 8×4 replay loads both images in succession after one cold reset.
At a four-cycle half-period, each image passes 1-, 33-, and 257-bit exchanges.
The 257-bit cases pause after bit 32 and each reaches a 4,572-cycle inactive
SCK interval. The frozen RTL and its CMOS5L gate netlist produced identical
public traces across 27,220 cycles. The recorded trace SHA-256 is
`1637829b80fb8640aad7544eb3a3eb58583b575557186b1fb1e8b79a78d1a2f1`.
Use the frozen release directory containing `src/` and `release/` and the
pinned vendor models from the [release replay](../research/streaming-8x4-jane-street-behavior-20261115.md).

```sh
python3.12 -B scripts/streaming_8x4_spi_modes.py \
  --release "$PINWHEEL_RELEASE" --models "$PINWHEEL_MODELS" \
  --iverilog "$PINWHEEL_IVERILOG" --vvp "$PINWHEEL_VVP" \
  --out build/spi-modes-frozen
```

## JTAG DR scan

The existing 13-row JTAG image uses unguarded instructions and has the same
word encoding on the sampled-ready target. The scan starts with five TMS-high
clocks, then enters Shift-DR from any of the 16 initial TAP states. A positive
START count supplies the number of data clocks. TMS goes high on the final
data clock, and two more clocks take the TAP through Update-DR to Run-Test/Idle.
An initial Shift-DR state contributes one shift on the first reset-preamble
clock. That clock carries no recorded TDO sample.

[The source proof](../../Pinwheel/Program/StreamingJTAGTrace.lean) checks the
actual TCK/TMS edges, one TDO sample per data edge, and completion under
eventual queue credit. The peer must present the intended TDO bit at raw
input 0 two core clocks before the data edge. The public pad mapping uses
`uio_out[1]` for TCK, `uio_out[2]` for TMS, and `ui_in[3]` for TDO.

[The package proof](../../Pinwheel/Hardware/StreamingReady/JTAGSession.lean)
reuses the certified cold upload waveform at duration three. It connects an
admitted START, the sampled public TCK/TMS trace, and an admitted RELEASE
after host drain. The acknowledged export contains exactly the captured TDO
bits in order. The intervening trace uses ordinary runtime commands with no
RELEASE command. The proof covers a digital DR scan and its readback.

## Verification boundaries

The source model proves structural queue bounds, exact data order, natural
nonwrapping counters, timeout prefix conservation, custody, and finite retained
completion under explicit service assumptions. Host-credit fairness and
unbounded peer-readiness fairness are separate. Bounded guards may terminate
in FAULT and do not require the peer eventually to become ready.

The new correspondence covers every represented register and output equation,
source runtime steps/runs, actual cold/upload/COMMIT initialization, and warm
cancellation. Concrete cold boot is a 1,961-clock public-pin sequence, derived
from arbitrary startup. A second warm upload is not part of that concrete cold
boot theorem.

Development and fresh committed-source qualification are distinct. The full
Ready gate must regenerate raw artifact certificates, actual wrapper proofs,
all 20 read/write/profile cases, six deadline/SV controls, matched synthesis
cost, typed composition, and a complete private-declaration axiom audit. It
must reject altered sampler and guard drivers as well as an injected private
axiom. Portable foundation and Python gates must use the same source commit.
The morning report records the accepted receipts when these gates close.

Kernel proofs concern two-state digital equations. Resolved-pin simulations
supply finite independent peer evidence. Technology mapping supplies cost and
an ABC combinational delay estimate with sequential boundaries cut. These do
not establish mapped-netlist equivalence, guaranteed Fmax, electrical I²C timing,
metastability behavior, arbitration, board behavior, SRAM-macro closure,
placement/routing, or silicon signoff.
