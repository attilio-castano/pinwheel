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
