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

The [typed export](../../Pinwheel/Hardware/StreamingReady/TypedExport.lean)
uses `TypedModule` for the existing sampled-ready core and shared quad frontend.
The depth-two SPI-only entry point uses the same
[typed protocol workflow](#typed-protocol-matrix).

```sh
python3 -B scripts/check-typed-spi.py --tag spi-local
```

The report and generated certificates are in `build/typed-spi/spi-local`.

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

## SWD DPIDR read

The fixed 20-row image reads the Debug Port Identification Register from a
point-to-point target already in SWD mode, with a one-clock turnaround and
an OK acknowledgment. The request is `0xA5` in LSB-first order. The image
clocks eight request bits, one turnaround, 36 reply bits, another turnaround,
and eight driven-low idle clocks. The 36 reply bits fit the two RX slots,
so the wire exchange runs without queue service. [Arm ADIv5, sections B4.1–B4.3](https://documentation-service.arm.com/static/622222b2e6f58973271ebc21)

The fixture drives SWCLK on `uio_out[0]` and joins the SWDIO drive
`uio_out[1]` to the raw sense input `ui_in[4]`. The modeled target advances
its output on observed SWCLK rising edges, starting after the first turnaround
edge and releasing after the parity edge. The [package proof](../../Pinwheel/Hardware/StreamingReady/SWDSession.lean)
checks the 54 clock edges, both released turnaround samples, and exclusive
drive at every observation. Each reply bit uses the public SWDIO sample two
core clocks before its rising edge. The host acknowledges the exact 36-bit
reply before RELEASE. The decoder returns the 32-bit value after checking
the ACK and even parity, and rejects the flipped-parity reply.

The frozen RTL and CMOS5L gate netlist produced identical public traces over
8,619 clocks for the valid and flipped-parity cases. The four-cycle half
period yields a 506-core-clock exchange after START. The trace SHA-256 is
`be2cf74265d790118d2d832d2bef256223e8e2be9b4d535a44559adf5bc1a547`.

```sh
python3.12 -B scripts/streaming_8x4_swd_dpidr.py \
  --release "$PINWHEEL_RELEASE" --models "$PINWHEEL_MODELS" \
  --iverilog "$PINWHEEL_IVERILOG" --vvp "$PINWHEEL_VVP" \
  --out build/swd-dpidr-frozen
```

## PS/2 keyboard receive

An opt-in two-row image programs the existing Ready engine to receive one
keyboard-to-host frame, then return to idle. The keyboard
drives open-drain CLK and DATA into `ui_in[3]` and `ui_in[4]` while Pinwheel
releases its protocol outputs. The waveform contract at a modeled 4 MHz
core clock allows each low and high half-period to range independently from
120 through 200 samples, or 30 through 50 microseconds. CLK starts high,
and the first falling edge may arrive any time after the three-clock setup
following an admitted START for 11 bits. The receiver takes the DATA bit
present at each keyboard falling edge. [Freescale AN1723, Figure 5](https://www.nxp.com/docs/en/application-note/AN1723.pdf#page=9)

The sampled CLK-low guard captures two core clocks after each raw falling
edge. The next poll starts 220 core clocks after the previous capture, after
the previous low phase has ended and before the next possible falling edge.
In the zero-based post-START trace, a final fall at index `f` gives a completed
prefix of length `f + 221`. The [package theorem](../../Pinwheel/Hardware/StreamingReady/PS2Session.lean)
checks the exact capture indices, released output enables, and 11-bit
export through an acknowledged drain and accepted RELEASE. The decoder checks
the start bit, odd parity, and the stop bit after the exact symbols have been
exported. It recovers the eight LSB-first data bits for every valid byte and
rejects each independently malformed framing field.

The frozen RTL and matching CMOS5L gate netlist produced byte-identical
traces across 18,810 public edges. The fixture used minimum, maximum, and
mixed half-periods. Both backends decoded `0xB2`, rejected the three malformed
frames, and acknowledged all 11 bits before releasing each owner. The trace
SHA-256 is `8f40487dfd6ad867ed4fd76df058939dab6930f5f38faa8eebb84e0a81f94cb0`.

```sh
python3.12 -B scripts/streaming_8x4_ps2.py \
  --release "$PINWHEEL_RELEASE" --models "$PINWHEEL_MODELS" \
  --iverilog "$PINWHEEL_IVERILOG" --vvp "$PINWHEEL_VVP" \
  --out build/ps2-frozen
```

## Passive Classical CAN receive

A three-row image observes a single standard-format data frame carrying one
byte. The transceiver's digital receive signal enters `ui_in[3]`, with LOW
representing dominant and HIGH representing recessive. The package releases
its protocol output enables throughout. The peer waveform includes a dominant
ACK from another receiver and a recessive idle tail. [Bosch CAN Specification 2.0, Part B](https://www.canlab.cz/sites/default/files/pages/download/Can2spec.pdf#page=43)

The modeled 4 MHz core gives 32 clocks per bit at 125 kbit/s. START arms
the guard while the bus is recessive. After the first dominant sample at
index `f`, the program uses raw samples `f + 16 + 32k` for `k` from 0 through
63. The capture events use the second sampler two clocks later. The peer
may shift each bit boundary by up to four core clocks in either direction
from its nominal position relative to `f`. Each sample still lands inside
its bit. In the zero-based post-START trace, the program completes after
`f + 2053` input samples.

The 64 samples fit the two RX slots. The [package theorem](../../Pinwheel/Hardware/StreamingReady/CANSession.lean)
connects the samples to acknowledged host export. The host decoder removes
stuff bits, checks CRC-15 and frame fields, and returns the 11-bit identifier
and byte. It rejects a corrupted stuff bit and an independently corrupted
CRC with correct stuffing. The proof uses one synchronization event at
start of frame and bounds the resulting clock skew over the entire window.

The frozen RTL and matching CMOS5L gate netlist produced byte-identical
traces across 11,018 public edges. Each backend exported 64 samples per
owner. The host decoder recovered identifier `0x012` and payload `0xB2`
and rejected both malformed captures. The fixture supplies a dominant ACK
in all three cases to isolate the injected errors. The trace SHA-256 is
`4b3d3ce229bcc8803a98960004cff72d071b55dfd5774a83f37277135cce1a08`.

```sh
python3.12 -B scripts/streaming_8x4_can.py \
  --release "$PINWHEEL_RELEASE" --models "$PINWHEEL_MODELS" \
  --iverilog "$PINWHEEL_IVERILOG" --vvp "$PINWHEEL_VVP" \
  --out build/can-frozen
```

## Ethernet serial PHY transmit

A six-row image sends a minimum-size Ethernet frame to an external 10 Mbit/s
serial network interface (SNI) PHY. The host supplies seven preamble octets,
the start-frame delimiter, and 64 MAC-frame octets including the FCS. The
72 octets become 576 LSB-first bits in nine quad-host words. The PHY handles
Manchester encoding and the twisted-pair interface. [TI DP83848-EP SNI timing](https://www.ti.com/lit/ds/symlink/dp83848-ep.pdf#page=22)

`ui_in[3]` receives `TX_CLK` and `ui_in[4]` receives the external arm signal.
`uio_out[0]` provides `TXD` and `uio_out[1]` provides `TX_EN`. START sets the idle
levels. The host stages the first two FIFO words with arm low. The program
then waits for arm and uses three waits on high, low, and high to align to
a fresh PHY clock rise. In the modeled 60 MHz domain the PHY rises every
six core clocks, with one or two sampled high ticks. In the checked schedule,
arm coincides with a PHY rise and the first enabled rise occurs 18 ticks later.
The TX bit launches two ticks before its sampling edge.

The host runs eight more `EXCHANGE64` transactions at 384-tick intervals.
The checked admission cuts fall 16 ticks after the preceding pair's second
word enters the shifter, with both queue slots available. The frontend then
stages the two new words before the shifter empties. The [package proof](../../Pinwheel/Hardware/StreamingReady/EthernetSession.lean)
checks the actual sampled request, response, and engine recurrences. It
establishes the exact frame bit on every PHY sampling edge, continuous
`TX_EN` during the frame, and RELEASE after all 576 bits are accepted and
consumed. The [core timing proof](../../Pinwheel/Program/StreamingEthernetCoreFrame.lean)
also covers arbitrary transmitted bits under explicit reservation credit.

The frozen RTL and matching CMOS5L gate netlist produced byte-identical
traces across 14,373 public edges. The independent PHY model accepted the
valid frame at both high widths and rejected the flipped-FCS control.
Each run checked all 576 sampling edges, the setup interval, nine admitted
bursts, and RELEASE. The trace SHA-256 is
`6e830b8973ab4929eb3db3016d18b47a2cbb992d46fb9021ae536383d63dee80`.
These results use a digital SNI model. A board implementation needs a
qualified core frequency and a shared timing budget for the PHY clock,
pad delays, and setup and hold.

```sh
python3.12 -B scripts/streaming_8x4_ethernet.py \
  --release "$PINWHEEL_RELEASE" --models "$PINWHEEL_MODELS" \
  --iverilog "$PINWHEEL_IVERILOG" --vvp "$PINWHEEL_VVP" \
  --out build/ethernet-frozen
```

### Host refill policies

The [credit checker](../../Pinwheel/Program/StreamingEthernetCredit.lean)
uses the session's runtime commands to establish the PHY slot levels, TX
credit and next bit at each reservation. The shared frame theorem then
establishes the exact wire trace. The original uniform policy launches
refills 384 clocks apart. The staggered policy delays every other refill by
24 clocks. Lean checks both policies for one- and two-clock sampled PHY high
widths.

With the pinned hardware tools installed, run the depth-two typed workflow
with a fresh tag.

```sh
python3 -B scripts/typed_ready_workflow.py --ethernet-only --tag refill-policies
```

The replay uses the independent PHY at high width one and compares legacy
and typed RTL traces byte for byte. Lean binds the replay's frame bytes,
image and observed refill launch cuts to the two proved schedules. The
late control delays the first refill by 180 clocks and the second by 64.
Lean checks that the engine lacks credit at the reservation after bit 64.
The host admits all 576 bits and releases the owner. The PHY sees the first
incorrect bit at index 65, counted from zero, with completion six clocks
late. Find the generated proofs and traces under
`build/typed-ethernet/refill-policies`.

## Typed protocol matrix

With the pinned hardware tools installed, run SPI and I²C at FIFO depths two
and four with a fresh tag.

```sh
python3 -B scripts/typed_ready_workflow.py --tag protocol-matrix
```

The workflow builds the legacy and typed emitters from Lean source and
requires identical port and register inventories, MLIR, and lowered RTL.
Each depth shares one core and wrapper certificate across both protocols.
The frontend certificate serves both depths after the workflow verifies
identical frontend RTL. Each depth's simulations use the same certified
digital core and wrapper bytes.

SPI runs the existing six exchanges against both emissions and compares the
public traces byte for byte. Its
[artifact proof](../../test/StreamingReadyTypedSPIProof.lean) carries cold
boot and START-to-RELEASE onto the reconstructed RTL. I²C runs the existing
read and write cases, including last-poll success. The separate one-poll-late
control checks retained fault and acknowledgment, and sampler-stage and
guard-bypass mutations must fail the independent wire oracle. The
[I²C artifact proof](../../test/StreamingReadyTypedI2CProof.lean) carries
cold boot, the completed 64-byte read, and both deadline theorems onto each
reconstructed configuration under the existing protocol assumptions.

Find the shared frontend, per-depth certificates, replay traces and axiom
audits under `build/typed-ready/protocol-matrix`.

## Shared session and deadline proofs

The [session proof](../../Pinwheel/Hardware/StreamingReady/SessionProof.lean)
gives SPI and I²C the same START, segment, and RELEASE argument. START
establishes ownership and the core start state. Each segment returns the
next reached state and accumulated bit custody, with its public drive trace
related to the source trace. A later segment can use that reached state
directly. An admitted RELEASE accounts for the last acknowledgment.

The [guarded-cell theorem](../../Pinwheel/Program/StreamingReadyGuardedCell.lean)
handles both outcomes of a bounded wait. Prior misses preserve the capture
prefix. The first ready poll captures the bit from the second sampler,
including when it is the final permitted poll. A miss at the deadline
faults. With the custody invariant, the earlier captures remain available
in the export and RX queue.
The [I²C deadline proof](../../Pinwheel/Hardware/StreamingReady/I2CReadSession.lean)
derives both outcomes for profiles with at least three polls using the
resolved open-drain inputs. It counts elapsed polls from the sampled wait
entry and distinguishes the raw edge from the two-clock-later aperture.

The depth-two FIFO substitution workflow replays budgets 31 and 19 on
both layouts. At each budget the last-poll case completes the 64-byte read.
The one-poll-late case retains and acknowledges the 11 captured slots,
refuses RELEASE with unused TX, and clears custody on explicit warm
cancellation. The second late case waits until slot 42 and drains a 32-bit
word followed by a 10-bit remainder. The peer observes 43 physical rises
in that case, and the host acknowledges exactly 42 captures. Lean binds the
image words from both budgets to the profiles used by the proofs.

### Complete reads under service and exact fault prefixes

The [completion proof](../../Pinwheel/Hardware/StreamingReady/I2CReadSuccess.lean)
derives a finite completed read for an admitted START. The peer supplies
resolved SDA at each capture aperture and meets each guard deadline. The
host offers the prescribed TX plan, eventually provides reservation credit,
and supplies a finite drain with an admissible RELEASE after completion.
The theorem gives START, 585 qualified slots, and STOP at the resolved bus,
the exact exported payload and acknowledgment, and the empty export at
RELEASE. The schedule and proof use the supplied `I2cProfile`.

The [fault proof](../../Pinwheel/Hardware/StreamingReady/I2CReadTimeout.lean)
starts from an initialized image and admitted START. At any reachable data
WAIT, a peer that holds SCL low through every eligible aperture forces a
timeout. The proof derives the slot ordinal from the remaining count and
checks the earlier resolved samples against the peer's payload. After an
ordinary host drain, the exported and acknowledged bits are exactly the
payload-dependent wire prefix before the failed slot.

The [layout proof](../../test/StreamingReadyTxShiftProof.lean) uses one package
simulation to transport both contracts, including the host reply pads across
drain and RELEASE. The gate checks both theorem instances and the certified
cold-upload sequence for each replayed profile.

### Warm I²C to SPI switch

The [RELEASE proof](../../Pinwheel/Hardware/StreamingReady/SessionProof.lean)
establishes a free, drained package with preserved generation and transfer
counters and cleared host export fields. The
[warm loader proof](../../Pinwheel/Hardware/StreamingReady/BootCorrespondence.lean)
uses a certified WRITE/COMMIT pin sequence from that exact frontend state.
COMMIT increments the generation, preserves the transfer counter, and
installs the new length and idle configuration. The physical word bank keeps
older rows beyond the new length. SPI runs from the new compiled program
through the same START-to-RELEASE proof used for a cold upload.

The [switch proof](../../test/StreamingReadyProtocolSwitchProof.lean) composes
the I²C result, RELEASE, warm upload and SPI exchange on one package state
history for both imported FIFO layouts. A separate admission theorem proves
that a delivered stale-generation START is rejected while the free owner,
generation, transfer counter and driven pads remain stable.

The independent replay drives one cold reset, a 64-byte I²C read and RELEASE,
and a four-row mode-0 SPI upload over the seven-row I²C image. The wire
receipt rejects a generation-1 START after generation 2 is installed. The
public pads hold the prior I²C idle drive through this rejection. A valid SPI
START exchanges 33 bits and RELEASE returns the SPI idle drive. Both layouts
match on all 13,987 edges in this sequence.

### Registered instruction reads

The [registered store](../../Pinwheel/Hardware/StreamingReady/RegisteredStore.lean)
reads the word for the next program counter and captures it in a 64-bit
register on the edge that updates the counter. The decoder consumes that
value in the existing fetch phase. An admitted write to the selected word
forwards the new data to the read register. Cold reset establishes agreement
from an arbitrary read-register value. The same image format and host
frontend work with both stores.

The [public session proof](../../Pinwheel/Hardware/StreamingReady/RegisteredStoreSession.lean)
transports the full clock-indexed pad and host transcript. Each execution
obtains inputs from its own environment, which advances on that execution's
observations. The two executions produce identical inputs and outputs on
every edge, so the store change preserves sampling apertures as well as
captured bits and ownership. The [causal I²C bridge](../../Pinwheel/Hardware/StreamingReady/CausalSession.lean)
derives input samples from the resolved bus and retains the host-service,
target data setup, and deadline premises of the read theorem.

```sh
python3 -B scripts/check-ready-registered-store.py --tag ready-store
```

The gate emits and replays both stores on the same images. It compares all
public edges across the warm I²C-to-SPI handoff and stale START, and checks
last-poll success and exact late-poll fault prefixes at budgets 31 and 19.
The same gate reruns the independent Reactive late-fetch control to check
that crossing the ACK aperture still fails even if read data agrees. The
evidence concerns digital circuit semantics and emitted RTL replay.

### Checked segments and combined register reads

The [segment compiler](../../Pinwheel/Program/StreamingReadySegments.lean)
extends the Ready cell language with a per-segment count, a forward branch
on a qualified receive bit, and a terminal instruction that discards
accepted but unsent TX. The checker enumerates both sides of every branch.
It checks row and branch bounds, capture availability, finite guards and
path-level TX/RX counts. Its clock bounds apply when queue credit is
immediately available and guards succeed within their declared windows.
Certification binds the source rows to their encoded image before upload.

One 24-row image performs the register-address write, repeated START and
one-byte read. The target's ACKs select whether to continue or execute STOP.
The host can queue all 36 TX bits before any branch. On each early NACK the
engine preserves the accepted and consumed counters, closes TX, and discards
the pending suffix. RX drains under the same owner before ordinary RELEASE.
A guard timeout uses the existing fault path and retains unused accepted TX
until explicit cancellation. The [control proof](../../Pinwheel/Hardware/StreamingReady/SegmentControl.lean)
checks the instruction fields, count and latched branch decision. The
[custody proof](../../Pinwheel/Hardware/StreamingReady/SegmentCustody.lean)
checks discard, TX rejection, RX drain and owner-checked RELEASE.

The [package simulation](../../Pinwheel/Hardware/StreamingReady/SegmentPackage.lean)
transports the complete timed pad and host transcript across both instruction
stores, including branches that redirect the fetch address. The
[readback theorem](../../Pinwheel/Program/StreamingReadySegmentReadback.lean)
relates the exact receive prefixes to the independent combined-read
outcomes. A source gate checks those prefixes from emitted RTL against a
wire-reactive target, including success, the three NACKs, a guard timeout,
and a warm SPI exchange following an early RELEASE.

```sh
python3 -B scripts/check-ready-segments.py --tag ready-segments
```

### Branch-sensitive execution and a split register read

The [source execution model](../../Pinwheel/Program/StreamingReadySegmentExecution.lean)
consumes TX data and pre-edge second-sampler observations. It records
credit parking, reservations, drive and capture events, and branches on
the last qualified capture. Each planned finish belongs to the image's
checked outcomes. An expired guard returns a timeout with the TX and RX
prefix reached at that poll.

The [split image](../../Pinwheel/Program/StreamingReadyRegisterReadVariants.lean)
moves the first address ACK to a separate one-slot stream. Each checked
path gains two clocks for the added COUNT and stream fetch. The general
[cell split law](../../Pinwheel/Program/StreamingReadySegmentSplit.lean)
preserves the cell events and logical timeout slot when the cell has no
final-slot pin modifiers. The register-read check also covers the decoded
outcomes and coalesces repeated writes of the same pad drive. In the
unstretched address phase of the timeout fixture, the interval before
the ACK rise grows from 12 to 14 clocks on both stores.

The source gate observes the actual instruction addresses, qualified branch
bits, TX reservations, second-stage poll samples, and terminal counters
from START. Lean checks their correspondence to the source model for both
images. The independent wire peer checks START, repeated START, data,
STOP, and digital timing. The inverted-ACK control retains the same
structural path bounds, takes the early-exit branch on ACK, and fails
the peer's STOP check.

The [circuit proofs](../../Pinwheel/Hardware/StreamingReady/SegmentPathControl.lean)
start an installed image at its entry row and tie each control fetch to
the encoded row at the current PC. The
[one-slot stream proof](../../Pinwheel/Hardware/StreamingReady/SegmentStreamStep.lean)
connects the actual fetch, reservation, LOW dwell, qualified poll, HIGH
dwell, and following branch in one run under its service premises.
Standalone [bounded waits](../../Pinwheel/Hardware/StreamingReady/SegmentWaitRefinement.lean)
advance on a qualified poll or retain ownership at expiry. The
[pulse proof](../../Pinwheel/Hardware/StreamingReady/SegmentPulseRefinement.lean)
connects the fetched row to its declared LOW and HIGH dwells and next
FETCH. A theorem composing every row into an arbitrary
START-to-terminal run remains open.

### Shared Ready runner

SPI, the combined I²C read, branching SWD, and Ethernet use `ReadyHost.load`,
`LoadedReady.submit`, and `ReadyPending.finish`. The runner collects contiguous RX intervals under
one owner and confirms the final acknowledgment before RELEASE. SPI supplies
an exact bit count. The combined I²C read takes its request, TX plan, and
per-exit TX/RX counts from the Lean-generated manifest. Its decoder checks
the address and register echoes and matches the captured ACK against the
declared exit. A timeout returns the captured prefix and keeps the owner live
until the caller explicitly invokes `cancel`. The existing quad receipts
carry accepted TX counts. The runner derives consumed and cancelled TX
counts for successful exits from the checked plan and decoded RX. I²C and
branching SWD use the same checked path-plan interface for completion,
early exit, and capture length.

The [ownership proof](../../Pinwheel/Hardware/StreamingReady/ProtocolOwnership.lean)
accounts for each accepted TX bit as reserved, discarded by an early exit,
or still owned at the drained cut. The captured RX count is exactly the
acknowledged end offset. A timeout can reserve the next TX bit before it
misses its guard, so the reservation count can exceed the number of observed
wire cells. [Legacy refinement](../../Pinwheel/Hardware/StreamingReady/SegmentLegacy.lean)
lets the fixed-length SPI proof close on the same segmented package.

The source gate uses the shared runner for standalone SPI and for SPI
warm-loaded on the same host after I²C early RELEASE. It checks the measured
ownership reports in Lean, including the timeout cut before explicit
cancellation, and compares the emitted stores with independent wire peers.

### Branching SWD RDBUFF read

The [59-row image](../../Pinwheel/Program/StreamingSWDBranching.lean) reads
the result of a modeled prior AP read from DP RDBUFF. It assumes a
point-to-point target already in SWD mode, one-clock turnaround, and
overrun detection disabled. Its three ACK bits select a path in the engine.
OK captures the 32-bit value and parity. WAIT and FAULT take the short
path through a released turnaround and eight driven-low idle clocks.
A malformed ACK keeps SWDIO released through a possible 33-bit data
phase and the following turnaround. Retrying a WAIT and resynchronizing
after a malformed ACK are separate operations.
[Arm ADIv5, sections B4.2.3–B4.2.5](https://documentation-service.arm.com/static/622222b2e6f58973271ebc21)

Every SWD path completes in the engine and returns its capture under the
same owner. The decoder reports OK, WAIT, FAULT, bad parity, or malformed
ACK. The runner acknowledges all 36 captured bits on an OK path and all
three on the other paths before RELEASE.

The source gate tests these five outcomes on the direct and registered
stores, with four core clocks per SWCLK high half-cycle. Separately captured
ACK bits exercise RX credit backpressure while SWCLK is low and SWDIO is
released. Lean checks the measured branch decisions, service clocks, RX
bits, and custody. The independent wire peer rejects an inverted ACK branch
and a driven turnaround. The same gate replays the fixed DPIDR image.

### Warm CAN and I²C handoff

One cold reset and one Ready host run CAN, the split I²C register read,
and CAN again. One sequence settles the I²C register NACK with RELEASE.
It also drains and releases a bad-CRC CAN capture after the decoder rejects
it. The other sequence holds the I²C clock through the last poll. The
retained fault rejects WRITE, COMMIT, START, and RELEASE while the TX
suffix is still owned. Explicit warm cancellation clears custody and
permits the final CAN install.

The [handoff theorem](../../Pinwheel/Hardware/StreamingReady/SegmentReload.lean)
follows the decoded core commands on both instruction stores. Accepted
RELEASE or explicit timeout cancellation establishes an empty, free cut.
Ordered writes and COMMIT install the new live rows and increment the
generation. The old generation's START is rejected. The admitted START
enters row zero with a fresh transfer, empty custody, and the new image's
idle pads. A shorter image can leave the preceding image's words in the
inactive tail.

The [CAN theorem](../../Pinwheel/Hardware/StreamingReady/CANSession.lean)
accepts a warm installed representation of the same image. The
[segmented projection](../../Pinwheel/Hardware/StreamingReady/SegmentLegacy.lean)
carries the original package observations through runtime execution of
that live image. The bench supplies separate CAN and I²C peer waveforms
with the appropriate digital pad connections at each session.

The source gate checks both sequences on each emitted store. It compares
the measured core writes with the Lean image words, checks each observed
CAN capture edge and decoded verdict, and checks the I²C outcomes and
owner accounting with the existing witnesses.

### Refill timing and ownership

SPI can park between cells when it runs out of TX credit. The combined
I²C read has a bounded clock poll within a cell. Ethernet needs credit
before each reservation on a fixed six-clock cadence. The
[reservation checker](../../Pinwheel/Program/StreamingReadyReservationTiming.lean)
finds the first missed cut in an executed input sequence. A same-edge
push can supply credit at the next cut. Ethernet uses the checker to
discharge the pre-edge obligations of its exact frame theorem.

The shared runner takes an explicit Ethernet refill schedule through
`ReadyPending.pump(scheduled_bits=64)`. The host chooses when to offer a
burst. The frontend checks current room, and the receipt confirms the
accepted prefix. The source gate measures the grant, both 32-bit core
pushes, and the first pre-edge cut that sees both accepts. It checks
those offsets against Lean and compares complete public pin traces across
the direct and registered instruction stores.

Both on-time schedules pass the independent digital PHY check. With
the late schedule, the reservation for zero-based bit 64 misses its cut,
the first sampled mismatch is at bit 65, and completion slips six clocks.
The same run accounts for all 576 accepted and reserved TX bits and
releases the owner.

The [guarded stream theorem](../../Pinwheel/Hardware/StreamingReady/SegmentTiming.lean)
starts from a reached LOW state with the encoded source row loaded. It
connects that row's guard budget to the actual circuit countdown, then
follows the successive polls. A qualified last poll captures the bit
already in the second sampler stage. An unqualified last poll retains
the owner, flushes the captured RX tail, and drives the installed idle
pads. The same theorem covers direct and registered instruction stores.

## Depth-two TX FIFO substitution

The [shift implementation](../../Pinwheel/Hardware/StreamingReady/TxShiftCore.lean)
keeps the transmit head in a fixed slot and moves each word with its valid-bit
count. Its emitted register inventory has 103 entries. The ring has 105,
including separate TX head and tail pointers. The implementations share the
core port interface, quad frontend, and package wiring.

The [queue law](../../Pinwheel/Hardware/StreamingReady/TxQueue.lean) relates the
stored slots in head order. Admission and dequeue both inspect pre-edge
occupancy. A full simultaneous push and pop removes the old head and rejects
the push. A push into an empty queue supplies data on a later edge. The
[package proof](../../test/StreamingReadyTxShiftProof.lean) relates the actual
imported RTL of both layouts. One cold edge establishes the relation from
independent startup assignments. Every public pad then agrees after any
finite input prefix, and the SPI, I²C, and Ethernet pin contracts use the same
reference trace.

```sh
python3 -B scripts/check-ready-tx-fifo.py --tag tx-layout
```

The check emits and independently certifies both cores, imports the shared
wrapper, and audits the composed Lean proof. Both replays exercise the full
push/pop edge directly and then run the existing SPI backpressure cases,
I²C read/write and deadline cases, and Ethernet refill schedules including
the missed credit control. It also runs the one-boot I²C-to-SPI switch.
The 18 trace files must agree byte for
byte. Reports and traces are under `build/ready-tx-fifo/tx-layout`.

## Verification boundaries

The source model proves structural queue bounds, exact data order, natural
nonwrapping counters, timeout prefix conservation, custody, and finite retained
completion under explicit service assumptions. Host-credit fairness and
unbounded peer-readiness fairness are separate. Bounded guards may terminate
in FAULT and do not require the peer eventually to become ready.

The new correspondence covers every represented register and output equation,
source runtime steps/runs, actual cold/upload/COMMIT initialization, warm
cancellation, and certified warm upload after RELEASE. Concrete I²C cold boot
is a 1,961-clock public-pin sequence derived from arbitrary startup. The warm
proof starts from the reached RELEASE boundary and an upload certificate for
that frontend state.

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
