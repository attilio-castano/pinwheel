# Autonomous UART reception on the sampled-ready engine

This extension uploads a nine-row receive program to the existing opt-in
sampled-ready circuit. It adds no protocol-specific RTL, registers, pins or
queue capacity. One START requests eight receive bits; the host then leaves
CSn HIGH and SCK LOW until the frame completes or faults. The emitted circuit
is the same one used for SPI, JTAG and stretched I²C.

## Program and timing contract

The profile chooses a quarter-bit duration `Q` from 4 through 128 engine clocks
and either of the two sampled inputs. A bit lasts exactly `4Q` clocks. All
three protocol outputs remain released throughout reception.

| Row | Operation |
| --- | --- |
| 0 | Wait unbounded for MARK/HIGH |
| 1 | Wait unbounded for the start LOW |
| 2 | Timed pulse with both pin patterns released |
| 3 | One-poll check that the start midpoint is still LOW |
| 4 | Timed pulse positioning the first data capture |
| 5 | Eight unguarded receive-only cells, each lasting `4Q` clocks |
| 6 | Timed pulse positioning the stop check |
| 7 | One-poll check that the stop midpoint is HIGH |
| 8 | HALT |

The pulse durations compensate for ordinary FETCH, BOUNDARY and WAIT clocks;
the durations are not simply a UART half-period copied into each instruction.
With the first raw LOW at input edge `F`, the ordinary two-stage sampler gives:

| Event | Input edge | Raw sample represented |
| --- | --- | --- |
| Start accepted | `F+2` | `F` |
| Start midpoint checked | `F+2Q+2` | `F+2Q` |
| Data bit `i`, `0≤i<8` | `F+(6+4i)Q+2` | `F+(6+4i)Q` |
| Stop midpoint checked | `F+38Q+2` | `F+38Q` |
| Successful HALT | `F+38Q+3` | No new capture |

Edges are zero-based: the state after processing edge `E` has consumed `E+1`
inputs. Thus, measured from an armed state immediately before the raw falling
edge, successful completion consumes `38Q+4` inputs. A bad stop faults after
`38Q+3`; a false start faults after `2Q+3`.

The receive theorem quantifies over every supported `Q`, input
selector and eight-bit payload. Its raw-input contract names the start, eight
data and stop sample centers. A stable 8N1 waveform is a concrete way to satisfy
that digital contract. It does not assert a tolerance for baud mismatch,
metastability, analog thresholds or a particular board clock.

The source results establish the terminal state at each named prefix. The
finite native peer separately checks the first public BUSY drop; an earliest
completion theorem over every shorter source prefix is not exported.

## Data and retained ownership

UART arrives least-significant bit first. The engine retains capture chronology
in its existing shift convention, so the low eight bits of the physical RX
word are the bit reversal of the UART payload. The host must reconstruct the
payload from chronological bits; treating the packed word as the payload byte
is incorrect.

An accepted START owns one frame and requires no TX data. Eight bits fit one RX
slot at either qualified queue depth. No host exchange, credit service or
protocol polling is needed while the frame is on the wire. After completion,
an empty EXCHANGE exports the eight captured bits; the exact RX acknowledgment
and matching RELEASE retire that owner before another START.

A false-start midpoint check faults with no captured RX. A bad stop faults
after retaining all eight data bits; those bits are a diagnostic prefix and
must not be returned as a valid UART frame. A line held HIGH remains in the
unbounded start wait until it falls or the host explicitly cancels the owner.
Warm cancellation clears installation and custody, requiring another upload.

## Qualification and limits

The fresh UART gate separately checks exact source/word compilation, initialized
source-to-RTL composition, retained ownership, independent public-pin peers,
actual RTL mutations and complete axiom/provenance audits. The peer schedules
raw input from absolute engine clocks and does not inspect private core state.
The corpus is designed to cover every payload byte at `Q=4,12,128`, at depths
two and four, plus false-start, bad-stop and held-HIGH controls.

Replacing the second sampler driver with current raw input shifts both start
detection and captures one clock earlier. The effective raw data centers can
remain unchanged, so payload mismatch alone cannot distinguish that mutation.
The independent oracle also checks the exact public BUSY completion edge.
Single-edge raw pulses, where used, are labelled sampling-window diagnostics,
not stable UART frames.

This milestone receives one 8N1 frame per START. Continuous frames under one
START, autobaud, parity, variable word lengths, electrical UART qualification
and mapped-netlist equivalence are separate obligations. Accepted committed
receipts and any remaining gaps belong in the campaign morning report.
