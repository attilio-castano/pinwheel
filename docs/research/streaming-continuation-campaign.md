# Streaming continuation campaign

Launch: 2026-10-17 15:30:35 UTC. Deadline: 2026-10-18 03:30:35 UTC.
Integration reserve begins at 2026-10-18 00:30:35 UTC.
Baseline: `31816bb86aa5154c2671a8d479650c7b063d93aa`.
Branch: `codex/streaming-continuation`.

The user authorized the full ambitious plan, autonomous local implementation,
validation, and incremental commits for up to twelve hours. This campaign does
not authorize a push, PR, publication, fabrication, paid service, or provider
message. Twelve hours is a maximum work budget, not a completion guarantee.

## Finish line

One emitted circuit for each bounded buffer configuration must execute a 4 KiB
full-duplex SPI transfer and a 4,097-bit JTAG scan. Each transfer has one START,
one owner, and repeatedly serviced fixed-size TX/RX queues. Device storage must
not grow with the message. Neither chunkwise restarts nor protocol-specific
RTL regeneration qualify.

Required evidence includes parameterized queue and ownership proofs; a source
compiler that automatically certifies its static image or rejects it before
I/O; initialized source-to-RTL correspondence covering every new represented
state/output and the actual wrapper; independent edge-driven peers at two
buffer depths; service-stall and corruption/recovery controls; matched mapping
with all storage counted; and fresh committed-source regression receipts.
Kernel proofs may use only the project's standard axiom allowlist. Digital
proof and mapping do not establish physical SRAM, electrical, routed, or
fabrication signoff.

If every mandatory gate closes early, continue in order to a 64-byte reactive
I²C exchange with bounded stretching, autonomous UART reception, and universal
source-to-mapped-netlist correspondence. Reserve the final three hours for
integration, independent review, immutable receipts, and the morning report.

## Design decision

Implement an opt-in streaming microcore. Preserve the current target, ABI,
semantics, and historical receipts. Reuse the typed expression/circuit emitter,
sampler approach, physical pad conventions, and artifact infrastructure. The
new stored program contains at most 64 words of 64 bits. A separate 16-bit
START count repeats one generic stream cell without expanding the program or
crossing the old virtual-position limit. Prefix/suffix pulse cells express
protocol navigation. No protocol dispatch is wired into the circuit.

The first implementation uses a register-backed program bank and bounded
word queues. Their entire cost must appear in the matched mapping. Reusing the
old SRAM fetch controller by hiding a START per chunk would violate this goal.
A future SRAM organization needs its own explicit correspondence.

The new host link is four lanes over otherwise unused existing pads. A bulk
exchange clocks 176 request bits and 208 response bits in 96 sampled SCK rises,
plus framing/dispatch overhead. At two engine cycles per sampled SCK bit this
has service headroom for a 64-bit exchange while a half-period-four SPI stream
consumes 512 engine cycles. Qualification must measure the actual complete
service interval, including dispatch and software framing.

Every cell first drives its declared low/park pins, reserves required TX and
RX credit, and captures on its low-to-high edge. Samplers continue during a
stall. High duration is exact; queue service may extend only the low phase.
Protocol-specific compiler corollaries must establish that these park pins are
safe. Progress requires explicit eventual host service and cooperating-peer
assumptions; an arbitrary admitted program need not succeed.

## Intake preservation

Two documents were already modified at intake and remain outside campaign
commits. Their exact contents must be preserved:

| Path | SHA-256 |
| --- | --- |
| `docs/protocols/buffered-spi-refinement.md` | `805eba24279d4dd798c49f92aaaa146005475f9496cafdf393d9f5140aa66d59` |
| `docs/research/status.md` | `c669c35bf690df6c370da43dc6d2cfa6fa96fb3e56be0e9bd2d741a39fb198fe` |

The combined intake patch hashes to
`efb3443f8103705eaeb222847c21750cdeeee5b0bde2ec0c3dea6d6eddef1108`.

## Work ownership

The root agent owns the typed streaming hardware, host frontend/wrapper,
integration, fresh correspondence, commits, and final evidence. The formal
agent owns bounded source queues/ownership/semantics. The compiler agent owns
the checked source compiler/static certificates and matched mapping. The peer
agent owns the bulk software transport and independent physical-edge peers.
All agents share the checkout and use separate new files.
