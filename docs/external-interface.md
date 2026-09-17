# External timing and interface contract

This is the digital boundary for future integration. It does not insert new
latency into the existing core or claim a completed package wrapper.

## Clock-edge meaning

The engine consumes its input snapshot from the state **before** each rising
clock edge. Every register then updates from that same snapshot. The existing
proofs refer to this core-side observation, not an asynchronous package voltage.

`Hardware/PinBoundary.lean` specifies a proposed two-register input pipeline.
On edge n, the first register captures the sampled pin; the second captures the
old first register. The engine simultaneously consumes the old second register.
Thus a pin sample captured on edge n is consumed on edge n+2, provided the two
pipeline updates are not reset. `two_edge_latency` proves this convention. Reset
clears both stages to an explicitly selected reset-sample profile; that profile
must match the board/protocol idle assumptions. Two capture edges refill the
pipeline before relying on a new external sample.

The [pin-sampler study](pin-sampler-study.md) now builds this pipeline
structurally in front of the proved backends, with the reset tied low, and proves
that every observation equals the reference machine's on the delayed pin history.
It is an experimental emitted variant; the default core still has no pipeline.

This theorem concerns digital samples. An asynchronous transition near a clock
edge can be captured later, and metastability resolution is not modeled here.
Physical integration must separately establish the synchronizer implementation,
clock/reset release, input timing assumptions, and electrical behavior. A fixed
two-edge digital delay is not an unconditional analog detection-time bound.

Protocol bounds must account for this delay. For example, a wait with four
remaining core observation opportunities has fewer opportunities to see a
new package event once the input pipeline is included. Recheck receive sampling,
clock stretching, timeout, and branch/capture contracts against the chosen pin
assumptions. Keeping output scheduling unchanged does not preserve a round-trip
external reaction deadline automatically. Do not silently reinterpret the input
history in existing compiler theorems.

## Drive and release

The core has output levels and output enables. A push-pull lane drives its chosen
level while enabled. An open-drain lane drives zero or disables the driver; a
logical release is not an actively driven one. The `openDrain` adapter always
has zero output data and enables only for `I2C.Drive.low`.
`openDrain_resolves` connects that adapter to the existing ideal pull-up bus model.
Arbitrary loaded programs are not automatically valid I2C programs; applying
open-drain mode requires the appropriate lane/program contract.

Pull-ups, pad input thresholds, rise/fall times, loading, and board voltage remain
physical obligations. The digital bus model establishes none of those values.

## Loading and package integration

The transport must deliver complete synchronous command/data snapshots to the
existing word loader. Each accepted word occupies exactly one core command edge;
partial serialized words cannot assert push. Commit/start/abort/reset and rejected
commands retain their current priorities and acknowledgement semantics. Transport
reset discards a partial word; core reset retains the committed program according
to the existing loader contract. Startup initialization remains a distinct action.

For any asynchronous host interface, specify how the entire command/data word
crosses into the core clock domain; independent bit synchronizers do not define
an atomic 64-bit transfer. Specify backpressure/acknowledgement and how the host
distinguishes transport acceptance from loader rejection. A protocol must not
start until upload and commit acceptance are known.

The serialized protocol, package-pin allocation, lane mapping, reset-sample
profile, and board electrical limits remain integration decisions. Resolve them
against the actual supported Tiny Tapeout wrapper/I/O budget before implementing
the transport. The current diagnostic 6x4 routed core is not that wrapper.

See [atomic loading](atomic-loader.md), [hardware closure](hardware-closure.md),
and [processor obligations](processor-verification.md#milestone-5-implement-real-loading-and-external-interfaces).
