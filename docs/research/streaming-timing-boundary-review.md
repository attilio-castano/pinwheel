# Streaming receive timing boundary review

The public SPI/JTAG helpers retain their minimum half-period of three engine
cycles. A development probe exercised half-periods 1–4 against actual Icarus
package pins and independent peers at both queue depths. All 32 runs transmitted
the expected bits and reached a non-fault retained state. Twenty runs also
received the expected bits; twelve intentionally tested insufficient receive
margin and returned incorrect RX bits.

This is **unqualified development evidence**, not a committed-producer
qualification receipt. No generic instruction duration, producer, peer source,
frontend, or core implementation was changed for this probe. The generic ISA
still permits durations 1–256; static legality alone does not establish success
with an external peer at every duration.

## Probe identity and deliberate guard bypasses

The ignored probe is
`build/streaming-proof-probes/half-period-public-01/probe.py`. It uses
`QuadRTL`, `QuadTransport`, and `StreamHost` to cold-reset, upload, COMMIT, START,
and collect each 64-bit transfer through public sampled pins. It makes no
private RTL register or hierarchy accesses. The independent peers see resolved
package pads and physical edge numbers, not source execution or queue state.

The captured TX bytes were `96 13 c7 5a 0f e8 b4 21`; expected RX bytes were
`a5 27 6c d2 81 5a e7 34`. SPI uses MSB-first byte order; JTAG uses the same
captured bytes as a 64-bit LSB-first scan.

Two timing guards were deliberately bypassed in this development probe:

1. `spi_image` and `jtag_image` require `half_cycles` in 3–256. The probe starts
   from each helper's half-period-four image, replaces only every cell's LOW and
   HIGH duration using `dataclasses.replace`, and calls the generic `lower`.
   This admits the intentional half-period-one/two boundary cases without
   changing the protocol helpers. Their Python static image binding is checked
   by the host; these ad hoc images were not given a fresh Lean certificate or
   a committed-source qualification run.
2. Peer constructors conservatively require `half_cycles >= tco + 3`. The probe
   constructs each peer with `max(half_cycles, tco + 3)`, then assigns its public
   `half_cycles` metadata to the requested test value. Edge, data, setup, hold,
   navigation, and RX checks remain in the original peer methods. This also
   permits testing half-period three with `tco=1`, which the conservative
   constructor normally rejects. No peer source or RTL state was patched.

The reused Icarus executables came from the retained worker directory of
`build/validation/streaming-full-328df31-20261017-01`, selected commit
`328df31fe35194e6814c178015a2c58b5d84dee5`. That full run's overall report did
not pass; reusing its compiled executables does not inherit a qualification
claim. At review time the current Core and Frontend source bytes matched the
selected report's recorded hashes exactly.

| Artifact | SHA-256 |
| --- | --- |
| `Pinwheel/Hardware/Streaming/Core.lean` | `64b86d1a5f0063c391b4ff2e1167603848fccdaa74b944a40b251b0e9418517b` |
| `Pinwheel/Hardware/Streaming/Frontend.lean` | `41db3a4a7387c1b816c63dbdc6627661337c54c4dad691ecc1fd0a0293263458` |
| `worker/wire/d2/chip.vvp` beneath that retained run | `a7edc2d7062654b30a43366ef734cbba1e4b2de3db70a4d603cccacd703ce5ee` |
| `worker/wire/d4/chip.vvp` beneath that retained run | `03ed16416951b16a9a4c47448449b8d65f27c8859afcee56259689908b43a043` |

The development result and log paths below are relative to
`build/streaming-proof-probes/half-period-public-01/`:

| Artifact | SHA-256 |
| --- | --- |
| `probe.py` | `dbc56b43b30d370405d2426ae0f3f5b3658015ae90a6e8a309b01db0caeec4ba` |
| `results.json` | `1dd26acb315060957e8bb6b96ee6b42a8325af6e5b5ad415a42e130c0ad292d8` |
| `stdout.log` | `9196a4203bf596fad9dbad15cbdd9660f8579548fe5462bb77d7c869d91945c5` |

The result records the script dependency hashes, executable hashes, complete RX
bit strings, mismatch positions, peer results, and per-case elapsed times.
There are 32 `d{depth}-{protocol}-h{half}-tco{tco}-recent-edges.json` files with
bounded recent actual-edge records. They are development logs, not complete
source-frozen trace receipts. The matrix took 9.62 seconds in total.

## Actual outcome matrix

`pass` means the independent peer accepted TX, RX, and its protocol checks.
`RX n` means the transfer retained normally and TX matched, but exactly `n` of
the 64 received bits differed. These are intentional receive-margin controls,
not successful exchanges or detected controller faults.

| Protocol | Queue depth | Peer tco | Half 1 | Half 2 | Half 3 | Half 4 |
| --- | --- | --- | --- | --- | --- | --- |
| SPI | 2 | 0 | RX 24 | pass | pass | pass |
| SPI | 2 | 1 | RX 24 | RX 39 | pass | pass |
| SPI | 4 | 0 | RX 24 | pass | pass | pass |
| SPI | 4 | 1 | RX 24 | RX 39 | pass | pass |
| JTAG | 2 | 0 | RX 35 | pass | pass | pass |
| JTAG | 2 | 1 | RX 35 | RX 35 | pass | pass |
| JTAG | 4 | 0 | RX 35 | pass | pass | pass |
| JTAG | 4 | 1 | RX 35 | RX 35 | pass | pass |

Thus the minimum observed safe half-period was two for `tco=0`, and three for
`tco=1`, in both protocols at both depths. This finite matrix does not establish
a universal minimum for arbitrary peers or analog delay. The ordinary repeated
LOW interval is `H+1`: the boundary/reservation mechanism adds one parked edge.
For this callback model, a peer update requires its `tco`, one callback-to-next-
edge delay, and two sampler stages. The corresponding ordinary-interval margin
is `H+1 >= tco+3`, or `H >= tco+2`. The existing peer constructor's
`H >= tco+3` rule is conservative by one ordinary parked edge and was preserved.

## Kernel-checked causal contract

[`StreamingLowTiming.lean`](../../Pinwheel/Program/StreamingLowTiming.lean)
provides a source-level condition independent of these finite probe patterns:

- `low_prefix` preserves LOW, pins, current instruction, and remaining count
  while decrementing the countdown exactly under ordinary inputs.
- `low_interval` derives countdown zero and the next actual transition to HIGH.
- `stable_sample_delay` derives the second sampler's selected bit after two or
  more ordinary stable samples, with unrestricted initial sampler contents.
- `low_capture_stable` starts in LOW with countdown at least two, a receiving
  stream cell, an ordinary wait list of exactly that countdown length, and the
  selected raw bit equal to the expected value on every wait edge. It derives
  the actual capture predicate, `rxEvent = [expected]`, and the next HIGH phase.
  It does not assume that capture occurred or that the received trace agrees.

At reservation, a declared half-period `H` loads countdown `H-1`. The protocol
helper bound `H >= 3` supplies `H-1 >= 2`. The peer-side obligation is explicit:
its selected raw input must already be stable from the first LOW wait edge
after reservation through the wait window. In the tested one-cycle-response
callback model, this is the causal window after the preceding falling edge.
Initial synchronizer values are arbitrary. Queue stalls may extend the parked
LOW interval; the HIGH timing theorem remains independent of queue service.

The new module passed native Lean checks with warnings treated as errors. A
development audit of its imported Pinwheel/private declaration closure reported
5,887 declarations and 3,137 theorems using only the standard axiom allowlist.
This audit is separate from the campaign's fresh committed-source gate.

These are two-state digital source and finite Icarus results. They do not prove
electrical setup/hold margins, metastability resolution, CDC behavior, board
timing, technology-mapped equivalence, routed timing, or silicon operation.
