# Buffered latency-one SRAM hardware

Decision, 2026-10-07: implement the conservative two-candidate hybrid below the
shared programming layer. The separately versioned target is
`pinwheel-buffered-shared-branches32-sram64-v1`. SPI, JTAG and I²C retain the
same `BufferedProgram`, sixteen-descriptor admission bound, command widths,
owned TX/RX lifecycle and waveform edges as the
[shared-branch register target](buffered-storage-fetch.md).

This advances post-fabrication programmability by changing where uploaded
instructions reside while preserving the common execution interface. It is an
opt-in parallel target. Serial/package integration and physical qualification
remain distinct work.

## Storage and request schedule

The controller retains 64 × 28 metadata bits, sixteen × 56 dictionary bits,
coverage, execution and owned data registers. Two pinned single-port 64 × 64
SRAMs each store the complete instruction bank. Accepted row writes broadcast
the complete instruction to both copies and hold their registered responses.
Other edges read independently addressed candidates. No physical reset or
assumption of equal initial arrays/responses is introduced.

The controller has 117 declared registers and 3,151 FF bits, including a
64-bit row-zero mirror updated by every accepted WRITE0. The mirror supplies
START immediately after COMMIT or matching release, without another waveform
edge. Coverage requires a fresh row-zero write before an image becomes valid.
The SRAMs allocate 8,192 instruction bits and contain their own registered
responses; these are separate from the controller FF count.

Each read address is a hypothetical successor of the actual prospective core
state after the current edge. Both branch choices are fetched together. On the
following edge, the registered branch decision selects the response; metadata
is selected at the actual entry PC and the dictionary stays combinational.
This renews both candidates when one one-cycle CHECKED instruction enters
another. Sequential candidates include inner-loop rollover, outer-loop
rollover and exit. WAIT and QUALIFY retain their existing release edges.

Candidate expressions use phase, PC, current control, loop indices and cached
branch endpoints. They do not read scratch, either sampler stage or raw inputs.
The complete next core still uses the existing sampled input semantics. No
first-stage synchronizer prediction, response tags or extra dispatch clocks
are added.

COMMIT leaves physical SRAM tail cells untouched. The controller count-gates
the complete compact 92-bit row before dictionary expansion. This matters
because descriptor zero can be nonzero: the projection preserves the
predecessor's zeroed compact-row representation and subsequent dictionary
lookup. The existing entry bounds check separately rejects a tail before pin
or TX/RX effects. Metadata tail clearing and upload coverage
retain their existing command semantics. The first accepted row/table write
invalidates the resident image; active and retained transfers reject writes.
There is one image bank and one finite transfer owner.

## Programming and loading

```python
from buffered_sram_hardware import BufferedSramHardwareHost
from buffered_reactive_hardware import compact_i2c_read
from buffered_i2c import register_read_tx

host = BufferedSramHardwareHost(transport)
host.initialize()
loaded = host.load(compact_i2c_read(4, phase_cycles=4, wait_cycles=32))
pending = loaded.submit(tx=register_read_tx(0x53, 0xa6))
pending.wait(timeout_cycles=200_000)
result = pending.read()
pending.release()
```

The host uses a distinct image format/key so a shared-branch register image
cannot silently identify this hardware. Imported images reconstruct the source
lowering before transport I/O. The fixed sixteen-descriptor limit and all source
bounds remain explicit. The inline reactive target remains available when a
program needs more distinct descriptors.

## Proof and replay boundaries

`SramCandidates.lean` contains nineteen named local candidate/memory laws.
`SramProofs.lean` adds sixteen named laws connecting the actual typed
controller to request addresses, read/write exclusivity, SRAM edge behavior,
START storage and counted tail projection. `readAddress_postcore` proves that
materializing the actual core step and then evaluating each candidate gives
exactly the emitted request address. The executable closed-loop model uses
that identity to avoid repeatedly interpreting the full composed core graph.

At this hardware checkpoint, candidate availability assumes resident bank
agreement on live words, and complete behavior uses finite independent replay.
The subsequent [initialized loading proof](buffered-sram-loading.md) derives
that agreement and both candidate responses from any initialized accepted-upload
history ending VALID. It proves every fixed-image binary runtime prefix and
public observation agrees with the full-register Reactive circuit. The reference
starts with the actual cut core and independently tracked image. Universal source
compiler, serial delivery/package and physical refinement remain separate.

`MemoEval` batches the actual next-state expressions. Its logical definition
maps ordinary `Expr.eval`, and `nextSnapshot_eq` identifies the controller
snapshot with its ordinary typed step. The native implementation caches nodes
within one edge, retaining source objects and checking widths. Independent
ordinary-evaluation comparisons and actual-controller/predecessor boundary
comparisons qualify that execution path; the full hardware oracle remains the
unchanged predecessor exporter. The cache adds no circuit state or hardware
behavior. Universal native evaluation/compiler correctness remains outside the
kernel proof claim.

`MemoBind` keeps ordinary `Expr.bind` as its logical definition. Its executable
implementation memoizes shared expression objects with retained source keys
and checked widths. Independent ordinary-binding comparisons, composed
bindings, byte-identical small emitter comparisons and interpreter/native
exporter parity test the native implementation. These checks do not constitute
a universal native substitution, compiler or emitter proof.

The hardware gate compares closed-loop typed vectors with the unchanged
accepted shared-bank oracle, then replays the complete controller plus pinned
SRAM functional models. Seeded typed fixtures vary controller registers,
arrays and responses independently. RTL starts controller FFs unknown; its two
additional poison fixtures vary the macro arrays and Q independently.
Saved controller SAT uses unrestricted Q
inputs, so it establishes controller-to-mapping equality rather than memory
availability. Complete macro-bound replays provide the separate availability
witnesses. Binding readback and negative controls check replication, independent
addresses, broadcast writes, full-word masks and exact macro ports.

## Measured hardware acceptance

Full hardware run `buffered-sram-02` passes in 1,027.204 s. It verifies the
accepted shared-branch baseline artifacts and identical tool/library pins.
All declared controller state survives both mappings; no coordinates are
pruned or derived.

| Measurement | Shared-branch FF baseline | SRAM hybrid |
| --- | ---: | ---: |
| Controller declared/retained FF bits | 7,183 | 3,151 |
| Generic controller cells | 43,065 | 23,634 |
| Typical CMOS5L controller cells | 37,428 | 16,611 |
| Typical summed standard-cell area, µm² | 644,939.6310 | 294,546.1050 |
| Typical sequential cell area, µm² | 351,886.5504 | 154,363.7088 |
| Allocated SRAM instruction bits | 0 | 8,192 |
| Summed macro footprints, µm² | 0 | 100,978.2656 |
| Standard-cell area plus macro footprints, µm² | 644,939.6310 | 395,524.3706 |
| Generic maximum controller next-state levels | 91 | 92 |
| Typical maximum controller next-state levels | 43 | 42 |
| Generic maximum data-signal sink pins | 2,547 | 469 |
| Typical maximum data-signal sink pins | 10 | 10 |

Controller FF bits fall 56.13%. The typical standard-cell-plus-macro-footprint
sum falls 38.67%. The SRAM count includes replication rather than substituting
one isolated macro's area for the whole target. Each macro measures
784.48 × 64.36 µm. Its internal registered Q is included in macro geometry,
not counted as controller FF state. Neither area sum includes pads, serial
transport, clock tree, placement, routing or halos.

The prospective memory address outputs have 99 generic and 43 typical cell
levels. These paths are distinct from the listed controller register next-state
depths. The graph screen includes neither SRAM clock-to-Q/address setup nor
wire delay and electrical loading. It establishes no frequency or routed fit.

Three interpreted/native cases and 123 edges produce byte-identical vectors,
MLIR and register metadata. Four supervised native workers export 232 cases and
11,892 edges in 6.416 s, enforcing all 309,192 public-field comparisons with the
unchanged predecessor oracle and 10,144 independent specified states across
64 raw-input histories. Four new 128-edge CHECKED histories exercise continuous
one-cycle branch-to-branch execution. The full-address fixture executes all
64 rows, multiple WRITE0 updates and a short replacement with descriptor zero
nonzero.

The portable closed-loop fixture compares nine independently seeded cases and
1,410 edges, including ordinary-evaluation boundary checks for both actual and
predecessor snapshots. Candidate tests cover 6,144 address/dependency cases,
three loop transitions, sixteen START cases and independent SRAM initialization.
Memoized substitution compares 10,240 ordinary bindings plus 1,280 composed
bindings and sixteen byte-identical small emitter artifacts. Memoized evaluation
compares 197,280 ordinary results over 6,936 heterogeneous roots.

Actual emitted RTL passes 2,311 wire cases: 1,027 SPI, 242 JTAG and 1,042 I²C.
It checks 1,509,697 source observations, 1,366,449 fetch/environment states and
1,515,348 independently derived sampler states. Three NACK stages and five
stretch/STOP timeout fixtures retain exact diagnostic prefixes. Indexed result
reads remain identical twice and host wait timeout preserves the transfer owner.
Both extra independently poisoned macro fixtures pass all 232 command cases.

Saved generic and typical controllers each pass unrestricted-Q, arbitrary
represented-state SAT against emitted outputs and every next-state coordinate.
After reconnecting both macros, each passes all 232 command cases and 58 wire
cases, with 47,381 independent sampler checks. Exact macro census, port directions,
controller aliases and wiring survive each complete readback. Single-response,
missing-broadcast and incomplete-word mutants reject; each mapped-output negative
also rejects. Standalone pinned-macro tests check 197 access edges and five
wiring/edge mutants. Normal and optimized Python each pass 1,057 of 1,059 tests;
two Linux-specific checks skip on this host.

Hardware report SHA-256:
`49bbe82bc6a85131e1ab10917c12c25701bb0cdaa5375b4567c5982260ed92e1`.
Full portable foundation `buffered-sram-foundation-02` passes in 1,758.924 s:
285 modules, 55 executable suites and one kernel suite. The whole-library audit
checks 25,185 declarations and 13,492 theorem constants, with standard axioms
only; the injected custom axiom is rejected. Foundation report SHA-256:
`b3277d9ddf146a6ffc0df5b2e7ef3efa3b72375804428ec25201d717929de72e`.

The [tracked acceptance manifest](../../physical/experiments/buffered-sram-results.json)
binds both reports, 733 frozen inputs, 212 accepted artifacts and all 427
predecessor hardware/physical file hashes. Closeout checks current bytes and the
unchanged `2aa8692` snapshot. Artifact pins identify local evidence; the manifest
does not itself back up ignored run files.

Development receipts preserve the interrupted initial fixture, three bounded
180/180/600-second attempts, two stopped first gate runs and a 32-edge timing
probe. The original fixture/source capture limits are explicit. Ordinary shared
graph evaluation was CPU-bound with stable memory. Batch evaluation retains the
full 1,410-edge comparison rather than reducing it. Forty-seven separately pinned
development files include those logs, diagnostic sources and passed macro-binding,
oracle and fixture probes; none substitute for final acceptance.

## Reproduce

The hardware gate needs the unchanged accepted shared-branch artifacts, the
pinned local CMOS5L tools/library and macro views from
`tools/storage-macros.json`. The portable foundation needs only the pinned Lean
toolchain and Python; its fixtures are embedded in tracked source.

```sh
python3 -B scripts/check-foundation.py --tag <fresh-foundation-tag>
python3 -B scripts/check-buffered-sram.py --tag <fresh-hardware-tag>
python3 -B -m unittest discover -s test -p 'test_buffered_sram*.py'
python3 -O -B -m unittest discover -s test -p 'test_buffered_sram*.py'
```

Macro footprints and summed standard-cell area exclude placement, halos,
clock-tree and route geometry. Cell-graph logic levels omit SRAM clock-to-Q,
address setup, electrical loading and interconnect delays. This implementation
does not qualify a macro, synchronizer, package power or routed chip timing.
