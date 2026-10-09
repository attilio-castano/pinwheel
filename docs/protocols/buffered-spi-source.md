# Buffered SPI source-to-resident bridge

The design question is whether a short, reusable SPI source really identifies
the program admitted by the buffered SRAM controller. The explorer's
[Program to pins session](../explorer/index.html#session) makes that connection
inspectable through source, exact image, accepted loading, pin execution and
retained result ownership. It is also a place to expose the next proof gap.

This continuation adds a bounded kernel bridge and an independently checked
finite session. It changes no execution hardware, image ABI or serial frontend.

## Kernel boundary

[BufferedSPI.lean](../../Pinwheel/Program/BufferedSPI.lean) constructs mode-0
SPI for one through four bytes and three through 256 controller edges per
half-period. SHIFT supplies MOSI from the transfer buffer; KEEP raises SCLK and
appends sampled MISO. An eight-bit inner loop and byte-count outer loop reuse
those two leaves, followed by a final low interval and HALT. TX payload belongs
to START rather than the resident instructions.
The timing range bounds the constructor; the bridge does not prove correct SPI
sampling for every peer environment at every supported half-period.

`geometry` proves four stored leaves, two loops and `16 * bytes + 2` virtual
entries. `fetch_shape` proves the source's virtual address decoding. Neither
theorem is an execution simulation.

[SpiSource.lean](../../Pinwheel/Hardware/Buffered/SpiSource.lean) supplies a
supported linear encoder and independent decoder. `linear_round_trip` covers
all four leaves and all 256 representable duration fields using kernel
evaluation. The source constructor selects the sampled timing range above.
The module constructs compact words, counted-loop metadata and the zero branch
dictionary, then proves their full-register resident expansion.

`initialized_source_reference` derives the exact source-constructed resident
image from an actual cold-initialized loading history ending VALID. The
`SourceHistory` premise constrains operands only when the controller accepts a
row, descriptor or COMMIT. Rejected noncanonical commands remain unrestricted.
The proof derives the four-row count and image equality from accepted-upload
knowledge; it does not assume matching SRAM banks or initial responses.

`initialized_spi_observe` composes that image with the existing initialized
binary execution theorem. Every public observation after every permitted
runtime prefix agrees with the independent full-register Reactive circuit
loaded with the source-constructed words. Its initial nonword core is the
actual VALID cut. The history premise uses one fixed SPI configuration, and
the runtime keeps that image fixed. Replacement by a different configuration
is exercised separately in the finite session below.
Permitted runtime inputs exclude loading, COMMIT and reset commands, including
rejected writes; their rejection behavior is finite session evidence.

The universal correspondence between `Buffered.run` source execution and this
binary circuit remains open. The new encoder is not a universal proof of the
Python compiler, and the theorem does not compose serial request delivery,
emitted RTL or physical timing.

## Recorded controller session

[ExplorerBufferedSession.py](../../scripts/ExplorerBufferedSession.py) lowers
the existing canonical Python source and checks both image records against
fresh exports of the typed Lean constructor. Changed word, loop-control,
dictionary-index and dictionary entries are refused by canonical admission.

The exporter replays all 691 controller edges through the typed digital
`SramModel`, starting its two SRAM replicas and the independent full-register
reference from different arbitrary contents. It compares complete core state,
public outputs and resident storage/response invariants. Selected initialization,
COMMIT and START boundaries also compare the ordinary function-valued
`SramState`. An independently resolved SPI peer provides the inputs and checks
the source execution, pin commands and decoded retained results.

| Transfer | Resident program | TX | Decoded RX | Execution edges |
| --- | --- | --- | --- | --- |
| First | Four bytes, half-period 4 | `96 a5 3c c3` | `a6 9b 42 e1` | 260 |
| Reuse | Same admitted image | `12 34 56 78` | `de ad be ef` | 260 |
| Replacement | One byte, half-period 6 | `a5` | `3c` | 102 |

The session includes incomplete COMMIT, writes while busy or retaining a
result, indexed result reads, stale RELEASE and matching RELEASE. Reuse changes
the payload without program writes. Replacement changes source geometry and
clock period on the same controller after releasing ownership.

Frames display post-edge state, except `rejected`, which reports command
admission before the edge. Raw inputs enter sampler stage 1 on that edge;
receive append reads the pre-edge stage-2 sample. The peer fixture uses one
edge of callback delay and `tCO=1`. This is finite digital evidence at the core
command boundary, with source hashes; it is not serial upload or silicon data.

## Use the HTML to guide the next change

The session reveals three useful design constraints. Program identity and
transfer payload are separate; reuse should preserve the former. Result reads
do not relinquish ownership; replacement must wait for a matching release.
Finally, four compact rows still require all sixteen branch descriptors under
the current ABI, even for this branch-free program. Each image therefore
uploads 1,264 logical data bits across twenty writes. The two instruction SRAM
replicas allocate 8,192 bits regardless of this program's size; neither number
is serial traffic or a new physical area measurement.

Keep those facts visible when proposing a storage or loading change. The
[source/image continuation](buffered-source-execution.md) now covers SPI and
reactive I²C interpreter execution. Connecting that interpreter to packed
circuit state is the next gate. Compiler, serial, electrical SRAM/CDC, RTL and
physical-chip qualification retain their separate gates.

## Reproduce

From the repository root with the pinned Lean toolchain:

```sh
lake build
lake env lean -DwarningAsError=true test/ProofAudit.lean
lake env lean --run test/BufferedSpiSource.lean 4 4
lake env lean --run test/BufferedSpiSource.lean 1 6
python3 -B scripts/ExplorerBufferedSession.py
python3 -B scripts/build-explorer.py --refresh-receipts
python3 -B scripts/build-explorer.py --check
```

The session exporter executes the comparisons and writes the ignored local
output `build/explorer/buffered-session.json`. `--refresh-receipts` validates
the regenerated evidence and updates the concise tracked
[recording receipts](../explorer/recordings.json) and standalone HTML. Normal
builds and `--check` require the recording to match those receipts. Bundle
validation checks source freshness, canonical image bytes, decoded display
fields, structural consistency and source navigation; it does not rerun Lean
execution.

On a fresh checkout, the builder can recover this frozen session from the
committed HTML and validate or rebuild the bundle using Python alone. When a
local export exists it takes precedence; changed recording source bytes require
the full exporter/replay above. After refresh, inspect loading rejection, both
completed payloads, matching releases, replacement and input/fetch details in
the browser. The [explorer workflow](../explorer/README.md) describes the other
recordings and the offline artifact.

The [source/image interpreter continuation](buffered-source-execution.md) now
proves arbitrary SPI execution prefixes after independently decoding this
resident image and adds a fixed reactive I²C case. The remaining state relation
connects that interpreter to the actual packed-register circuit.
