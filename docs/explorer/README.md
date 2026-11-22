# Pinwheel design explorer

Open the [interactive design explorer](https://attilio-castano.github.io/pinwheel/)
directly in your browser. For offline use, run `python3 -B scripts/build-explorer.py`
from the checkout and open `build/explorer-site/index.html`. The page contains its data, styles,
scripts and source excerpts, so it works offline without a server or dependencies.
Recording source dialogs show the verified historical Git tree. Editorial
source dialogs show the current checkout and offer a local source link when
opened from disk. Both link to GitHub when their source revision is known to
an `origin` tracking ref at build time.

The default **Start here** view introduces the project through a recorded demonstration:
run a four-byte SPI transfer, change its payload while reusing the same program,
then replace the program to send one byte with a slower clock. The circuit stays
fixed across those three transfers. This is playback of a buffered digital SRAM
model, not a browser simulation or a demonstration of physical silicon.

This overview also gives a dated progress summary and entry points into the
engineering. **Architecture** explains both current paired and buffered SRAM
designs; its component map is not a physical floorplan. **Program to pins** opens
the exact session, source and execution-proof links. **Protocol walkthroughs**
offers UART, SPI and I²C recordings. **Design decisions** and **Evidence & source**
explain the reasoning and checks. These views keep the historical routed Design A
separate from current-source capabilities and the opt-in buffered continuation.

## Use it during design

Start with **Start here** for the project story and visible behavior. To inspect a
design question against an exact implementation, open the component or transition
that owns the question, follow its source and evidence, and make the unresolved
obligation explicit.
For example, changing program storage requires checking both uploaded capacity
and whether the next instruction is available on its required edge.

The **Program to pins** view follows a bounded buffered SRAM SPI session through
source, concrete image, accepted loading, execution and retained ownership.
Each connection states whether it is a kernel theorem, a finite executable
comparison or an open obligation. Read that boundary before generalizing a
recording to another program or implementation.

The execution-link panel compares parametric SPI and the fixed four-byte
reactive I²C source. Both have kernel source/decoded-image interpreter proofs
for arbitrary execution prefixes and inputs. The connection to packed circuit
state remains open and is drawn separately. Selecting I²C changes the proof
scope shown in that panel; the recorded SRAM waveform still follows SPI.
[The source-execution study](../protocols/buffered-source-execution.md) owns the
exact theorem boundaries and focused reproduction gate.

The session executes three transfers across 691 actual digital SRAM-model
edges: four-byte SPI, another payload using the same image, then a one-byte
replacement with a slower clock. Source and independently resolved peer
execution, typed SRAM/public state and the full-register reference are compared
by the exporter. The [SPI bridge study](../protocols/buffered-spi-source.md)
owns the kernel premises, finite evidence and next obligations. Frames are
post-edge except command rejection, which records admission before the edge.

When a design changes, refresh the recordings and their source snapshots,
inspect successful and rejected transitions, and update the associated design
question. A clear graph is a navigation aid; the linked checks establish what
the design actually supports.

## Protocol recordings

The walkthroughs play frozen Lean model executions. The browser displays recorded
states; it does not simulate a protocol. Each recording identifies its source
bytes, input convention and evidence scope. These are digital model observations,
not paired RTL, silicon, serial transport or physical timing measurements.

### UART

The first walkthrough uses byte `0x53` and four intervals per symbol. Its frozen
data comes from `Compile.UART.program` and `Compile.UART.execute` in the original
32-slot timed Engine reference. All 42 states are checked against the independent
UART waveform and transmitter busy state, plus exact completion and boundary
checks. The recorded PC/countdown belong to that model. The paired path embeds
and widens this program; the recording describes the original reference engine.

There are ten four-interval actions followed by HALT. Cycle zero is the interval
immediately after action entry; cycles 0–39 are busy and 40–41 are completed.
When stopped, PC and remaining counter are absent. The HALT row is highlighted
to explain completion, not to claim that stopped state has PC 10.

### SPI

Four recordings transmit `0xa6` and receive `0x96`, one for each CPOL/CPHA mode,
with four cycles per half-period. The compiled Reactive program is checked at
every cycle against the independent SPI transaction reference, waveform and
capture contracts. Displayed MISO is the input consumed on that cycle's edge;
package input latency and electrical timing are outside this fixture.

The eight samples occupy capture slots 0–7 in wire order. Their packed register
value is `0x69`; decoding the MSB-first transfer gives `0x96`. An untouched slot
shows a dot, while an observed zero shows `0`.

### I²C

Four environments execute the same canonical 115-row one-byte write image:
normal acknowledgments, three-cycle clock stretching after each SCL release,
address NACK, and SCL held low until bus qualification times out. The exporter
checks every image record and execution edge against the independent I²C
reference using an edge-driven resolved-wire peer.

The displayed bus is resolved from the controller and target's pull-low commands
and is consumed on the next engine edge. Capture markers identify the preceding
edge's observation. Slots 0 and 1 hold address and payload ACK flags: zero means
ACK, one means NACK. The NACK path completes STOP while skipping the payload;
engine completion and protocol success are separate. The stuck-clock path times
out before START, releases the controller drivers and has no completed result.

The wait budget displays the number of blocked observations remaining, including
the last allowed one. Use event jumps to find ACK captures, branches and STOP,
or the 48-interval window to inspect a short part of a transfer. The program pane
follows the current PC; its full view also shows rows skipped by the selected case.

## Validate or rebuild the retained snapshot

The committed UART, SPI, [I²C](i2c-traces.json), and
[buffered SPI](buffered-session.json) JSON files contain the retained recordings.
[recordings.json](recordings.json) stores their source and semantic-hash receipts.
The builder renders them into a standalone page under `build/explorer-site/`.

From a fresh checkout, Python can validate the retained recordings or rebuild
the page without running Lean:

```sh
python3 -B scripts/build-explorer.py --check
python3 -B scripts/test-explorer-recordings.py
python3 -B scripts/build-explorer.py
```

Routine builds read the committed JSON files and check all recording digests,
source hashes and session structure. Source hashes and
recording excerpts resolve against the recording's verified Git tree, so
checkout edits can publish with the same recordings. A normal rebuild refreshes
the presentation and editorial source excerpts. To demonstrate behavior at a
new revision, rerun the corresponding exporter and replay below.

## Publish with GitHub Pages

The [Pages workflow](../../.github/workflows/explorer-pages.yml) publishes the
explorer when changes reach `main`; it can also be dispatched manually on `main`.
GitHub Actions fetches history, validates the retained recordings and source
inputs, rebuilds the page, then deploys only `index.html` at the website root.
Keep every verified source tree reachable in the fetched Git history. Source
excerpts are embedded, and recording links open the verified GitHub revision.

Pages uses GitHub Actions as its publishing source. Recording refresh runs the
Lean models and comparisons. Publishing checks and displays that retained
evidence.

## Refresh from source

From the repository root, using the existing pinned Lean toolchain and committed
recording inputs:

```sh
lake build Pinwheel.Compile.UART Pinwheel.Compile.SPITransaction Pinwheel.Compile.I2CWriteTransactionProofs
lake env lean --run scripts/ExplorerTrace.lean docs/explorer/uart-trace.json
lake env lean --run scripts/ExplorerSPITrace.lean docs/explorer/spi-traces.json
mkdir -p build/explorer
lake env lean --run scripts/ExplorerI2CTrace.lean build/explorer/i2c-traces.json
lake build Pinwheel.Hardware.Buffered.SpiSource Pinwheel.Hardware.Buffered.SramModel
python3 -B scripts/ExplorerBufferedSession.py
python3 -B scripts/build-explorer.py --refresh-receipts
```

The buffered exporter writes `build/explorer/buffered-session.json`. After
the exporters have rerun their comparisons, `--refresh-receipts` validates
the I²C and buffered SPI candidates from `build/explorer/` and writes them
to `docs/explorer/` as compact JSON. It also updates `recordings.json`
and rebuilds the offline page. Routine builds and `--check` require matching
receipts for the retained JSON.

Each exporter records a generation revision and SHA-256 hashes of its input
files. The builder checks those hashes against the generation revision by
default. The `sourceTrees` bindings in `recordings.json` handle older traces
whose recorded bytes were first committed after their generation base. The
existing bindings resolve all ten retained traces to `c46786f2`, which contains
the matching source bytes. The original generation revisions stay in the traces.

The buffered exporter compares the exact Python images to fresh typed Lean
constructor exports. When accepting a new buffered receipt, the builder checks
image bytes, decoded instructions and loops, and storage accounting against
the model from the committed source inputs. Routine builds verify the accepted
receipt and the retained transcript, observations, and session structure.

`content.json` contains curated component descriptions, claims and design
decisions. Review those descriptions and their line references when the design
changes; excerpt validation alone cannot establish that prose is still accurate.
`explorer.template.html` owns the UI. GitHub collapses generated waveform JSON
in diffs. The template, descriptions, exporters and recording receipts are
visible for review.

After refresh, inspect both targets, source dialogs, all four SPI modes, I²C
ACK/NACK/timeout outcomes, the buffered loading/reuse/replacement session,
event jumps and playback controls in a browser. Check
a narrow window as well. The explorer's
checks establish content and presentation consistency; hardware qualification
continues to use the repository's existing validation workflows.
