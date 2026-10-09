# Pinwheel design explorer

Open [index.html](index.html) in a browser. The page contains its data, styles,
scripts and source excerpts, so it works offline without a server or dependencies.
Source dialogs also link to the full local file. They offer the corresponding
GitHub revision when its bytes match the snapshot and that revision is reachable
from a local `origin` tracking ref.

The architecture view explains both current paired and buffered SRAM designs.
It groups components by purpose; it is not a physical floorplan. Component
inspectors link owned state, update/consumer relationships and timing obligations
to implementation sources and scoped evidence. The decisions and evidence views
keep the historical routed Design A separate from current-source capabilities.

## Use it during design

Treat the explorer as a place to inspect a design question against an exact
implementation. Start with the component or transition that owns the question,
follow its source and evidence, and make the unresolved obligation explicit.
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

The committed `index.html` retains the frozen recordings needed for offline
use. [recordings.json](recordings.json) keeps concise source and semantic-hash
receipts for them. The large I²C and buffered-session JSON exports are local
build outputs under the ignored `build/explorer/` directory.

From a fresh checkout, Python can validate the retained recordings or rebuild
the page without running Lean:

```sh
python3 -B scripts/build-explorer.py --check
python3 -B scripts/test-explorer-recordings.py
python3 -B scripts/build-explorer.py
```

The builder uses a local `build/explorer/` recording when present; otherwise
it reads the matching frozen recording embedded in `index.html`. Both paths
check the tracked receipts, source bytes, image fields, session structure and
source references. Rebuilding refreshes the presentation and source excerpts;
it does not execute the model again. Changed recording sources require the
corresponding exporter and replay below.

## Refresh from source

From the repository root, using the existing pinned Lean toolchain:

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
the regenerated recordings and updates both `recordings.json` and the
standalone HTML. Normal builds and `--check` require matching receipts;
they do not accept a changed recording as a new result.

The trace exporter records the repository base and SHA-256 hashes of its source
inputs. Generation is deterministic for those inputs. The page builder refuses
a trace with changed source bytes, validates every
source path/range and embeds the actual referenced excerpts. It suppresses
revision links for excerpts that differ from the Git base, are new local files,
or belong to a commit absent from local `origin` tracking refs. This uses local
Git knowledge; generation does not contact GitHub.
The trace keeps its original generation revision; unrelated commits do not
invalidate it when every recorded source hash still matches.

The buffered exporter also compares the exact Python images to fresh typed
Lean constructor exports. The builder rechecks image bytes, decoded instruction
and loop descriptions, storage accounting and session structure. These bundle
checks do not re-execute the Lean model; regenerate the recording for that.

`content.json` contains curated component descriptions, claims and design
decisions. Review those descriptions and their line references when the design
changes; excerpt validation alone cannot establish that prose is still accurate.
`explorer.template.html` owns the UI, while `index.html` is its generated bundle.
The generated HTML and UART/SPI waveform snapshots are collapsed in GitHub
diffs; the template, descriptions, exporters and recording receipts remain
visible for review.

After refresh, inspect both targets, source dialogs, all four SPI modes, I²C
ACK/NACK/timeout outcomes, the buffered loading/reuse/replacement session,
event jumps and playback controls in a browser. Check
a narrow window as well. The explorer's
checks establish content and presentation consistency; hardware qualification
continues to use the repository's existing validation workflows.
