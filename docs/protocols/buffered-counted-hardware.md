# Compact counted programs in buffered hardware

Decision, 2026-10-06: implement timed counted schedules in the owned buffered
digital engine before choosing a memory backend. The target is
`pinwheel-buffered-counted32-v1`, implemented by `Hardware.Buffered.Counted`.
SPI and JTAG load different programs into the same emitted circuit. Loop
rollover installs the next timed instruction on the dispatch edge; it adds no
control-only clock to the waveform.

This advances the [Jane Street protocol-emulator goal](https://blog.janestreet.com/protocol-emulator-asic-competition/)
of programmable, precisely timed protocols and firmware flexibility after
fabrication. Early mapping measures the cost of that flexibility. The next
discriminator is reactive I²C on this ownership contract, followed by a memory
implementation that preserves the resulting fetch deadlines.

## Source, image and execution

The host accepts the timed subset of the shared `BufferedProgram` schedule:
blocks, sequences and up to two nested repeats, each with one through eight
iterations. Images contain at most 64 instruction leaves, 256 source syntax
nodes and 1,024 virtual positions. One final HALT or FAULT is outside all repeats.
The recursively derived TX/RX demands must match the source declarations and
fit the owned 32-bit buffers. Instruction durations are one through 256 edges.

The image retains the entire immutable source tree and its identity. Import
re-lowers that tree and checks every stored instruction and control record,
virtual span, buffer demand and image identity before transport I/O. Encoded
rows alone cannot recover the source's sequence grouping. Scratch capture,
WAIT, CHECKED, QUALIFY, branches, inverted SHIFT and preserved enable masks
remain outside this target's admitted subset.

The load/submit/wait/read/release API is the same for both uploaded protocols:

```python
from buffered_counted_hardware import BufferedCountedHardwareHost, compact_spi

host = BufferedCountedHardwareHost(transport)
host.initialize()
loaded = host.load(compact_spi(byte_count=4, half_cycles=4))
pending = loaded.submit(tx=b'\x96\xa5\x3c\xc3')
pending.wait(timeout_cycles=loaded.image.execution_edges + 2)
result = pending.read()          # Retained, nondestructive result.
pending.release()               # The loaded program can accept another payload.
```

`compact_jtag(bit_count=17, half_cycles=4)` changes the loaded source program,
using the same host and circuit. Custom timed schedules use the same
`BufferedBlock`, `BufferedSequence` and `BufferedRepeat` constructors as the
shared reference engine.

Each physical row packs the existing 32-bit timed instruction with 24 bits of
loop metadata. The circuit contains no SPI or JTAG dispatch. A timed word
chooses DRIVE, SHIFT, KEEP, HALT or FAULT, output levels/enables, duration and
optional input-0/input-1 append. SHIFT consumes the next TX bit; KEEP preserves
selected output levels. See the [linear word layout](buffered-hardware.md#programming-and-storage).

| Control bits | Meaning |
| --- | --- |
| 1:0 | Enclosing loop depth: 0, 1 or 2 |
| 7:2 / 10:8 | Outer start row / iteration count minus one |
| 16:11 / 19:17 | Inner start row / iteration count minus one |
| 20 / 21 | Last leaf of outer / inner body |
| 23:22 | Reserved zero |

Every leaf carries its enclosing bounds; ending flags identify body exits.
Inner rollover takes priority, preserves the outer index and jumps to the inner
start. Inner exit clears its index. Outer rollover increments its index and
jumps to the outer start; outer exit clears it. Sequential loops reuse the
counters after exit. Public `env0` is the innermost index and `env1` is the outer
index for depth two; for depth one, `env0` is its sole index and `env1` is zero.
Public `pc` names the stored row; `virtual_pc` names the source position.

The current descriptor cache stores its 22 meaningful bits. Uploaded rows
retain all 24 control bits, including reserved bits so execution can reject
them. Physical and virtual successor checks use wider intermediate values:
row 63 cannot alias row 0, and virtual position 1,023 cannot wrap to zero.
Invalid depth, reserved fields, loop starts, counter bounds or terminal
metadata fault before that entry's TX/RX effects. These are local execution
guards; raw hardware COMMIT does not certify the whole schedule tree.

| Four-byte mode-0 SPI representation | Count |
| --- | ---: |
| Virtual positions, including HALT | 66 |
| Source instruction leaves / total syntax nodes | 4 / 9 |
| Uploaded physical rows | 4 |
| Uploaded timed-word / control bits | 128 / 96 |
| Total uploaded program bits | 224 |
| Previous linear upload, 66 × 32 bits | 2,112 |

The two data leaves repeat eight times per byte and four times per transfer;
the tail deasserts chip select and halts. Lengths one, two and four and different
half periods reload this same circuit. A 17-bit reset-selected JTAG DR scan
uses 20 rows, 58 virtual positions and 1,120 uploaded bits, including its
distinct final TMS bit. The frontend admits one through 32 bits; wire fixtures
cover widths 1, 7, 13, 17 and 32 across all 16 starting TAP states.
This frontend assumes a DR selected by reset; IR selection and
multi-device chain discovery need separate programs and evidence.

## Ownership and timing

Commands retain the [linear ownership contract](buffered-hardware.md#ownership-and-entry):
coverage-tracked WRITE, COMMIT, generation-bound START, nondestructive indexed
read and identity-matched RELEASE. WRITE atomically supplies `word` and
`control`. COMMIT snapshots the physical count, virtual span and idle profile,
then clears unused rows. The loaded host handle is reused across payloads.
START copies TX and reserves RX; running and retained transfers block reuse.
Host wait timeout preserves its pending handle. Faults and completion restore
idle pins and retain results until release. Reset and finite counter saturation
keep the prior session rules.

Timed entry uses the pre-edge second input sampler. TX consumption precedes
RX append; underflow prevents append, while overflow retains successful TX
consumption and the preceding RX prefix. Held duration edges do not advance
the virtual PC or repeat counters and do not repeat data effects. Rollover
dispatch enters the next leaf immediately, including duration-one instructions.

The wire differential explicitly binds reference sampler state at START and
requires the first leaf to have no RX append. Both supplied frontends satisfy
that condition. Separate raw command fixtures check first-entry capture with
primed pads and distinguish both input selections. This is the comparison's
stated initial relation; it does not establish every reference-constructor
start condition as a hardware lifecycle theorem.

## Circuit cost and verification

| Declared state owner | Bits |
| --- | ---: |
| 64 packed timed/control rows | 3,584 |
| Upload coverage mask | 64 |
| Owned TX / retained RX | 32 / 32 |
| Other control, loop, identity and sampler state | 148 |
| Total | 3,860 |

The register-backed implementation deliberately gives lookup an explicit
baseline. Four physical rows are an upload count, not the circuit's allocated
store. Repeats increase virtual capacity while the distinct-leaf limit falls
from 128 linear rows to 64 counted rows. Cost comparisons must retain that
capacity difference rather than treating syntax compression as universal area
savings.

The accepted mapping uses the same pinned CMOS5L library and models as the
linear baseline. All 3,860 logical state bits survive both saved mappings,
including every timed-word, control, coverage and TX/RX bit.

| Complete register-backed target | Linear baseline | Counted target |
| --- | ---: | ---: |
| Declared / mapped flip-flops | 4,389 | 3,860 |
| Generic cells | 26,438 | 23,638 |
| Typical CMOS5L cells | 24,671 | 20,674 |
| Typical standard-cell area, µm² | 400,519.6524 | 350,479.332 |
| Typical sequential area, µm² | 215,011.8432 | 189,096.768 |

Typical cell area falls 12.49%, while the distinct-row capacity changes as
described above. The state saving is 512 fewer allocated bank bits plus 64
fewer coverage bits, offset by 47 additional control bits. These are mapped
cell sums, not placed area, die fit, routed timing or electrical qualification.

Forty-three named local Lean proofs cover entry, ownership, bounds, sampler
age, counter rollover, same-edge dispatch and finite identities. Directed
execution checks actual typed `Counted.Schedule.locate` for a SPI-shaped nested schedule and a
nested-loop/tail/adjacent-loop fixture. These are local universal equations and
finite schedule witnesses; a complete initialized compiler/package refinement
is a further proof obligation.

The gate exports actual circuit command states and MLIR, compiles emitted RTL
and compares all 23 public fields. Independent command expectations exercise
nested and adjacent loops, duration holds, malformed records, row-63 and
virtual-1,023 falloff, retained prefixes, sampler age and both input selections.
Wire cases compare the source engine's execution, stored-row geometry and
lookup environment at each active edge, with independent SPI and JTAG peers.
`reference_edges` also counts retained result observations; it is not a count
of execution-only edges. `fetch_environment_checks` includes held active edges.

Saved generic and typical CMOS5L mappings are independently read back. Exact
state cuts compare all public outputs and each represented next-state bit for
arbitrary defined inputs and represented state, without a reachability or
initialization assumption. Deliberate sampler-age, input-selection, inner-loop
rollover and mapped-output corruptions must fail. Full Python regressions run
both normally and under `-O`; the portable foundation includes the new
`BufferedCountedHardware` suite and whole-library custom-axiom rejection.

Accepted hardware run: `buffered-counted-hardware-01`, 525.507 seconds,
report SHA-256
`8bfa4ec9183c4eadae71af7ceeaf18982b54e440fc2dd96e56d9096bed8500ad`.
Its 96 command cases cover 3,878 edges with 1,275 independent state checks and
all 64 three-edge raw input histories. Emitted RTL passes 1,027 SPI and 242
JTAG cases, 407,666 compared reference observations and 332,692 active lookup
checks. Each saved mapping replays all command cases plus 19 SPI and 20 JTAG
wire cases. All three execution mutants and both mapped-output mutants reject.
Python discovers 964 tests in both modes, with two platform-specific skips.
The whole-library audit checks 23,409 declarations and 12,541 theorems using
standard axioms only, and rejects the custom-axiom mutation.

The full portable run `buffered-counted-foundation-01` also passes: 273 library
modules, 47 executable suites and one kernel suite in 1,505.787 seconds.
Its report SHA-256 is
`8f57b5c7484ae944e07292865f27a9cb0af08d5391fc10481139b8694611ce15`.
The tracked manifest binds 669 frozen inputs and 124 generated artifacts across
both completed runs, with all 414 predecessors unchanged.

The initial development mapping (`counted-transport-dev-01`) stopped at exact
state intake: its declared cache had 24 bits but emitted readback had 22. The
cache now honestly stores 22 meaningful bits while uploaded descriptors retain
24. The failed assembly/readback and peer smoke bytes remain preserved; the
accepted report comes from the fresh final run.

## Reproduction and continuation

```sh
python3 -B scripts/check-foundation.py --tag <fresh-foundation-tag>
python3 -B scripts/check-buffered-counted-hardware.py --tag <fresh-hardware-tag>
```

The hardware gate needs pinned Lean, CIRCT, OSS CAD and the pinned CMOS5L
standard-cell library/models. `--pdk-root` accepts a standard-cell directory
with `lib/` and `verilog/`. Tool wrappers, native binaries, source and selected
library/model bytes are hashed; every run uses a fresh output directory.
On a fresh checkout the gate reconstructs the predecessor map from the
[tracked manifest](../../physical/experiments/buffered-counted-hardware-results.json),
checks its digest and verifies all 414 historical hardware/physical files.
Emitted artifacts live under ignored `build/`; retain the accepted run directory
alongside the manifest if exact artifact replay is needed.

Next, implement reactive entry/hold/branch decisions against the same owned
buffers and compact lookup. Use multi-byte I²C, early NACK and stretch timeout
to check data, scratch and failure timing. Then choose a register/SRAM fetch
implementation against the measured dispatch deadlines, including one-cycle
and loop-exit paths. Existing paired fetch logic is a useful comparison, but
its operand/result widths and session contract need explicit reconciliation.
Serial loading, FPGA/board execution, physical pads, routed timing, SRAM
qualification and package power each retain their own evidence gate.
