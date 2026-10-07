# Owned buffered SPI in a programmable digital circuit

Decision, 2026-10-06: implement the first digital slice of the
[shared buffered contract](buffered-reactive.md) with dedicated TX/RX registers
and a reloadable linear instruction bank. The target is
`pinwheel-buffered-linear32-v1`. Its parallel command interface supports
simulation and synthesis. The retained paired SRAM chip and serial interface
keep their existing contracts.

## Programming and storage

`Hardware.Buffered.Linear` is a typed circuit with no protocol dispatch.
Programs choose DRIVE, SHIFT, KEEP, HALT or FAULT. Timed instructions last one
through 256 edges. SHIFT consumes the next owned wire bit and sets one of three
output levels. KEEP preserves selected levels. Each timed instruction can append
either sampled input bit on entry. Output enables are literal fields.

The host lowers the supported linear subset of `BufferedProgram` into canonical
32-bit words, binding them to the full source identity and image version.
Waits, guarded/qualified actions, branches, counted schedules, scratch captures,
inverted/enable SHIFT and enable preservation reject before transport I/O.
This target does not yet implement the reactive I²C frontend.

| Stored resource | Bits |
| --- | ---: |
| 128 writable instruction rows | 4,096 |
| Upload coverage mask | 128 |
| Owned TX / retained RX | 32 / 32 |
| Other control, identities and sampler state | 101 |
| Total declared state | 4,389 |

Four-byte SPI uses 66 rows. Repeated transfers reuse the loaded image;
new lengths and timings reload the same emitted circuit.

| Instruction bits | Field |
| --- | --- |
| 2:0 | DRIVE=0, SHIFT=1, KEEP=2, HALT=3, FAULT=4 |
| 5:3 / 8:6 | Literal levels / enables |
| 16:9 | Duration minus one |
| 19:17 | KEEP level-preservation mask |
| 21:20 | SHIFT output selection |
| 23:22 | RX append: none / input 0 / input 1 |
| 31:24 | Reserved zero |

Unused operation fields must be zero; terminal words are exactly 3 and 4.
The host decoder rejects malformed words. A raw hardware upload may contain
them; execution then faults before that instruction's TX/RX effects.

## Ownership and entry

Commands are NONE=0, WRITE=1, COMMIT=2, START=3, RELEASE=4 and warm RESET=7.
A separate `initialize` input performs cold initialization. The transport
records the pre-edge `rejected` decision with the post-edge observed state.

WRITE invalidates the image and starts a coverage-tracked upload. COMMIT
requires every row below the requested count, snapshots count/idle and clears
the unused tail. START requires a valid image and matching generation,
copies TX data and reserves RX capacity. Running or retained ownership blocks
WRITE, COMMIT and START. Indexed RX reads are nondestructive; RELEASE requires
both matching identities. Host wait timeout retains the pending handle.
Successful decoding requires exact TX consumption and RX length; decode
rejection leaves the completion available for release.

Input pads pass through two sampler registers. Entry uses the pre-edge second
register, consumes TX before appending RX, and applies effects once. Underflow
prevents RX append; overflow retains successful TX consumption and the preceding
RX prefix. Malformed fetch, row-127 falloff and explicit FAULT retain a fault.
Every terminal outcome restores the committed idle profile.

Generation and global transfer counters are sixteen bits. Saturation blocks
COMMIT and START respectively; an existing last-generation image can still run
while transfer identities remain. Warm reset cancels ownership/image validity,
advances or saturates generation, and preserves the transfer counter.
Cold initialization clears counters and requires a fresh software session epoch.
Raw token uniqueness across external cold reset, power loss or reconnection
remains outside this session contract.

Hardware samples during idle/upload and resets sampler values to zero.
The reference `BufferedEngine` constructor starts them at three. The SPI
differential binds sampler state at START and uses a first leaf without RX.
Circuit/RTL vectors separately check first-entry RX with pads primed low.
This states the relation needed for comparison; it does not claim unconditional
equivalence between every reference constructor and hardware start.

## Reproduction and evidence

    python3 -B scripts/check-buffered-hardware.py --tag <fresh-tag>

The gate needs pinned Lean, installed CIRCT/OSS CAD tools and CMOS5L library
and simulation models. `--pdk-root` accepts a standard-cell directory containing
`lib/` and `verilog/`. Selected bytes are verified before use; native tools,
wrappers, models and sources are hashed. Runs preserve earlier reports.
The Lean circuit trace export can take several minutes before printing its result.

Before the first run in a fresh checkout, reconstruct the predecessor map from
the tracked manifest. This verifies the same 411 preserved files rather than
treating the new checkout as a fresh preservation baseline:

```sh
python3 -B - <<'PY'
import hashlib, json
from pathlib import Path
manifest = json.loads(Path('physical/experiments/buffered-hardware-results.json').read_text())
record = manifest['preservation']
data = (json.dumps({k: record[k] for k in ('base', 'prior_sha256')}, indent=2) + '\n').encode()
assert hashlib.sha256(data).hexdigest() == record['baseline_map_sha256']
path = Path('build/buffered-hardware/baseline-preservation.json')
path.parent.mkdir(parents=True, exist_ok=True)
if path.exists():
    assert path.read_bytes() == data
else:
    path.write_bytes(data)
PY
```

Twenty-six named local circuit proofs cover entry, capacity under stated
premises, sampler age, retention, admission and finite identities. Directed
Lean tests exercise counter-boundary snapshots. Whole-library axiom auditing
rejects an injected custom axiom. No complete initialized compiler/package
refinement is claimed.

Actual circuit traces are replayed through emitted RTL and saved generic and
typical CMOS5L gates. Independent command expectations cover upload, fault
priority, sampling, reset and release. SPI execution is compared to the existing
reference and checked by a resolved-pad peer without program/cursor access.
Payload sweeps, length/timing reloads and repeated retained reads use the same
circuit. Moving RX capture to the first sampler stage must fail these traces.

Saved Verilog is read back before resource census. An exact state cut binds
every surviving bit; SAT compares all public outputs and surviving logical
next-state bits for arbitrary defined inputs/state, with inverted-output
negative controls.
The [accepted manifest](../../physical/experiments/buffered-hardware-results.json)
binds final reports/artifacts and preserved preceding hardware/physical files.

Accepted run `buffered-spi-hardware-01` completed in 698.785 seconds on the
frozen implementation commit `d67fbe0`.

| Accepted check | Result |
| --- | --- |
| Actual Lean circuit versus emitted RTL | 76 cases, 1,920 edges, all 20 public state fields |
| Independent command expectations | 714 state checks, including 64 raw-input histories |
| Emitted SPI versus reference and resolved-pad peer | 1,027 transfers, 350,864 reference execution edges |
| Saved generic and CMOS5L gate replay, each | Same 76 control cases and 19 SPI transfers |
| Mapping SAT, each | All public outputs and all 4,389 next-state bits; zero pruned coordinates |
| Negative controls | Custom axiom, early RX sampling and both inverted gate outputs rejected |
| Normal / optimized Python, each | 926 passed, two platform skips |
| Frozen-input closeout | 659 source/tool/model inputs and 60 artifacts verified |
| Preceding evidence | All 235 physical and 176 hardware files unchanged |

The SPI sweep varies every byte value in each of four lanes, totaling 1,024
four-byte payloads. Three additional transfers reload lengths/timings
(one byte at H=3, two at H=7 and four at H=256). The same emitted circuit
uses four images and 184 uploaded words; repeated payloads reuse their image.
Every transfer recovers from a zero-budget host wait, reads retained RX twice
and releases with the matching identities. This is finite digital evidence.

| Saved implementation | Cells | Flip-flops | Standard-cell area |
| --- | ---: | ---: | ---: |
| Generic gates | 26,438 | 4,389 | — |
| Typical CMOS5L | 24,671 | 4,389 | 400,519.6524 µm² |

The instruction bank accounts for 4,096 of 4,389 physical state bits (93.3%).
Typical sequential-cell area is 215,011.8432 µm². These measurements make
instruction storage and lookup the next architectural cost question.

Mapped area sums Liberty standard-cell areas. Clock distribution, placement,
routing, parasitics and physical timing remain unqualified. Use this register
store as the measured behavioral baseline for SRAM-backed instruction storage,
compact counted lookup and reactive control. Preserve dispatch deadlines and
failure prefixes, then integrate serial commands and initialized package
lifecycle. Physical sampling, SRAM qualification and package power retain
their gates.
