# Atomic loading for the reactive core

The indexed E64 core now has a structural loader described and proved in Lean.
It preserves the committed program during upload, validates each word, and
switches instructions and metadata together on commit. One generated circuit
runs UART, SPI, I²C write, and repeated-START I²C read after host uploads.

This is a reference implementation of the synchronous loading contract. It uses
two register-backed images and one scheduler. It is **too large for the nominal
competition allocation in the current mapping**: see the [technology record](../physical/technology-mapping.md).
Keep its semantics and proofs as the reference for a cheaper implementation.

## Host contract

All commands and data are sampled on the rising clock edge. Inputs must be
stable for that edge. The ports are `init`, `reset`, three-bit `command`,
64-bit `data`, and the two observed protocol inputs. `init` is a synchronous
power-on initialization request; runtime `reset` has different retention behavior.

| Command | Value | Accepted behavior while idle |
|---|---:|---|
| Nop | 0 | Hold loader state |
| Begin | 1 | Discard staging progress and open a new upload at cursor zero |
| Push | 2 | Validate and store the next word in the inactive image |
| Commit | 3 | Require an open, complete upload; select it and reset execution |
| Abort | 4 | Discard staging progress; retain the committed image and execution state |
| Start | 5 | Execute the committed image; reject if no image has been committed |
| Reserved | 6, 7 | Reject |

The priority is **init → reset → busy → command**. Busy rejects every nonzero
command, including start and commit, and allows the scheduler to keep running.
Nop while busy raises no rejection. On the final execution edge the pre-edge
busy state still blocks commands; the host retries on a later idle edge.
`loader_push`, `loader_commit`, `loader_start`, and `loader_rejected` describe
the current pre-edge handshake, not latched acknowledgments. State outputs
include active-bank selection, committed validity, pending upload, and cursor.
A host must advance its stream only on an accepted push.

Start during staging runs the old committed program. Staging progress freezes
while it runs and can resume afterward. Uploading occurs only while idle; this
baseline does not overlap execution with background memory writes.

A successful commit switches the whole image, including idle pins and last
address, clears counters and captured results, and leaves the engine ready.
The new idle pins take effect on that edge. Start requires a separate command.
Abort and begin do not clear results or change pin registers. Runtime reset
clears execution/results and staging progress, retains the committed image, and
applies its idle profile. Init forgets committed validity and releases the pins.
Neither reset clears either memory bank. Before the first commit the engine
remains reset with released pins, regardless of attempted starts.

## Ordered image stream

Every upload has exactly **322 accepted 64-bit words**, in this order:

| Cursor before push | Meaning | Validation |
|---|---|---|
| 0–63 | E64 dictionary records | Canonical valid E64, including unused entries |
| 64–319 | 256 six-bit dictionary references | Upper 58 data bits zero |
| 320 | Idle levels in bits 0–2, drive enables in 3–5 | Upper 58 data bits zero |
| 321 | Last executable address | Upper 56 data bits zero |
| 322 | Complete, awaiting commit | Further pushes rejected |

Pad unused dictionary records with canonical halt (`4`). Address-map entries
are always in range because they are validated as six-bit unsigned values.
The cursor increments only after validation, with no wrap past 322. Invalid
words leave both memory and progress unchanged, so the host can retry. Commit
before completion fails. Abort, reset, or begin invalidates prior progress;
old physical contents in the inactive bank do not make the new upload complete.

This stream occupies 2,576 host bytes if each word is serialized as eight bytes.
It is an internal word interface, **not a new PWL format or an implemented byte
transport**. Host software must first decode/lower PWL or typed programs to the
indexed E64 image. The existing 64-distinct-record limit remains in force.
Record validation establishes instruction legality; a legal program can still
fault by branching beyond its declared last address, as the engine contract defines.

## Proof boundary

All **41 public loader theorems** pass the standard-axiom audit. No `sorry`,
custom axiom, `native_decide`, or `bv_decide` is used. The main claims are:

- Structural controller gates and register updates equal the command equations.
- Indexed store writes and reads equal the functional store operations.
- `Machine.next_correct` and `Machine.run_correct` connect every controller,
  scheduler, and memory register to the functional atomic-loader machine, for
  arbitrary command/input histories and initial two-valued states.
- Upload writes preserve the active image. Without commit or initialization,
  both its identity and committed-valid flag are retained.
- Successful commit selects precisely the previous staging image, writes
  neither memory, and resets execution using the newly selected metadata.
- Initialization establishes safe control and a validity invariant. Validity
  survives arbitrary command histories: the cursor is bounded, each accepted
  dictionary prefix is valid, and every committed dictionary record is valid.

The integrated model uses the previously proved reactive scheduler equations;
[the reactive-core proofs](../engine/reactive-core-hardware.md) connect execution of
represented typed programs to the instruction-level engine and existing compiler
proofs. The new loader proofs concern command handling, register correspondence,
and image validity/selection. They do not prove that arbitrary uploaded bytes
implement a particular protocol or that an external transport delivered the
host's intended bytes.

Lean's semantics use two-valued registers. RTL tests separately exercise startup
with uninitialized storage, using an explicit init edge and ordinary uploads.
The named-wire emitter, CIRCT, simulation, and synthesis remain outside the
Lean proof boundary. Physical I/O synchronization and transport are not modeled.

## Executable evidence and cost

`python3 scripts/check-loader.py` passes:

- **20,340 independent oracle edges**, matched by Lean structural components
  and generated SystemVerilog; **12,462,616 physical memory observations**.
- Thirty interrupted-upload cases: abort/reset/restart at ten cursor boundaries,
  including dictionary, address-map, and both metadata boundaries. Each retains
  and reruns the old UART program. A staged SPI image also resumes after UART
  execution, then commits successfully.
- **68 malformed records** and **516 over-wide map/metadata values** rejected
  without advancing the cursor; complete-upload overflow and repeated commit
  rejection; initialization, reset, busy commands, and status-clearing cases.
- UART, full-duplex SPI, a stretched I²C write, and **23 I²C reads** under quiet,
  stretched, and NACK conditions. Successful reads retain **502/557 cycles**.
- Five faulty RTL variants rejected: ignored init, reset, or start; corrupted
  upload data; and commit enabled one word too early.

The testbench observes both banks directly but never writes or initializes them
through hierarchy. Once a slot has been written through the interface, every
subsequent edge checks its retained value, including both metadata fields.

| Storage | Bits |
|---|---:|
| Each dictionary | 4,096 |
| Each address map | 1,536 |
| Each idle/last profile | 14 |
| Two complete images | 11,292 |
| Scheduler | 49 |
| Loader control | 12 |
| **Total** | **11,353** |

Generic synthesis retains all storage and reports **41,728 cells**, including
**30,375 combinational cells**, with an **89-cell** longest combinational path.
The earlier single-image indexed core has 5,695 register bits, 29,732 total
cells, and an 86-cell path. These are generic counts; actual mapped area is
reported separately in [technology mapping](../physical/technology-mapping.md).

The host interface has 72 input bits including clock and observed protocol
inputs. The emitted module also exposes diagnostic outputs. This interface is
for integration/testing and is not a proposed Tiny Tapeout pin allocation.

The success receipt, source/artifact hashes, emitted MLIR/RTL, traces, mutations,
and netlists live under ignored `build/loader/`. Reproduce using the pinned
[development tools](../development.md#atomic-loader-and-early-technology-mapping).

Next: use this proved contract to compare smaller storage implementations.
Preserve the committed image during upload unless an explicit contract revision
is chosen. Synchronous memory requires an explicit read/prefetch schedule and a
renewed timing correspondence proof; it cannot silently add execution cycles.
