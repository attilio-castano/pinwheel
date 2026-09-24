# Upload, execute, and retrieve a result

The host workflow exercises one unchanged chip through its package pins. Programs
are data: UART TX/RX, SPI, I²C and a conditional trigger use the same RTL. The
[whole-chip contract](whole-chip.md#host-result-interface-version-1) owns pin
assignments, synchronization and mailbox semantics; this page owns the client,
demonstration and its limits.

## Reproduce the demonstration

Install the pinned Lean/CIRCT/Icarus tools described in [development](development.md).
For the hybrid, first install the hash-checked models with
`python3 scripts/inspect-storage-macros.py`. Use fresh tags:

```sh
python3 scripts/pinwheel-host.py demo --backend hybrid --tag demo-hybrid
python3 scripts/pinwheel-host.py demo --backend reference --tag demo-reference
```

Each command builds its dependencies, compiles the examples, emits one chip and
keeps one Icarus process alive through all uploads. It exports reusable program
JSON, command logs and a receipt in `build/host/<tag>/`. The receipt binds source,
tool, compiler-image, MLIR, RTL and macro-model identities. The reference is the
unrestricted two-port flip-flop chip; the one-port chip cannot run this RX program.

| Workload | Independent external observation |
| --- | --- |
| UART TX | Byte `0x53`, 8N1, four chip edges per bit; all 40 driven edges checked |
| SPI mode 0 | Transmit `0xa6`, receive `0x96`, four edges per half clock; eight rising edges checked |
| I²C register read | Address `0x53`, register `0xa6`, receive `0x96`; repeated START, ACKs, open-drain release and 0–3-edge clock stretches |
| UART RX | Byte `0xa6` with a good stop, then `0x53` with a bad stop, 16 edges per bit |
| Custom trigger | Wait on input 0; capture input 1 and branch immediately; emit an eight-edge pulse only when the captured bit is high |
| Recovery | A malformed upload aborts staging; the previous committed trigger program still executes |

The trigger runs with high, low and absent input, covering both branches and
timeout. Each successful run reads its retained result twice, then consumes it.
The peers inspect only pin values and edge counts. `host_bridge.sv` never reads
internal DUT state, and the host client does not import the engine oracle.
Acceptance checks remain active with `python -O`, `python -OO`, or
`PYTHONOPTIMIZE`. Mailbox observations execute before their values are checked;
any failed check prevents the CLI from publishing its success receipt.

Capture slots are the machine's raw 16-bit result. SPI/I²C place the first received
bit in slot 0, so wire byte `0x96` appears as `0x69`. UART RX uses the low byte for
data and slot 9 for the stop observation: a bad stop is captured data, while the
engine outcome can still be `complete`. Protocol interpretation belongs above
the raw mailbox.

## Client and program format

`scripts/pinwheel_host.py` exposes `Program`, `Host`, `Result` and a small
`Transport.advance(ui, cycles, rst_n=...)` interface. `pinwheel_sim.py` supplies
the interactive RTL transport. A future board transport must establish the same
clock, sampling, voltage and drive/release assumptions separately.

`Program` holds 1–256 unsigned E64 records, the last executable address and three
idle levels/enables. It deduplicates the full padded image, rejects more than 32
distinct records before I/O, and produces the existing 322-word upload. Canonical
record validation remains in the chip: a rejected push aborts staging before
commit. Uploading does not consume an older result. Starting with an unread
result is refused, and readback preserves overflow/rejection flags.

Exported JSON has exactly `format: "pinwheel-e64-v1"`, `words`, `last`,
`idle_levels`, and `idle_enabled`. This is a host-side E64 interchange format,
separate from the [PWL binary format](binary-images.md). For example:

```sh
python3 scripts/pinwheel-host.py run --backend hybrid --tag custom-trigger \
  --program build/host/demo-hybrid/trigger-captured-high.json --incoming 3
```

`run` supplies constant external inputs. Dynamic protocol peers are part of
`demo`; a constant input is not an SPI or I²C target. Host polling has an explicit
edge budget (plus at most three edges to observe the last status page); a timeout
does not reset the engine or consume a result.

## What this says about the next data path

One full upload costs 94,629 chip edges at the demonstrated minimum serial phase,
including client status operations: 1.89258 ms at the **assumed** 20 ns period.
The TX example executes for 40 edges, or 0.8 µs on that same assumption. These
are modeled edge counts, not measured board throughput or signed-off rates.

The next useful workload is repeated transfers with changing payloads and a
resident program. Compare a small data register/shift operation and explicit
rearm against reuploading code. Specify ownership, starvation and result delivery
before adding a FIFO. Continuous UART receive remains a separately proved model;
this demonstration does not compose its supervisor into the chip. Defer an ISA
change until the physical experiment establishes the remaining area/routing
budget, and retain this workload as its acceptance test.

### Bounded resident-payload proposal (2026-09-19)

Use one resident UART 8N1 transmitter to send `00`, `ff`, `a6`, and `53`, then
all 256 byte values, with four chip edges per bit and the same program image
throughout. This is a specification for a future data path, not implemented
behavior of the current emitter.

The [compact execution study](compact-execution-study.md) now tests this payload
ownership and all 256 UART values in an isolated execution model. It does not
implement this extension in the current E64 emitter or close the budget gate below.

The smallest candidate uses the data word already carried by `START`: capture
`data[7:0]` into an eight-bit shift register on an **accepted start**, and add
an instruction operation that drives a selected output from its low bit and
shifts once on instruction entry. Holding that instruction for four edges must
not shift four times. Start/stop bits and their timing continue to use the
ordinary program instructions. Eight unrolled data-bit operations avoid a new
hardware loop counter. The instruction encoding and dense-record cost remain
to be designed and measured; eight data bits alone are not the total area cost.

This candidate needs no additional serial command, payload queue, or separate
payload-valid register: each complete START frame already contains its data.
Existing programs continue to ignore the data word. A future host API can expose
`start(payload=...)`; its current zero payload remains the default. The transport
and record-format compatibility checks are still required before implementation.

| Ownership event | Proposed behavior |
| --- | --- |
| Accepted START | Snapshot the payload once and begin the resident program |
| No complete START frame | Stay idle; starvation cannot stretch an in-progress UART bit |
| START while busy | Follow the existing loader acceptance gate; do not replace execution-owned data |
| Instruction entry | Drive the old low bit and shift right once, filling with zero |
| Instruction hold | Preserve both shift-register contents and the driven bit |
| Completion | Retain the existing result; the host reads/consumes it before starting again |
| Init/reset | Stop execution; the next accepted START supplies fresh data |
| Partial/aborted upload | Preserve the committed program; do not treat upload data as execution payload |

Unread-result backpressure is currently enforced by the host client. The
observer does not inhibit core execution: raw starts that violate host ownership
retain the existing mailbox overrun behavior. The proposal must not silently
turn that host rule into a claim about hardware gating.

At the demonstration's minimum serial phase, a 72-bit command frame takes
`72 × 4 + 4 = 292` chip edges. Reupload-plus-start requires 325 frames, or
94,900 framing edges; this candidate requires one START frame, or 292 framing
edges, after the initial upload. Both figures exclude status/result operations
and the 40 execution edges. They are transport-model budgets, not board rates.

Acceptance requires an independent pin observer to verify every UART bit for
all 256 payloads on one unchanged program, exactly 40 execution edges per byte,
and no shifts on held edges. Also test a changing serial data input after start,
a busy start, truncated frames, reset during each bit, malformed-upload recovery,
and unread-result overrun. The proof must connect the accepted-start snapshot and
one-shift-per-entry rule to the compiler's UART trace. Implement only after the
selected physical organization has a measured area and routing budget.
