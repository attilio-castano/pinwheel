# Buffered storage and fetch comparison

Decision, 2026-10-07: compare storage implementations below the shared
programming interface. The experimental target
`pinwheel-buffered-shared-branches32-v1` stores complete branch descriptors in
a 16-entry dictionary. The [inline reactive target](buffered-reactive-hardware.md)
remains available for programs needing more distinct descriptors. Both execute
SPI, JTAG and I²C through the same protocol-independent operations and owned
TX/RX/result contract.

This tests the programmability goal by changing the implementation of program
storage while retaining the source language and waveform edges. Target resource
bounds remain explicit; a smaller representation is useful only if its capacity,
loading cost and fetch path fit the intended programs.

## Representation and admission

The source remains `BufferedProgram`, with 64 leaves, 256 syntax nodes, two
nested loops and 1,024 virtual positions. Instruction durations, WAIT budgets,
scratch capture, successful demands, maximum RX reservation and endpoint
coordinates retain their [reactive meanings](buffered-reactive-hardware.md).

Each row stores instruction64, loop control24 and branch index4: 92 bits.
The separate dictionary stores sixteen complete 56-bit descriptors, preserving
reserved bits and both endpoint environments. A balanced row lookup occurs
first; one dictionary lookup expands its reference afterward. The expanded
144-bit row feeds the existing execution equations. Cached branches remain
54 bits, so CHECKED terminal capture and branch selection still happen on
the original edge. No protocol selector or added waveform clock is introduced.

The host deduplicates descriptors in first-use order and pads the dictionary
with zeros. All sixteen entries are uploaded. Imported images reconstruct the
complete original source lowering, including exact row indices, dictionary
ordering, padding, source identity and demands, before transport I/O.
There is no forced zero entry: a program can use sixteen distinct nonzero
descriptors. Counted NEXT counts as a distinct descriptor when present.

Programs requiring more than sixteen descriptors fail admission. A tested
counterexample has 64 CHECKED leaves inside two repeats, 1,024 virtual
positions and 64 distinct descriptors: it fits the inline target and fails
this target. This is a separately versioned capacity choice, not full preservation
of the inline target's source set.

| Representation | Allocated program bits | Added dictionary coverage | Total declared state |
| --- | ---: | ---: | ---: |
| Inline: 64 × 144 | 9,216 | 0 | 9,599 |
| Shared descriptors: 64 × 92 + 16 × 56 | 6,784 | 16 | 7,183 |
| Full 64-descriptor dictionary: 64 × 94 + 64 × 56 | 9,600 | 64 | 10,047 |

The third row is a geometry calculation, not an implemented circuit. It shows
why a dictionary sized for every possible inline program does not guarantee
savings. An alternative 32-entry endpoint dictionary with 64 × 104 rows needs
7,424 program bits before coverage; it has a different endpoint-capacity limit
and is not implemented here.

| Uploaded program | Rows | Distinct descriptors | Inline bits | Shared bits |
| --- | ---: | ---: | ---: | ---: |
| Four-byte mode0 SPI | 4 | 1 | 576 | 1,264 |
| 17-bit JTAG DR scan | 20 | 1 | 2,880 | 2,736 |
| Four-byte I²C register read | 50 | 2 | 7,200 | 5,496 |

Fixed dictionary upload increases small SPI loading traffic while reducing
allocated state. Uploaded size, retained storage and complete mapped area are
separate measurements.

## Loading and owned results

The parallel command fields and 26 public observations keep their widths.
Command1 writes a row, using the low four bits of `branch` as its reference;
upper reference bits must be zero. Command6 writes a complete descriptor using
address0 through15; upper address bits must be zero. COMMIT requires coverage
of every declared row and every dictionary entry. It retains the prior count,
span, generation, identity and profile checks.

The first accepted write of either kind begins one pending generation and
clears both coverage masks. Neither table-first nor row-first upload can reuse
old coverage. Any accepted write invalidates the old image; active and retained
transfers reject both write commands. The raw interface still permits malformed
descriptors to be stored; inherited entry normalization rejects them before
entry effects. COMMIT does not certify a source tree.

```python
from buffered_shared_branches import BufferedSharedBranchesHost
from buffered_reactive_hardware import compact_i2c_read
from buffered_i2c import register_read_tx

host = BufferedSharedBranchesHost(transport)
host.initialize()
loaded = host.load(compact_i2c_read(4, phase_cycles=4, wait_cycles=32))
pending = loaded.submit(tx=register_read_tx(0x53, 0xa6))
pending.wait(timeout_cycles=200_000)
result = pending.read()
pending.release()
```

The inherited lifecycle copies TX, reserves maximum RX and retains completion
until matching release. Host wait timeout preserves the pending owner; NACK,
hardware timeout and failed STOP retain diagnostic RX prefixes and scratch.
The same host loads compact SPI/JTAG sources. Dictionary upload occurs once
per image, not once per transaction.

## Proof and fetch deadline

`SharedBranchProofs.lean` contains eighteen named kernel proofs. Expression
rewriting agrees with ordinary `Expr.bind` for every expression, input and
represented state. The factored row-then-dictionary lookup preserves evaluation.
Expanded-state runtime steps and all public observations equal the inline core
on commands other than row WRITE1, COMMIT2 and dictionary WRITE6. Runtime
includes reset, START, held phases, release and retained reads; arbitrary initial
represented state is allowed. Dictionary and row storage hold during runtime.
Dense snapshot indexing, 116 register declarations and 7,183 state bits are
also kernel-checked.

All-input observation equality uses the explicitly mapped command/interface.
The proofs do not establish a whole-upload trace relation. Upload coverage and
admission have executable/RTL witnesses. Named closed expressions build the
adapter's execution expressions once. The logical rewrite retains these kernel
proofs; its executable replacement memoizes source expression objects and their
expanded results. It retains source objects for pointer-key validity and checks
cached widths. Forty small graphs compare both the public adapter and the
explicit implementation against independent `Expr.bind`: 25,600 evaluations,
including every constructor, sixteen references, sampled inputs and malformed
upload shapes. Four small module comparisons are byte-identical across logical
and executable adapters and safe and memoized emitters. These checks and the
full interpreter/native exporter parity are finite implementation evidence,
not a universal native rewrite, compiler or emitter proof.

The gate first compares three interpreted/native command cases byte-for-byte,
then exports independent complete cases under one supervisor with at most four
workers. Every shard passes the unchanged public-state/expectation checker;
its MLIR and register metadata must equal the passed native parity artifacts.
The merge preserves exact input transcripts and original case order, and passes
the same checker again before publication. Timeout, failure and cancellation
reap the workers and retain their records. This changes export orchestration;
the typed circuit and `Expr.eval` remain unchanged.

`FetchDeadline.lean` adds eight named laws. A single fixed registered response
cannot directly supply two distinct successor rows when a terminal decision
arrives. Reading both candidates beforehand permits selection under an
immutable bank. This is a local deadline statement, not a universal two-port
lower bound or a complete buffered SRAM refinement.

The actual circuit also exposes a possible single-port strategy: decisions use
stage2, whose next value is the preceding stage1 value. Kernel laws establish
that dispatch and endpoint selection use registers, and successor addressing
uses registers when START is excluded. Twenty-four actual-step fixtures explore
CHECKED, WAIT and QUALIFY across prior sampler values and changing current/next
raw inputs; predicted rows match required dispatches. Additional fixtures cover
both one-cycle terminal choices, last-budget WAIT readiness and nested-loop
rollover/exit addresses.

Predicting from stage1 would use the first synchronizer stage for memory address
logic. Its logical predictability does not qualify that electrical path or its
metastability containment. A complete single-port design must account for that
boundary, address timing, start-word availability and candidate renewal after
every branch/loop entry. Two-candidate prefetch is the comparison that avoids
depending on the unsynchronized-stage prediction. An isolated SRAM bit count
does not settle either design.

## Measured acceptance

Full hardware run `shared-branches-03` passes in 1,756.039 s. It compares the
same pinned tools and CMOS5L library with accepted inline run
`buffered-reactive-hardware-02`. The saved mapped designs retain every declared
state bit; neither has pruned or derived state coordinates.

| Complete target measurement | Inline baseline | Shared descriptors |
| --- | ---: | ---: |
| Declared and retained state bits | 9,599 | 7,183 |
| Generic mapped cells | 57,639 | 43,065 |
| Typical CMOS5L mapped cells | 51,602 | 37,428 |
| Typical summed cell area, µm² | 876,881.3004 | 644,939.6310 |
| Typical sequential cell area, µm² | 470,243.4912 | 351,886.5504 |
| Generic maximum next-state logic levels | 90 | 91 |
| Typical maximum next-state logic levels | 40 | 43 |
| Generic maximum data-signal sink pins | 3,781 | 2,547 |
| Typical maximum data-signal sink pins | 10 | 10 |

State falls by 25.17% and typical summed cell area by 26.45%. Typical maximum
logic depth increases by three levels. These levels and sink-pin counts come
from the saved cell graph; they include no wire delay or electrical timing.
The area comparison includes the complete parallel target and its upload,
coverage, execution and owned data state. It excludes pads, serial transport,
SRAM, clock tree, placement and routing. The smaller mapped area does not
establish chip fit or a faster fetch path.

The interpreted/native parity fixture matches three cases and 123 edges,
including byte-identical vectors, MLIR and register metadata. The full native
export uses four workers for 227 cases and 11,120 edges in 816.039 s. Its
independent checker evaluates 9,558 specified states across 64 raw-input
histories. Emitted RTL matches all 26 public fields on those command edges
and passes 2,311 wire cases: 1,027 SPI, 242 JTAG and 1,042 I²C. It compares
1,509,697 source observations, 1,366,449 fetch/environment states and 1,515,348
independently derived sampler states. Three NACK stages and five timeout
fixtures preserve the inherited STOP and diagnostic-prefix behavior. Retained
results read identically twice, and host wait timeout preserves ownership.

Saved generic and typical mappings each pass arbitrary represented-state SAT
comparison of public outputs and every next-state bit, all 227 command cases
and 58 wire cases. Each mapped wire replay independently checks 47,381 sampler
states. The branch-index circuit mutation and each mapped-output negative
control reject. Normal and optimized Python each pass 1,036 of 1,038 tests;
two Linux-specific tests skip on this host.

Full portable foundation `shared-branches-foundation-02` passes in 1,535.931 s:
279 modules, 51 executable suites and one kernel suite. Its standard-axiom audit
checks 24,711 declarations and 13,276 theorem constants, and rejects the injected
custom axiom. This includes the logical adapter/fetch proofs and finite
executable adapter comparisons described above.

The [tracked acceptance manifest](../../physical/experiments/buffered-shared-branches-results.json)
binds both reports, 693 frozen inputs, 152 accepted generated artifacts and
422 predecessor hardware/physical file hashes. Closeout checks all current
bytes against those pins and the predecessor Git snapshot. Report SHA-256:

- Hardware: `bfcea3f349526299f9471387101d55d567c6f08b3ea86da64032fd0cfb35caf2`
- Foundation: `eaf37579f00d341fdf640259ea78afe0cec5775cf3784c3643e538fb436012e6`

Two failed development exports remain separately pinned: recursive graph
copying was interrupted after 1,268.05 s with a sampled 30.3 GB footprint;
after memoized adaptation, sequential native evaluation timed out at
1,800.004 s with a sampled 54.0 MB footprint. The accepted run uses the same
typed evaluator under supervised complete-case export. The manifest also
preserves the bounded development probes and earlier foundation snapshot;
they are not substitutes for the final acceptance runs.

## Reproduce and continue

The inspected [SRAM geometries](../storage-primitives.md) include 64×64,
512×8 and 512×64 single-port macros. The 64×64 macro measures
784.48 × 64.36 µm, or 50,489.1328 µm². Two conservative allocations use it:

| Latency-one allocation | 64×64 macros | Macro footprint, µm² | Remaining declared FF bits |
| --- | ---: | ---: | ---: |
| Instruction64 in SRAM; control/reference and dictionary in FFs | 2 | 100,978.2656 | 3,087 |
| Complete92-bit rows in SRAM; dictionary in FFs | 4 | 201,956.5312 | 1,295 |

These are allocation calculations, before START storage, response alignment,
macro output registers, clocking, halos and routing. Each read candidate needs
its own single-port replica; full rows need two 64-bit stripes per replica,
with 36 padded bits in the high stripe. The hybrid retains 1,792 row metadata
bits and aligns the two responses with either 56 metadata bits or 12 request
address bits. Keeping the 896-bit dictionary combinational avoids a second
dependent synchronous lookup. Both require broadcast writes and mutually
exclusive reads/writes. A second complete image bank would change ownership
and double these macro counts.

Immediate COMMIT→START needs a row0 mirror updated on accepted row writes,
or a COMMIT-read bypass with a saved START, as in the existing
[SRAM schedule](../../Pinwheel/Hardware/Storage/SramSchedule.lean).
Existing execution caches already retain operation fields. The controller must
mask arbitrary initial contents and stale responses, align metadata with the
selected response, and replace parallel tail clearing with a count-gated
compact-row projection. That projection precedes dictionary expansion:
dictionary entry0 can be nonzero. The pinned physical trust experiment uses
512×64 and remains unqualified; its evidence does not qualify a 64×64 backend.

```sh
python3 -B scripts/check-foundation.py --tag <fresh-foundation-tag>
python3 -B scripts/check-buffered-shared-branches.py --tag <fresh-hardware-tag>
```

The comparison uses the pinned Lean/CIRCT/OSS CAD/CMOS5L tools and the retained
accepted inline run `build/buffered-reactive-hardware/buffered-reactive-hardware-02/`.
The gate verifies that report against its tracked manifest, checks the used
saved artifacts and matches tool/library hashes. Retain both accepted run
directories beside the tracked manifests; generated artifacts remain under
ignored `build/`. Fresh tags preserve earlier receipts. `--smoke` uses the
development wire subset and does not count as full acceptance.

Next, build one explicit latency-one row-fetch organization, including physical
memory width, striped/replicated storage, cached start row, branch metadata,
upload coverage and owned data. Prove its availability invariant across START,
one-cycle CHECKED, unpredictable WAIT release and nested-loop exits, then
compare the complete target. Serial transport and retained-result commands
follow that memory decision. SRAM/component qualification, routed timing,
package power and full initialized compiler/package refinement retain their
separate gates.
