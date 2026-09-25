# SRAM and latch feasibility

This records primitive feasibility, scheduling and complete experimental SRAM
chips for the [storage study](storage/storage-study.md). The emitted flip-flop
implementations remain the proved references. The hybrid now has a closed-loop
array/controller refinement in Lean, plus independent RTL/mapped-cell checks
and pre-layout timing. Full chip translation/binding and physical closure remain
open; the direct prototype does not inherit the hybrid proof.

## Pinned SRAM evidence

The CMOS5L PDK at `607e18d4bd9214a52575c194b4181ef449f9252f` contains
[`libs.ref/sg13cmos5l_sram`](https://github.com/IHP-GmbH/ihp-sg13cmos5l/blob/607e18d4bd9214a52575c194b4181ef449f9252f/libs.ref/sg13cmos5l_sram),
a symbolic link to the sibling SG13G2 SRAM library. Thus the public PDK provides
a concrete SRAM reuse path; a directory name alone was insufficient evidence.
The inspected target library is fixed at IHP Open PDK revision
[`5e6d592e4002946a4616f798c357f0f3c06cf3b6`](https://github.com/IHP-GmbH/IHP-Open-PDK/tree/5e6d592e4002946a4616f798c357f0f3c06cf3b6/ihp-sg13g2/libs.ref/sg13g2_sram).
The two repositories must be installed with their expected sibling relationship;
this study downloaded selected views, not a complete PDK installation.

| Single-port macro | LEF dimensions, µm | Footprint, µm² | Potential allocation |
|---|---:|---:|---|
| `RM_IHPSG13_1P_64x64_c2_bm_bist` | 784.48 × 64.36 | 50,489.1328 | Both 32-entry dictionaries; bank selects one half |
| `RM_IHPSG13_1P_512x8_c3_bm_bist` | 236.80 × 110.38 | 26,137.9840 | Both 256-entry address maps |
| `RM_IHPSG13_1P_512x64_c2_bm_bist` | 784.48 × 191.34 | 150,102.4032 | Both direct 256-record images |

The indexed allocation has **76,627.1168 µm²** of macro footprint and reserves
8,192 physical bits for 6,080 logical dictionary/map bits. Metadata, controller,
cache, decoder, clocking, routing, halos, power distribution, and loading logic
are additional. The direct alternative uses more memory footprint but removes
the index-to-dictionary dependency. These are geometric allocations, not measured
whole-machine area savings. The 784.48 µm width also makes aspect ratio and
floorplanning material; a small area sum does not ensure a legal placement.

The [behavioral model](https://github.com/IHP-GmbH/IHP-Open-PDK/blob/5e6d592e4002946a4616f798c357f0f3c06cf3b6/ihp-sg13g2/libs.ref/sg13g2_sram/verilog/RM_IHPSG13_1P_core_behavioral_bm_bist.v)
updates its output register on a positive clock edge when reading is enabled.
It supports masked writes and shows the newly masked data when reading and writing
the same addressed word together. This is a different read contract from the
current combinational stores. Integration must also bind the enable, bit-mask,
and BIST controls and use the corresponding timing/physical views.

The atomic loader currently rejects uploads while execution is busy, which avoids
execution/upload port contention. It does not eliminate the execution read-latency
problem. An indexed SRAM lookup introduces a dependency between an address-map
read and a dictionary read.

## The scheduling gate

The present machine can capture an input, use that capture to choose a branch,
and enter its successor on the same protocol edge. A synchronous SRAM cannot
supply an unanticipated record to a register that is sampling on that same edge.
A one-word cache fixes the current-word read but does not solve successor supply.

A future SRAM experiment needs an explicit schedule and proof obligations:

1. Define request/response latency, reset, retained outputs, disabled reads, and
   simultaneous read/write behavior for the selected macro.
2. Hold the current record and prefetch both possible branch successors before
   terminal capture. The branch decision must select records already available.
3. Account for the dependent map/dictionary accesses and the worst case of
   consecutive one-cycle instructions and branches. Average I²C wait time cannot
   justify the general engine's schedule.
4. Either establish sufficient ports/buffering under the existing clock contract,
   or introduce a faster internal schedule with a proved correspondence to the
   same external pin/capture edges. Extra visible wait cycles require a changed
   contract and are outside this study.
5. Prove reset/commit invalidate pending reads, prevent responses from the old
   image entering the new one, and retain atomic replacement. Then test a macro
   simulation model and measure the complete wrapper and physical implementation.

No SRAM replacement is adopted here. The verified scheduling contract must come
before memory inference or macro mapping. The
[memory abstraction](memory-abstraction.md) (2026-09-17) now states that
contract and proves obligations 1, 2, 4 and 5 at the functional level: a
prefetch machine that reads both candidate successors from next-state values on
two read ports refines the atomic reference edge for edge. Obligation 3 becomes a
structural constraint: the composite read is latency one only if the address
map or the dictionary stays combinational.

## Bounded SRAM scheduling study (2026-09-19)

The early decision is **keep two logical successor reads available while we
finish the shared chip interface**. SRAM can preserve the execution contract;
it does not inherently require the one-port program restriction. Do not commit
to a new UART polling schedule on the basis of the existing one-port area result
alone. The existing two-port flip-flop netlist is the unrestricted reference;
neither SRAM option below is promoted to a proved backend. The later
[complete-chip comparison](#complete-chip-comparison-2026-09-19) supersedes this
early study's pending mapping and source-compatibility questions.

### Organizations and complete upload schedule

* **Dictionary SRAM, combinational maps.** Each `64x64` macro contains both
  32-entry dictionaries, addressed by `{bank, dictionary_index}`. Retain both
  256x5 maps in flip-flops. Two independent successor reads need two identical
  dictionary macros with broadcast writes. Dictionary pushes 0–31 write the
  inactive half of both copies; pushes 32–63 are validated padding; pushes
  64–319 update the inactive map; pushes 320–321 update its idle/last metadata.
  The map read remains combinational before the SRAM edge. This preserves the
  two-port policy's one-edge composite latency, but retains the large map read
  trees. One macro instead requires the existing one-port scheduling rule.
* **Direct SRAM, expansion during upload.** Each `512x64` macro contains both
  256-record images. One staging dictionary, shared across replacements, holds
  the first 32 records; the existing capacity rule validates the remaining
  dictionary slots and rejects indices above 31. On each index push, read this
  scratch dictionary combinationally and write the expanded record into the
  inactive bank. Broadcast that write to two macros for two successor reads.
  Metadata remains in two small register banks. All 322 accepted pushes retain
  their current edges: expansion occurs during each index push, with no hidden
  copy pass before commit. Restarting the active image during an incomplete
  upload uses its expanded SRAM contents, independently of staging scratch.
  The harness uses 32x64 scratch; the area scenarios also include 32x55 scratch
  using the existing dense codec. Supporting 64 unique records needs larger
  scratch and a separate area estimate.
* **Index and dictionary both synchronous.** The small raw allocation of
  76,627 µm² is not a one-edge composite store. The dictionary address appears
  only after the index read edge; its response arrives one edge later. Neither
  the current one-port rule nor two copies of the pair remove that dependency.
  A different schedule/admission rule, more speculative reads, or a separately
  timed faster internal clock would be required. This option is deferred.

Execution and accepted uploads are mutually exclusive in the atomic loader.
For either viable organization, `begin` only starts staging; `abort` and reset
discard its validity/cursor, not memory contents; a later complete upload writes
every reachable slot before commit. Commit selects the finished bank and resets
execution. No simultaneous read/write is needed: during a write, `REN=0`; during
an execution/commit read, `WEN=0`. `MEN` qualifies either access, write masks are
all ones, `A_DLY=1`, and BIST controls are tied off. This avoids relying on the
macro's write-through collision behavior to implement a read-first contract.
Global reset invalidates the active program; engine reset retains its image.

### Edge schedule and buffering

On commit edge C, port 0 reads word 0 of the new bank. Its registered output is
available **after** C. An additional start-word register cannot capture that new
output on C: an immediate start at C+1 needs a bypass from macro Q, then a
one-bit pending flag permits the retained start register to capture it on C+1.
Later starts use that retained word. The harness exercises this bypass and
retention; simply substituting a macro for `reads` and leaving the existing
start register untouched would add an incorrect edge.

On entry edge E, the already available successor supplies the record being
entered. Its two successor addresses are decoded before E and presented to the
two SRAM copies. Their outputs after E supply either branch on E+1, including a
zero-duration checked instruction that captures its branch bit on E+1. On that
edge the selected word also determines both addresses for E+2. Consecutive
branches therefore require no average-duration assumption. Holds repeat the
current candidates; disabled reads retain Q. Reset/commit must invalidate all
pending response ownership before the next dispatch.

Two macro output registers can serve as the fetched-candidate registers. The
current word and retained start word still need registers. A one-port variant
also needs a retained untaken response while Q is replaced by the taken one;
its admission rule is still required. These registers, the start bypass,
loader/metadata, serial sampler/receiver and host result state are included in
the logic allowance below, not claimed as free macro storage.

### Area scenarios and evidence

| Organization | SRAM footprint, µm² | Whole-chip area scenarios, µm² | Remaining read path |
| --- | ---: | ---: | --- |
| Hybrid, one port | 50,489 | 348,644–402,677 | Flip-flop map, SRAM dictionary |
| Hybrid, two ports | 100,978 | 445,327–503,560 | Two map reads, SRAM dictionaries |
| Direct, one port | 150,102 | 364,551–440,251 | SRAM plus response retention |
| Direct, two ports | 300,205 | 509,854–585,117 | Two direct SRAM reads |

These are **gate-budget scenarios, not measured bounds or routed area**.
`check-sram-feasibility.py` records the formulas: enabled storage bits cost a
48.9888 µm² FF plus an 18.144 µm² mux; scratch/map read trees and write decoding
are counted separately. The current result chips have 468/469 non-storage
register bits. Replacing two fetched words with macro Q and adding a start-bypass
flag leaves 341 bits for two ports; retaining one candidate leaves 406 bits for
one port. The larger scenario reserves 64 additional control bits. The common
logic allowance adds 400–800 muxes and 1,500–3,000 NAND2 equivalents, plus
10–20% of all standard-cell area for clocking, buffering and repair. It is an
explicit estimate of control complexity, not synthesized evidence. The direct
cases span dense and raw scratch. Both atomic banks and both physical read
copies are counted. Routing whitespace, power integration and macro halos are
additional geometric costs. Two direct macros alone occupy 784.48×382.68 µm
before separation/halos; they cannot be placed side by side in the current die.
The earlier 625,727 µm² routed one-port core is a different boundary and flow
stage, so these estimates do not establish a saving or whole-chip fit.

The public functional macro models pass 1,979 storage edges and 1,000 branch
fetches in four runs of consecutive branches, with immediate commit/start,
retained start data, disabled reads,
restart after partial inactive writes without another commit, and repeated bank
replacement. Collapsing the two
responses to one fails with a lookup mismatch. Run:

```sh
python3 scripts/inspect-storage-macros.py
python3 scripts/check-sram-feasibility.py --tag local-sram-study
```

The local receipt is `build/storage/feasibility/schedule-05/report.json`.
All 13 selected views were rehashed against `tools/storage-macros.json`.
The installed physical PDK's SRAM symlink is dangling: the selected views are
available separately, but the complete local SRAM physical installation is not.
The SRAM-library revision differs from the physical flow's pinned PDK; the later
comparison establishes that the selected files themselves are identical.
No macro-aware timing, placement, power hookup or LVS claim follows from this
functional test. The harness supplies accepted storage
operations and branch requests; it is not a complete loader/engine simulation
or a Lean refinement proof.

**Early decision:** SRAM justifies keeping an unrestricted two-read organization in
the design space. Direct replicated storage is the cleaner execution-path
experiment; hybrid storage has the smaller estimated footprint. Defer the
replacement itself until the complete wrapper is mapped and the physical views
are integrated. Continue generic admission and host readback against the existing
cores; perform independent chip checks before choosing which artifact merits
the official-template physical run. The study does not establish enough evidence
to select one final storage implementation or to rewrite UART timing now.

## Complete-chip comparison (2026-09-19)

**Select hybrid dictionary SRAM with two logical reads for the next adapter
proof and physical experiment.** It is smaller than the complete direct-SRAM
and flip-flop chips, while the functional checks preserve the unrestricted
execution contract and current UART program. This selects an implementation
candidate; it does not promote a default or establish routed fit.

The shared assembly, now in `Storage.SramAssembly` and serialized by
`test/SramChipEmit.lean`, reuses the existing Lean loader, scheduler, sampler,
serial receiver and host mailbox expressions. A single parameter selects direct
storage with dense upload scratch or dictionary SRAM with combinational maps.
Only the storage/fetch interface changes. Typed emission rejects references to
omitted storage registers. SRAM Q passes through the feeder layers without being
sampled a second time; the commit/start bypass and saved start word implement
the schedule above. `test/sram_chip.sv` connects each controller to two instances
of the actual pinned macro model, with independent reads and broadcast writes.
This comparison did not promote the experimental backend or add a refinement
claim. Subsequent proof and ownership work is recorded below and in the
[assembly study](physical/chip-architecture-study.md#checked-assembly-and-edge-obligations).

All three chips include the same serial transport, pin samplers, admission and
result mailbox. The SRAM cases retain both program banks and all buffering,
metadata, scratch/maps and control. The comparison uses the same Yosys/ABC
mapping recipe and pinned CMOS5L cells at each corner.

| Whole result chip, two reads | Typical cells + macros, µm² | Slow cells + macros, µm² | Typical standard cells, µm² | Mapped FFs |
| --- | ---: | ---: | ---: | ---: |
| Flip-flop reference | 622,897 | 622,875 | 622,897 | 6,544 |
| Direct SRAM | 479,596 | 479,611 | 179,391 | 2,095 |
| Hybrid dictionary SRAM | **393,558** | **393,558** | 292,580 | 2,895 |

Hybrid uses 36.8% less mapped area than the matched flip-flop chip and 17.9% less
than direct SRAM. Its two macros contribute 100,978 µm²; the direct pair contributes
300,205 µm². These totals exclude clock-tree insertion, hold/fanout repair,
placement whitespace and halos. Applying the earlier 10–20% **standard-cell**
repair allowance to these measured subtotals gives hybrid scenarios of
422,816–452,074 µm² and direct scenarios of 497,535–515,474 µm². The allowances
remain estimates, not measured repair cost or bounds. Two stacked hybrid macros
occupy 784.48×128.72 µm before halos/separation, compared with 784.48×382.68 µm
for the direct pair. No placement was attempted in this comparison. The later
[whole-chip physical experiment](chip-physical-study.md) measures placement and
repair cost and exceeds this allowance.

### Functional and timing evidence

`check-sram-chip.py` regenerates the independent host vectors, checks all three
chips at RTL and at both mapped corners, and now records 508,252 external-pin edges
and 2,324 serial frames per simulation. These include UART TX, SPI mode 0, UART
good/bad stop capture, stretched I²C, all 16 capture bits, result ownership and
program replacement.
Each SRAM controller also passes 11,840 direct core edges: 1,000 consecutive
branches, immediate commit/start, every address in both banks, seven commits,
partial inactive writes followed by abort/restart, and malformed/over-capacity
push rejection. Collapsing the second read and disabling its write broadcast
both compile and then fail the core oracle, for both organizations.

`check-sram-timing.py` reads the complete mapped designs and **both the cell and
SRAM Liberty files** in pinned OpenSTA 2.7.0. The period is 20 ns, I/O delays are
4 ns maximum and 0.2 ns minimum, clock uncertainty is 0.2 ns, clock transition
is 0.15 ns and output load is 0.010 pF. Constraints cover the actual chip ports;
the SRAM response-to-address paths are explicitly reported. Clocks are ideal
and there are no wire parasitics. These are comparison assumptions, not board
or analog synchronizer guarantees.

| Chip | Typical setup / hold slack, ns | Slow setup / hold slack, ns | Max-fanout violations at each corner |
| --- | ---: | ---: | ---: |
| Flip-flop reference | +13.77 / +0.01 | +10.38 / +0.02 | 3,048 |
| Direct SRAM | +13.80 / **−0.42** | +9.97 / **−0.53** | 800 |
| Hybrid dictionary SRAM | +13.55 / **−0.58** | +10.26 / **−0.86** | 1,300 |

Neither SRAM variant meets hold yet. In the hybrid's worst slow hold path, a
serial data FF changes its output about 0.35 ns after the clock, while the SRAM
requires that write-data input to remain stable until about 1.21 ns, including
uncertainty. Delay/buffer repair must fix that physical path without adding an
execution edge. The reported setup margin does not remove this obligation.
All three unrepaired netlists also violate the library fanout limit; no slew,
capacitance, minimum-period or pulse-width violations were reported in these
two-corner, no-wire screens. The fast corner and extracted checks remain open.

### PDK compatibility and remaining integration

The physical PDK is pinned at `2bbec755dc67ca3db0261c3d6163e15735d66710`.
All 13 study views are byte-identical to blobs in its hash-verified Git tree,
despite the different study revision. The mapping Liberty files also match the
installed physical PDK byte for byte. Macro LEFs use Metal1–Metal4 and Via2;
their routing layers exist in the installed CMOS5L technology LEF.

This resolves **source/view compatibility**, not layout qualification. The local
SRAM installation was incomplete at this comparison. GDS, CDL and fast Liberty
views were not installed by this check; they are now frozen by the separate
[chip physical preparation](chip-physical-study.md).
Power pins need explicit integration: LEF names are `VDD!`, `VDDARRAY!`, `VSS!`,
whereas Liberty power groups omit `!`. GDS/CDL binding, power connections, macro
placement/halos, clock/hold/fanout repair, official-template routing, DRC and LVS
must be checked by the physical experiment.

The selected admission contract stays at 32 usable dictionary records, halt
padding in slots 32–63, indices below 32, and the existing canonical-word and
metadata checks. **No duration restriction or UART rewrite is indicated.**
`Storage.Sram` now proves the hybrid response-ownership model's initialized
trace refinement, including held Q during writes and commit/start bypass. The
shared bypass expression leaves all four experimental emissions byte-identical.
The September 21 composition below connects uploaded words and the actual fetch
schedule to that model. Complete emitted-chip composition remains a promotion gate.
Keep the direct prototype as a comparison if the hybrid's map routing or repair
cost overturns its area advantage.

`Memory.Sram` supplies the reusable array contract for that work. Each single-port
copy receives the same full-word write or an independent synchronous read, and Q
holds on writes. A partial model records which cells/responses are defined: the
physical copies may start with unrelated contents, and reset is not assumed to
clear SRAM. The proved relation survives arbitrary finite request histories;
accepted writes initialize every copy, reads of defined cells return the expected
word, and an inactive-bank write preserves every active-bank address. These facts
apply to either SRAM size.

`Storage.SramController` owns the experimental controller expressions.
Package composition, typed register ownership and SRAM interfaces now live in
`Storage.SramAssembly`; `test/SramChipEmit.lean` serializes that description.
All four MLIR and RTL emissions remain byte-identical after these moves.
`Storage.SramSchedule` collects edge obligations from the existing model.
The request lemmas connect
the hybrid core's actual write enable to accepted capacity-adapted uploads,
prove the address mux and low-six-bit macro binding, select index entries from
the correct bank (including commit), and establish broadcast host-data writes
and active-bank preservation through `Memory.Sram`. The physical read enable is
the complement of write enable, and commit enables a read.

`Storage.SramCoverage` now connects accepted-cursor progress to initializedness.
A valid bank has every dictionary word defined; a pending upload has initialized
the inactive-bank prefix below its cursor. This invariant survives every loader
transition and finite command history after initialization, including reset,
abort, rejected commands and interrupted/restarted uploads. Commit requires
cursor 322, so it selects a bank whose 32 physical dictionary words are defined.
Reset invalidates ownership; it does not clear either SRAM copy.

The controller's actual control-register updates and request expressions are
proved to follow the same transition. Each selected-bank read address is defined
when the chip is valid or committing. On a non-write edge, each related physical
copy returns the value recorded by the partial model. This holds independently
of the chosen program address, so it does not yet prove that the address is the
correct successor for execution.

### Closed-loop hybrid execution (2026-09-21)

`Storage.SramContents` proves that every defined dictionary word agrees with the
existing loader image. Accepted broadcast writes preserve that equality. The
actual selected bank and index lookup therefore return that image's word; this
strengthens the earlier initializedness result with value correspondence.

`Storage.SramExecution` combines that invariant with the replicated arrays and
shared controller. Array Q supplies the successor; no ideal-memory word is
substituted for a physical response. Both actual program-address expressions
match the existing two-port schedule, including word zero on commit. The
start bypass/save and write-held Q preserve the existing response-ownership
invariant. `core_step` checks each controller register against the same netlist
used by emission. The backend image retained in the proof state is specification
bookkeeping, not an additional physical memory requirement.

`initialized_trace` establishes the same observations on every later edge as
`Backend.referenceComponent`, after one initializing edge, from arbitrary
controller registers, array contents and Q. The existing capacity adaptation
remains in the reference; there is no new duration or UART admission rule.
The proof reuses the loader, scheduler, array contract and `Sram`/`TwoPort`
invariants. It does not define another instruction interpreter.

This closes the hybrid model's word/address/response/execution composition.
The package wrappers, external Verilog macro binding and emitted-chip read-back
still require their own correspondence evidence. Macro electrical behavior and
routed physical checks also remain separate. Direct SRAM's address/expansion
proof is not supplied by this result, and no default backend changes.

Reproduce with fresh tags and the pinned PDK installed locally:

```sh
python3 scripts/check-sram-chip.py --tag NAME \
  --pdk-root /path/to/installed/pdk --pdk-tree /path/to/pdk-tree.json
python3 scripts/check-sram-timing.py \
  --comparison build/storage/sram-chip/NAME/report.json --tag NAME
```

The first command uses local tools and views; the second uses the already
installed, identity-checked physical-tools container with two CPUs, 2 GB RAM,
120 seconds per invocation, no network and read-only input mounts. Receipts are
`build/storage/sram-chip/integration-02/report.json` and
`build/storage/sram-timing/integration-02/report.json`; the journal preserves the
[original comparison](research/journal.md#2026-09-19-complete-sram-chip-comparison)
and the later integration refresh. The new shared response expressions preserve
the original emitted bytes, and the fresh hybrid RTL matches all physical attempts.

## Latches

The pinned typical CMOS5L standard-cell library contains these cells:

| Cell | Cell area, µm² |
|---|---:|
| `sg13cmos5l_dfrbpq_1` (FF reference) | 48.9888 |
| `sg13cmos5l_dlhq_1` | 30.8448 |
| `sg13cmos5l_dlhr_1` | 32.6592 |
| `sg13cmos5l_dlhrq_1` | 27.2160 |
| `sg13cmos5l_dllr_1` | 34.4736 |
| `sg13cmos5l_dllrq_1` | 29.0304 |

For 6,080 storage bits, multiplying the reference FF area gives 297,851.904 µm²;
multiplying the smallest listed latch area gives 165,473.280 µm². This comparison
is a cell-only lower bound. It omits clock/enable circuitry, input buffering,
write decoding, timing closure, and the remaining machine. The latch cells have
different polarity/reset behavior and are not interchangeable replacements.

A transparent latch can change during part of a cycle. Directly gating it with
live host command/data can therefore modify staging storage before the edge on
which an upload is accepted or rejected. A viable implementation needs a phase
contract, stable write selection, and appropriate clock/enable circuitry. A
registered upload followed by a separate write phase may preserve external
behavior, but requires a new phase-aware proof and a check that commit cannot
expose an incomplete write. The existing edge-based equality theorem alone does
not establish that behavior.

## Primitive inventory reproduction

`python3 scripts/inspect-storage-macros.py` downloads selected public views at the
fixed revision and records SHA-256 identities, LEF dimensions, and typical/slow
Liberty metadata in `build/storage/macros/report.json`. It does not install tools,
map a design, or run placement/routing. The standard-cell source identity remains
in `tools/technology-library.json`.

Retain the proved flip-flop machines as references and the 64-entry machine for
programs that exceed the small dictionary. The complete-chip comparison above owns the
current SRAM decision; raw bit-cell savings alone do not justify replacement.
Latch storage still needs the distinct phase contract described here.
