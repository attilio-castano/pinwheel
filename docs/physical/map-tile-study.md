# Local decoding in the index map

The separate and combined complete-chip tile candidates pass functional
validation. The combined boundary saves about 1.08% of standard-cell area and
limits fanout to ten, but neither candidate reduced the maximum address depth.
The subsequent [fetch-deadline and electrical study](../fetch-contract-study.md)
supersedes the original decision to defer timing: six retained-netlist STA runs
take about five seconds. They identify SRAM response delay, hold obligations
and a library fanout limit of eight. A measured flat repair costs more than the
tile saving, so neither candidate is promoted. Gate depth remains diagnostic;
strict depth improvement is no longer a prerequisite for cheap STA.

The preceding map-only experiment remains useful evidence: its 18-input-bit,
10-output-bit tiles and 346 distribution buffers reduce local fanout to ten,
leaving 0.2189% area saving and ten read-logic levels. Integration exposes the
controller work and shared loads outside that boundary.

The [original receipt](../../physical/experiments/map-tile-results.json) records
`build/storage/map-tile/local-decode-03/report.json`; the
[buffered receipt](../../physical/experiments/map-distribution-results.json) records
`build/storage/map-tile/distributed-02/report.json`. The
[complete-chip receipt](../../physical/experiments/tiled-chip-results.json) records
`build/storage/tiled-chip/integration-03/report.json`. The
[slice study](map-slice-study.md) and [original plan](../../physical/experiments/map-tile-plan.json)
remain historical evidence. [Research status](../research/status.md) owns allocation.

## One implementation, existing semantics

`Storage.MapTile.circuit` reuses `Memory.Flops.circuit 4 5 2`, whose latency-zero
memory refinement already exists. There is no second memory implementation or
new execution semantics. For bank `b` and low address nibble `l`, tile word `h`
is the existing index word at address `h ++ l`. The 32 tiles retain exactly
2,560 state bits; each tile has 80 flip-flops and no registered read output.

Six new kernel-checked lemmas establish:

- The full nine-bit cursor matches a word's existing store offset exactly when
  it lies in 64–319 and both nibbles match. Truncating without the range check
  would alias unrelated uploads into map words.
- Every tile next-state word equals the corresponding existing store update.
- Both tile reads equal the restricted current `Execution.readTree`; selecting
  the tile by the PC's low nibble recovers the complete lookup.
- The tile update matches the actual `SramController.core false` after existing
  capacity, loader and inactive-bank admission. The result holds for every
  input and state, including rejection, reset and abort/replacement histories.
- Both reads retain the actual controller's candidate PCs and selected bank,
  including commit/start selection. No extra edge or branch-spacing assumption.

These are local correspondence results. The retained hybrid baseline is
unchanged. A separate complete-chip candidate now instantiates the tiles using
the existing SRAM binding, fetch schedule and upload admission.

## Complete map comparison

The flat probe emits the current balanced `readTree` for both banks and readers,
and the current per-word loader offsets. The tiled probe uses 32 instances of
the same tile plus one combinational glue module. Lean emits the selectors and
write decoder; a thin generated Verilog wrapper connects the enumerated ports.
Global command admission stays outside both probes.

Both probes have the same map-level interface, state and behavior: two PCs,
read bank, accepted write, write bank, nine-bit cursor and five-bit data. This
controlled comparison measures the **complete map subsystem**, not the whole
chip and not the earlier private-cell partitions of its shared mapped logic.

| Mapped map-only cost | Flat | Tiles plus glue | With distribution |
| --- | ---: | ---: | ---: |
| State bits / FFs | 2,560 | 2,560 | 2,560 |
| Combinational cells | 7,518 | 5,988 | 6,334 |
| Standard-cell area, µm² | 253,254.9348 | 250,189.4304 | 252,700.5600 |
| Read-zero gate depth | 14 | 9 | 10 |
| Read-one gate depth | 13 | 9 | 10 |
| Next-state gate depth | 8 | 8 | 8 |
| Maximum signal sink count | 10 | 224 | 10 |

Before distribution, the area difference is **3,065.5044 µm² (1.21%)**.
A tile costs 7,664.0256 µm²,
including 80 FFs and 178 combinational cells. All 32 copies cost 245,248.8192 µm²;
the remaining 292-cell glue costs 4,940.6112 µm². These disjoint costs reproduce
the flattened mapped total. Exactly 32 tiles and one glue instance survive
mapping. There are 369 distinct signal nets at tile boundaries: 49 shared or
selected inputs and 320 partial-read outputs, excluding clock. Each tile still
has the intended 18 input and 10 output bits.

Typical and slow mappings give the same cell census, area and depth here. The
mapping uses the same pinned IHP CMOS5L libraries, driver, output-load setting
and ABC target as the previous chip comparison. It deliberately preserves
tile/glue hierarchy, whereas the flat probe is one module. The per-module load
assumption does not account for all inter-module broadcast loading. ABC's
individual module delay estimates therefore cannot be treated as end-to-end
timing or compared as if they were extracted chip slack.

## The remaining communication cost

Local decoding narrows the tile boundary. It also duplicates decoding and
makes high address bits and write data common inputs to many tiles. In the
composed graph, PC bits reach up to 64 sink pins and cursor/data bits up to 224.
The flat map's synthesis already distributes these through buffers and has a
maximum fanout of ten.

### Bounded distribution result

The follow-up reuses the exact retained typical and slow mappings. It adds
`sg13cmos5l_buf_1` instances at the parent and rewires child input connections;
every tile, glue and library module remains identical. Seventeen shared bits
receive trees: nine write-address/data bits and eight read-address bits.
The trees contain 346 buffers at 7.2576 µm² each, adding **2,511.1296 µm²**.
The remaining difference from the flat map is **554.3748 µm² (0.2189%)**.
Typical and slow results agree on these structural measurements.

The transform counts actual cell input pins inside each child. Some tile inputs
consume seven pins, so counting 32 module connections would understate a
224-pin load. It resolves the glue's pass-through aliases, retains fixed loads
on source nets, groups leaves within each logical bank and adds parent buffers
when needed. Read distribution adds one buffer level; write distribution adds
up to two. Complete-map next-state depth stays eight after insertion.
Yosys independently flattens the result and confirms every signal
fanout is at most ten, including internal nets; clocks are excluded.

This is a deterministic structural construction, not an area-optimal tree or
a placement. Ten is the flat comparison's observed sink count, **not a
technology signoff limit**. Sink types and capacitances differ. Matching this
count does not establish equal delay, valid slew or adequate drive strength.
Wire length, switching power, electrical limits, placement legality and
physical timing remain unmeasured. Per-module ABC delays from the original
mapping do not describe the added distribution network.

This near-equal-area map with fewer read levels justified the complete-chip
comparison below. Its acceptance screen required no area regression, a lower
maximum address depth and no increase in maximum signal fanout before timing
or physical allocation. The map-only margin did not establish those properties
for the chip.

## Complete-chip integration — September 22

`TiledMap` now owns the shared interface, reference circuit and selection glue;
the original map emitter consumes it and preserves all four emitted map
artifacts byte for byte. `TiledController` reuses the existing controller,
serial receiver, sampler and result observer. It exposes actual candidate PCs,
selected bank, admitted push, inactive write bank, cursor and payload, and
receives the two five-bit lookup results. The original 2,560 map registers are
excluded from the controller's emitted list and owned exactly once by 32 tiles.
No execution edge, SRAM macro, capacity rule or host protocol changes.

The general `Netlist.toCircuit` substitution has step/observation proofs. The
split preserves remaining transitions; its core outputs match after connecting
the original indices. Further Lean results tie both map reads and every update
to actual controller computations. Package wiring and mapped cells are checked
independently below. This does not add a complete Lean theorem for the external
Verilog macro model and package trace.

| Complete chip, typical library | Retained hybrid | Tiled candidate |
| --- | ---: | ---: |
| Physical FFs | 2,895 | 2,895 |
| SRAM macros | 2 | 2 |
| Combinational cells | 12,593 | 8,327 |
| Standard-cell area, µm² | 292,580.0514 | 288,888.2010 |
| Cells plus SRAM footprints, µm² | 393,558.3170 | 389,866.4666 |
| Address depth, ports zero/one | 29 / 29 | 30 / 30 |
| Maximum next-state depth | 27 | 24 |
| Maximum signal sink count | 11 | 15 |

Typical standard-cell area falls **3,691.8504 µm² (1.261826%)**; including the
unchanged SRAM footprints, the reduction is **0.938069%**. Slow mapping uses
one additional buffer in the candidate: 288,895.4586 µm² of standard cells,
1.259345% below baseline. Its address depths are 30/30 versus baseline 29/30,
and maximum fanout is again 15. Both corners fail the structural screen.
Cell counts exclude `$scopeinfo` metadata; areas include every physical cell.

The local diagnostic `build/validation/tiled-chip-02/boundary-diagnostics.json`
(identified by the tracked [tile result](../../physical/experiments/tiled-chip-results.json))
locates the composed loads. Cursor bits zero and one each drive eight engine
pins and seven map pins. Upload-data bits three and four each drive seven
engine pins, four map distribution roots and two SRAM pins. A map-internal
budget of ten therefore leaves loads up to fifteen on its external producers.
One deepest path to each candidate SRAM address begins at cached-word bit 35
and contains twenty engine gates plus ten map gates. These are conservative
graph paths, not measured cell or wire delays.

This result motivated the combined controller/selection comparison below,
retaining storage tiles and budgeting each producer's loads across all consumers.
The separate synthesis boundaries lose the isolated map's depth advantage;
the area reduction alone does not justify placing this candidate. Macro positions
and the half-height corridor remain reserved for a later qualifying physical
comparison. Existing routing/antenna problems remain open.

## Combined controller and selection — September 22

The opt-in `--organization combined` mode keeps the 32 `pinwheel_map_tile`
instances while flattening the surrounding controller, selection glue and
package wrappers before technology mapping. The Lean circuit, emitted RTL,
state projection, tools, libraries and SRAM views match the preceding study.
The existing separate mode remains the default. Each tile still contains exactly
80 FFs and 178 combinational cells; buffer insertion preserves all child modules.

Distribution now counts actual loads across the complete chip, including direct
controller gates, tile inputs and both SRAMs. The macro terminals remain fixed
and consume the source budget. Binary tie-offs and clock wiring remain intact;
unknown values, conflicting aliases and unsupported boundaries are rejected.
The same helper reproduces both prior separate mapped hierarchies and buffer
receipts exactly, without rerunning synthesis.

| Complete chip, typical library | Original hybrid | Separate tiled | Combined tiled |
| --- | ---: | ---: | ---: |
| Physical FFs / SRAM macros | 2,895 / 2 | 2,895 / 2 | 2,895 / 2 |
| Standard-cell area, µm² | 292,580.0514 | 288,888.2010 | 289,427.1156 |
| Cells plus SRAM footprints, µm² | 393,558.3170 | 389,866.4666 | 390,405.3812 |
| Address depth, ports zero/one | 29 / 29 | 30 / 30 | 30 / 29 |
| Maximum next-state depth | 27 | 24 | 25 |
| Package `uo_out` depth | 14 | 14 | 15 |
| Maximum signal sink count | 11 | 15 | 10 |

Both combined corners have these candidate metrics. The slow baseline has
address depth 29/30 and package output depth 13. Combined mapping adds 354
distribution buffers costing 2,569.1904 µm², already included in the table.
Standard-cell area is **1.077632% below the original baseline** and about
539 µm² above the earlier typical tiled candidate. Aggregate fanout now passes,
but maximum address depth does not decrease at either corner; package output
depth also grows. The original receipt deferred timing and physical allocation.
The [subsequent timing study](../fetch-contract-study.md) supersedes that allocation
rule while preserving this receipt. These gate and sink counts do not measure
delay, electrical limits or wire costs.

The local path diagnostic `build/validation/combined-chip-01/boundary-diagnostics.json`
(identified by the tracked [combined result](../../physical/experiments/combined-chip-results.json))
traces one deepest path per address from cached-word bit 35. The two paths have
18 controller/selection gates before a candidate PC, one distribution buffer,
four tile gates, then seven or six final selection gates. No signal exceeds ten
sinks. The remaining depth therefore spans candidate computation and lookup;
it is not removed by changing the synthesis boundary. Some optimized-away named
nets survive as metadata and are recorded as absent (`null`), without assigning
them a depth. Every live measured path still agrees with `chip_metrics`.

This motivated the completed [candidate-dependency and electrical checks](../fetch-contract-study.md).
They prove capture forwarding and metadata dependence, compare complete-chip
timing and measure a library-budget repair. Immediate commit/start and
consecutive one-cycle branches remain required. Neither an added pipeline stage
nor removal of validity checks follows from the structural or timing reports.

The [selected receipt](../../physical/experiments/combined-chip-results.json) binds
`build/storage/tiled-chip/combined-01/report.json`, the diagnostic and source
hashes. The **274.167-second** run passes four positive arbitrary-state SAT
checks, rejects both a joined address and an inverted distribution buffer,
replays 1,536,596 core/package edges, and independently rereads both mapped
Verilog corners. The 180-second cap applies to each external command; the
longest command took 74.092 seconds. Twenty-seven focused Python tests pass,
and the unchanged library audit covers 14,831 declarations / 7,529 theorems.
All 252 frozen inputs and 123 generated artifacts were verified after completion.
All 45 preceding experiment manifests remain unchanged. This study changes
only synthesis/distribution tooling and tests; no Lean definition, execution
schedule, production backend, timing or physical run changes.

## Independent checks and reproduction

```sh
python3 -B scripts/check-tiled-chip.py --tag CHIP_NAME
python3 -B scripts/check-tiled-chip.py --tag COMBINED_NAME --organization combined
python3 -B -m unittest discover -s test -p test_tiled_chip.py -v
python3 -B -m unittest discover -s test -p 'test_map*.py' -v
```

The separate complete-chip run takes **254.643 seconds** with a 180-second cap per
external command. Four SAT checks prove the core and chip RTL, then both mapped
chip corners, against the unchanged controller RTL with arbitrary SRAM
responses and reference state. Joining the two SRAM addresses is rejected.
Actual external pin aliases, both macro instances and every address/data/read/
write/mask/BIST/clock terminal are validated before abstracting macro outputs.

Generic RTL retains 2,901 state bits. Both mapped chips prune the same six
unused cached-word bits (3–8), leaving 2,895 physical FFs. The comparison omits
only the absent slots' next values; their reference current-state inputs remain
arbitrary. SAT must still prove every external output and every surviving
next-state bit, so it establishes their noninterference without a reset or
reachability assumption. Exact FF bijections and rejection tests guard this
projection. Independently reread mapped Verilog reproduces all metrics.

The independent external-pin oracle passes **508,252 edges each** on chip RTL
and both mapped corners. The core oracle passes 11,840 edges, including 1,000
consecutive branches, all addresses, bank replacement, rejection and immediate
start. Together these are 1,536,596 simulated edges. Twenty-four focused Python
tests pass; the standard-axiom audit covers 14,831 declarations / 7,529 theorems.
The checker freezes 248 inputs and records 119 generated artifacts. The retained
hybrid chip/core emissions are byte-identical to `corridor-02`; no baseline
replacement, timing, placement, routing or Docker run occurs.
The separate `tiled-chip-boundary-01` gate takes 16.161 s, verifies all four
hybrid/direct MLIR/RTL pairs against `corridor-02`, reruns the library audit and
`Interfaces`, and checks both mapped Verilog read-backs. Its 241 frozen inputs
match the completed checkout.

`integration-01` stopped at a reserved Verilog instance name. `integration-02`
passed RTL equivalence but stopped because the checker compared mapped pruning
to the unpruned generic state list. A mapped-baseline pruning check and the
arbitrary-current-state comparison above resolve that distinction.
`integration-03` passes validation and records `defer-timing-and-physical`.
All attempts and earlier receipts are retained.

The original map-only commands are:

```sh
python3 -B scripts/check-map-tile.py --tag NAME
python3 -B scripts/check-map-tile.py --tag BUFFERED_NAME \
  --distribute-from physical/experiments/map-tile-results.json --fanout-limit 10
```

The historical distribution receipt requires its frozen source snapshot and
rejects later source changes. The current complete-chip checker instead verifies
the retained map artifact hashes and requires the shared emitter's bytes to
match them. Tags are create-only. Every map-only external command has a
180-second cap. The selected
complete run took **77.772 seconds**, including emission, six library mappings
and the formal checks. No physical tool or Docker container was launched.

The checker cuts only validated positive-edge FFs, exposes all Q values as
arbitrary inputs and every D value as an output, and checks an exact bijection
to the typed bank/word projection. Independent behavioral Verilog defines both
reads and updates by direct indexing and store offsets. Yosys SAT proves equality
of every next-state bit and both outputs for all binary states and inputs.
There are nine successful checks: tile, flat map and tiled map at RTL and at
both mapped corners. Mapped checks consume independently reread Verilog; its
area, state, depth and fanout also agree with mapped JSON. A deliberately joined
pair of read outputs is rejected. These checks do not assume cleared storage or
replace physical/X-state qualification.

The library audit covers 14,526 declarations and 7,421 theorems using only the
existing standard axioms. Six checker tests reject incorrect coordinates,
missing/aliased state, wrong clock/reset, unsupported flops and invalid areas;
the existing 30 architecture tests also pass. A separate unchanged-chip gate
regenerates all four existing MLIR/RTL artifacts and compares them byte for byte
with `corridor-02`.

The buffered run took **37.020 seconds**, including two mapped arbitrary-state
SAT proofs and rejection of a deliberately inverted distribution buffer.
Mapped JSON and independently reread Verilog agree on the exact FF bijection,
cell census, area, depth and fanout. The comparison first verifies the original
receipt, all 102 retained artifacts, tools, pinned libraries and unchanged
hardware/oracle inputs, and reproduces both original baselines' metrics. Only
the extended checker differs from the original source snapshot; its current
hash and all 213 current inputs are frozen. No new synthesis was necessary.

Fourteen focused Python tests pass, including weighted loads, pass-through
aliases, fixed root loads, multiple levels, bank grouping, invalid/ambiguous
connections and stale evidence. A small regression also repeats the shared
checker on the saved generic tile and rejects the joined-reader mutation.
The existing production identity gate's 239 inputs all still match; its prior
byte-identical emissions and Lean audit remain applicable. No new Lean proof,
production emission, placement, routing or Docker run was needed here.

Earlier attempts are preserved. `local-decode-01` stopped at the axiom audit:
the first cursor proof used a native SAT-certificate check, replaced with
kernel-checked arithmetic. `local-decode-02` stopped when the negative control
failed to reject: changing a JSON output port without its same-named net did
not change the imported circuit. The corrected mutation changes both, and
`local-decode-03` passes every gate. No failed attempt is selected as evidence.
The first distribution attempt, `distributed-01`, stopped before export because
a generated cell and wire shared a name in Yosys. Separate wire names fix the
collision; a regression checks disjoint names. `distributed-02` passes all gates,
and both attempts are retained.
