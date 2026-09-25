# Validation and review gates

Run the local checks below before pushing a PR. Hardware experiments remain
separately reproducible with the pinned Apple Silicon tools and explicit fixture
prerequisites. Passing the portable gate does not establish emitted-RTL
equivalence, physical fit, or an operating frequency.

The [integration record](history/branch-integration.md) identifies retained interfaces,
experimental backends and proof obligations at consolidation. When integrating
a staged subset, validate that exact source snapshot so uncommitted modules
cannot supply a dependency missing from the commit. Reusing a prior validated
Lean build cache is acceptable; the current source build, complete import
coverage and axiom audit must still pass. Generated fixtures belong to the
isolated snapshot, preserving earlier experiment outputs.

## Local pre-push checks

Install the repository's `lean-toolchain` with Elan and use Python 3.12+:

```sh
python3 -B -m unittest discover -s test -p 'test_*.py'
python3 scripts/check-foundation.py --tag first-check
```

The first command checks physical input/checkpoint provenance, backend import
boundaries, receipt binding, bank-selection helpers, DEF route parsing and
process-group timeout cleanup, host input/readback/timeout boundaries, shared command logging and reasoned negative
checks using disposable files and Python children; it
requires no CAD tools. The second runs the portable Lean/model gate.

`test_host_demo.py` and `test_host_receipts.py` also run in optimized Python
children. They reject invalid observations, require repeated mailbox reads and
consumption checks, bind receipts to captured input bytes despite later file
replacement, and check that failed demonstrations publish no success receipt.
Their CAD commands and host observations are stubbed; these are validation-tool
regressions, not new RTL or physical evidence.

The runner requires no prior `.lake/` or `build/` content. Each run writes logs,
commands, source hashes and a success receipt under `build/validation/<tag>/`.
Choose a fresh tag to preserve earlier gate evidence. Other model suites retain
their existing output locations, so use a separate checkout to preserve previous
experiment outputs when rerunning them. A failure produces no success receipt.

The gate:

1. Checks that every library module is reachable from `Pinwheel.lean` and that
   the actual compiler matches the repository pin, then runs `lake build` with
   warnings treated as errors.
2. Audits every Pinwheel declaration in the compiled environment, including
   private and generated declarations and definitions containing proofs. Only
   `propext`, `Classical.choice`, and `Quot.sound` are allowed. An injected custom
   axiom must fail for the expected diagnostic. Counts include generated
   theorems; they are not counts of manually written mathematical results.
3. Runs UART TX/RX, link timing, continuous buffered reception with ideal and
   unequal clocks, SPI, shared engine, reactive I²C, explicit/counted/binary execution,
   register reads, encoding, countdown, timed-interface/fetch, and storage
   certificate checks, serial upload and host-result ownership checks. Their
   existing negative cases remain included.
4. Independently decodes and checks generated PWL images and UART RX E64 execution
   with Python oracles. RX includes every supported period/input storage configuration.

The [continuous UART suite](protocols/uart-stream.md#validation-and-reproduction) checks
all 65,536 ordered byte pairs, independent wire/queue oracles, consumer stalls,
reset/error recovery, and exact correspondence with the compiled RX supervisor.
The [unequal-clock stream suite](protocols/uart-stream-clocks.md#validation-and-reproduction)
adds independent physical-time wire and detection schedules, varying observation
age, relative phases, rearm boundaries, and cases outside the sufficient bounds.
These are Lean/model checks; the supervisor's new buffer has no RTL validation yet.

Validation runs locally; the repository has no automatic GitHub Actions workflow.
Include the check results and source identity in the PR description. Before
pushing, verify that the committed sources match the validated sources. If code,
tests, or validation inputs change, run the affected checks again. Documentation
edits require link and whitespace checks.

## Hardware prerequisite order

These are explicit local gates, not mandatory cloud CI jobs. The checked archives
in `tools/hardware-toolchain.json` target **darwin-arm64**; do not use them in a
Linux workflow. Install the pinned tools and Liberty libraries as described in
[development](development.md). The physical flow has a separate container/PDK pin.

For a new checkout, the relevant dependency chain is:

| Gate | Inputs to generate first | Evidence owner |
| --- | --- | --- |
| Countdown artifact/equivalence | `check-hardware.py` generates its own fixtures; pinned CIRCT/Yosys/Icarus binaries required | [Hardware closure](engine/hardware-closure.md#countdown-artifact-interpretation-rather-than-a-compiler-proof) |
| Full-backend Lean RTL read-back | `check-backend-readback.py --tag NAME` regenerates its own artifact; pinned CIRCT/Yosys/Z3 binaries required | [Full read-back](engine/hardware-closure.md#full-backend-rtl-read-back) |
| Composed dense cached backend | `check-backend.py --tag NAME` builds the native emitter and loader fixtures; pinned hardware tools and technology libraries required | [Composed backend](engine/hardware-closure.md#composed-backend) |
| Program-bank selection variants | `check-backend-readback.py --variant command-split` or `--variant late-bank`, followed by `check-bank-select.py` with the exact proof receipt | [Bank-selection study](storage/bank-selection-study.md) |
| Cache-enable variant | `check-backend-readback.py --variant enable-split`, followed by `check-bank-select.py` and exact-cache regression | [Cache-enable study](storage/cache-enable-study.md) |
| Pin-sampled backend | `check-sampled.py --tag NAME --variant command-split`: inner emission identical to the read-back-proved RTL, reference-pipeline equivalence, wrong-depth rejections, pin-shifted independent oracle and mapping | [Pin-sampler study](pin-sampler-study.md) |
| Fetch-policy backends | `check-prefetch.py --tag NAME` (decoupled, three ports), `--variant twoport`, `--variant oneport`: emission alone and behind the pin pipeline, RTL/generic-gate equivalence of both (two-step induction; three for one port) with registers that synthesis narrows re-exposed at full width so that name matching compares them, the independent oracle on both with pins shifted for the sampled one and rejected unshifted, and mapping. The one-port variant runs the oracle in ready mode — the UART receiver exercise replaced by a register read, the terminal-capture branch record given one cycle, no pushed word outside the readiness rule — and must be rejected on the unrestricted vectors | [Memory abstraction](memory-abstraction.md#fetch-organizations-as-a-parameter) |
| Chip with host results | `check-chip.py --tag NAME --variant twoport` or `oneport`: actual serial pins, retained capture reads/consume/overflow, reset and replacement, RTL/generic-gate equivalence and simulation, corruption rejection. One-port emission enforces readiness; UART RX is exercised only on two ports | [Whole chip](engine/whole-chip.md#host-result-interface-version-1) |
| SRAM schedule feasibility | `inspect-storage-macros.py`, then `check-sram-feasibility.py --tag NAME`: pinned public models, expanded uploads to two atomic banks, immediate start, consecutive branch requests and explicit area scenarios; no mapping or physical claim | [SRAM study](storage-primitives.md#bounded-sram-scheduling-study-2026-09-19) |
| Experimental upload stage | `python3 -B scripts/check-upload-pipeline.py --tag NAME`: current Lean build/emission, pinned digital macros, independent core/pin traces and a compiled write-priority mutant; 120 s per command, create-only receipts. No placement or routing | [Upload schedule and boundaries](fetch-contract-study.md#experimental-upload-pipeline--september-22) |
| Hybrid array/controller proof | The default `Pinwheel` import includes `SramContents` and `SramExecution`; `check-foundation.py --tag NAME` builds and audits initialized trace refinement and actual controller-register correspondence using the unchanged standard-axiom gate | [Closed-loop execution](storage-primitives.md#closed-loop-hybrid-execution-2026-09-21) |
| Complete SRAM chips | `check-sram-chip.py --tag NAME --pdk-root PATH --pdk-tree PATH`: verified local views; direct/hybrid/FF RTL and both technology-mapped corners against the independent external-pin oracle; SRAM core stress and two mutations | [Complete comparison](storage-primitives.md#complete-chip-comparison-2026-09-19) |
| SRAM assembly and architecture | `report-chip-architecture.py --tag NAME --comparison build/storage/sram-chip/PRIOR`: builds/audits current Lean, runs `Interfaces`, requires four regenerated MLIR/RTL pairs to match the saved comparison, then binds state, computations and mapped consumers with Verilog read-back. Optional paired `--placed-context FILE --placed-database FILE` require exact database/exporter/helper hashes; `--locality-windows physical/experiments/sram-address-locality.json` adds an unlegalized all-incident-net projection. Run `python3 -B -m unittest discover -s test -p test_chip_architecture.py -v` for rejection controls. No new synthesis, RTL simulation, placement or routing | [Computational and locality checks](physical/chip-architecture-study.md#computational-map-and-phase-cuts) |
| SRAM pre-layout timing | `check-sram-timing.py --comparison build/storage/sram-chip/NAME/report.json --tag NAME`: pinned local OpenSTA container, complete cell/macro arcs and chip-port constraints; reports hold/electrical failures without claiming physical closure | [Timing boundary](storage-primitives.md#functional-and-timing-evidence) |
| Map slice budgets | The same `report-chip-architecture.py` gate now emits `hybrid-map-slices.json`: typed bank/word coordinates, bit planes, consecutive tiles and tiles following `readTree`; exact stored-bit support checks, shared-control accounting, retained Liberty areas reconciled with the original total, and boundary/cost agreement with Verilog read-back. The existing architecture Python suite includes slice and renaming rejection controls | [Map-slice reproduction](physical/map-slice-study.md#reproduction-and-limits) |
| Local-decoding map tile | `check-map-tile.py --tag NAME`: builds/audits the reused memory and controller projection; emits one tile, flat map and complete tiled map; checks every output and next-state bit against independent behavioral Verilog for arbitrary binary states at RTL and both mapped corners. Verilog read-back, exact state/port checks, a joined-reader negative control, hierarchy/area/depth/fanout accounting; 180-second cap per command. `test_map_tile.py` tests fail-closed state/clock/reset/coordinate handling. No whole-chip replacement or physical run | [Map-tile reproduction](physical/map-tile-study.md#independent-checks-and-reproduction) |
| Map buffer distribution | The same checker with `--distribute-from physical/experiments/map-tile-results.json --fanout-limit 10`: verifies retained artifact/source/tool hashes, inserts actual library buffers while preserving child modules, counts internal sink pins and glue aliases, checks flattened and reread Verilog metrics, proves all outputs/next-state bits at both mapped corners and rejects an inverted buffer. `test_map_distribution.py` checks weighted loads, aliases, bank grouping, unsupported boundaries and stale evidence. No new synthesis or physical run; 180-second cap per command | [Distribution result and limits](physical/map-tile-study.md#bounded-distribution-result) |
| Complete-chip tiled map | `check-tiled-chip.py --tag NAME`: build/audit actual controller/map wiring, require retained baseline/map emission identity, four core/chip RTL and mapped-corner SAT checks, address-mutation rejection, exact package/macro terminals, paired mapping and Verilog read-back, then existing core/package-pin oracles. All reference current-state inputs remain arbitrary; only next values of six slots absent in both mapped chips are excluded. `test_tiled_chip.py` checks state projection, pruning, actual ports and macro constants. Reports structural acceptance separately from functional success; 180-second cap per command | [Complete-chip result](physical/map-tile-study.md#complete-chip-integration--september-22) |
| Experimental paired controller | `check-paired-controller.py --tag NAME`: emit the typed controller with existing wrappers, validate core/package traces, exact one-macro/state intake, both saved mapped corners and typical mapped pin replay, then include SRAM arcs in cell timing under the eight-load policy. Axiom, stale-row and inverted-buffer negatives must fail. `test_paired_mapping.py` and `PairedGraph.lean` check malformed intake and shared-expression construction without CAD. Create-only receipts; 120-second command caps; bounded local STA containers; no placement/routing | [Complete controller and macro timing](storage/compact-execution-study.md#complete-controller-and-macro-timing) |
| Combined controller/selection | The same checker with `--organization combined` retains all 32 storage tiles and optimizes the surrounding logic together. Requires the preceding tiled RTL/projection/tool/library identities, reproduces its mapped metrics, counts all controller/tile/fixed-macro loads, checks unchanged child implementations and reconciles every added cell after flattening/read-back. Repeats the full equivalence/pin gate and rejects an inverted distribution buffer. Optional `--fanout-limit 8` applies the pinned unit-load library budget during ABC mapping and aggregate distribution, rejects the incomplete separate boundary, and leaves baseline mapping unchanged. `test_map_distribution.py` checks fixed terminals, tie-offs, unknowns and aliases; `test_tiled_chip.py` additionally rejects library-budget mismatches. Successful checks are eligible for cheap STA; the structural score is diagnostic. Same 180-second command cap | [Combined result](physical/map-tile-study.md#combined-controller-and-selection--september-22), [library-budget follow-up](fetch-contract-study.md#local-mapping-with-the-library-budget--september-22) |
| Interactive host demonstration | `pinwheel-host.py demo --backend hybrid --tag NAME` (or `reference`): builds its dependencies, loads protocol/custom programs on one fixed RTL chip, checks pin-only peers and retained results; pinned macro models required for hybrid | [Host workflow](host-workflow.md) |
| Whole-chip physical experiment | `prepare-chip-physical.py --comparison REPORT --design NAME [--fetch]`, then `run-physical.py --design NAME --tag RUN --pdk-root PATH --timeout-seconds SECONDS`: verified comparison/PDK/container, chip SDC, pinned macro views and official DEF; no shared-PDK modification | [Chip physical study](chip-physical-study.md) |
| Routing diagnosis | Enable `physical/experiments/routing-diagnostics.json` through `--overrides`; export a retained database with `routing_context.py` in pinned OpenROAD Python, then run `diagnose-routing.py` on its matching iteration report. It requires a stopped run, verifies database identity and completed log counts, and emits classification plus SVG/HTML. A separate `routing_keepouts.py` derives the controlled macro-obstruction checkpoint | [Routing diagnosis](chip-physical-study.md#routing-diagnosis-2026-09-19) |
| Macro orientation / guide screen | Stage with `prepare-chip-physical.py --macro-placement FILE` to change only existing macro placements in a separate design; the runner validates the derivation on fresh and resumed runs. `report-routing-guides.py` binds a guide to the same completed step's database/context and counts body overlaps by layer. These are coarse guides, not wires or DRC | [Orientation experiment](chip-physical-study.md#orientation-experiment-2026-09-19) |
| Placement corridor | Add `--placement-exclusions FILE` during preparation. In pinned OpenROAD Python, export each completed placement/repair database with `routing_context.py --placement-exclusions FILE`; require no intersecting rows/cells and the matching hard blockage after legalization and repair. `physical_checkpoint.py --design PATH` captures/verifies the named design | [Reserved-corridor screens](chip-physical-study.md#reserved-corridor-screens-2026-09-21) |
| Physical chip netlist view | `check-chip-physical.py --physical-report REPORT --comparison COMPARISON --pdk-root PATH --tag NAME`: checks the reported netlist's identity, replays the complete pin oracle and rejects output corruption using pinned cell/macro models. Records the actual netlist view because a physical state may inherit it from an earlier step | [Chip physical study](chip-physical-study.md) |
| Clock-gated routed netlist | `check-physical-netlist.py NETLIST --label NAME --vectors VECTORS`, then `check-clock-gates.py NETLIST --label NAME`: every integrated clock gate stuck open or shut must be rejected by the retained traces | [Physical correlation study](physical-correlation-study.md#third-attempt-clock-gated-03-routes) |
| Structural levels | `check-structure.py --tag NAME`: Lean arrival levels against MLIR depths, mapped cone depths and routed launch-family ranking recorded in tracked manifests; for each fetch-policy backend, the deepest endpoint per launch family and the requirement that the loader's data port reaches no register of the fetch path (also a theorem, `Storage/DataPort.lean`); needs Lean only | [Structural timing](engine/structural-timing.md) |
| Lean gating plan on unchanged RTL | `gate-clocks.py --rtl RTL --plan PLAN --testbench DIR --tag NAME`: netlist versus plan bit by bit, oracle with every storage register observed, every stuck clock-gate enable rejected, two mapped corners | [Register enables](physical/register-enables.md) |
| Original UART/SPI core | No prior protocol fixtures; `check-core.py` generates its own | [Original core](engine/core-hardware.md) |
| Reactive core | No prior binary fixtures; `check-reactive-core.py` generates its own | [Reactive core](engine/reactive-core-hardware.md) |
| Atomic loader | No prior binary fixtures; `check-loader.py` generates its own | [Atomic loader](storage/atomic-loader.md) |
| UART RX integration | No prior fixtures; `check-uart-rx-hardware.py --tag <fresh-tag>` regenerates mixed-protocol traces and simulates four backends, including the default dense cached core | [UART receive](protocols/uart-receive.md) |
| E64 frontends | Run `check-binary.py`, then `check-execution.py` | [E64 hardware](storage/execution-hardware.md) |
| Dense codec | Execution decoder vectors from the preceding frontend check; create `build/storage` with `test/Storage.lean`, then run `check-dense-codec.py` | [Storage study](storage/storage-study.md) |
| Cached/dense storage | Loader vectors and observation include from `check-loader.py`; emit with `test/Storage.lean`, then run the storage measurement commands below | [Storage study](storage/storage-study.md) |
| Timed contracts | Cached oracle vectors, codec vectors, and general small/dense/cached oracle fixture hashes | [Timed contracts](engine/timed-components.md) |
| Decoder candidate screen | Successful current timed-contract receipt, mapped default receipt, and prepared default physical RTL | [Successor-fetch study](storage/successor-fetch-study.md) |

After loader/frontend/codec preparation, the storage fixtures required by the
current timed-contract runner can be generated with:

```sh
lake env lean --run test/Storage.lean
python3 scripts/measure-storage-variant.py cached --ff 11417
python3 scripts/measure-storage-variant.py small-dense-cached --ff 6226
python3 scripts/check-timed-contracts.py
```

These storage commands include technology mapping. They overwrite their older
run receipts; prefer a new checkout when reproducing them. The timed-contract
runner validates the frozen fixture identities in `test/timed-contracts-baseline.json`
and the unchanged default MLIR/RTL hashes. A mismatch is a failed comparison to
investigate, not a reason to replace the baseline hashes automatically.

Existing retained fixtures may also be used for a focused regression after their
hashes are checked. Label that result as a regression against frozen fixtures,
not as proof that every prerequisite was regenerated from a clean checkout.

The composed-backend gate retains old/new RTL equivalence, RTL/generic-gate
equivalence, independent storage regression, and two mapped corners under a
fresh `build/backend/<tag>/`. Run `check-backend-readback.py --tag NAME` to check
the full emitted transition and initialized traces in Lean. Pass its receipt to
`check-backend.py --readback-report PATH --tag NAME` to require exact source and
artifact identities across both gates. Both countdown and full-backend read-back
retain an explicit trusted parser/frontend boundary. See
[hardware closure](engine/hardware-closure.md) for initial-state relations and mutations.

Candidate staging and timeout/provenance regressions use disposable files and no
CAD execution:

```sh
python3 -B -m unittest discover -s test -p 'test_physical_*.py'
python3 -B -m unittest discover -s test -p 'test_backend_readback.py'
python3 -B -m unittest discover -s test -p 'test_bank_select.py'
```

Physical candidate preparation requires its manifest to be present and
byte-identical in HEAD, the Git index and the working tree before any output is
written. The current portable receipt format uses repository-relative paths
without dereferencing logical PDK symlinks; historical absolute-key receipts
remain readable in their original checkout. Clock-gate mutation checks verify
the retained model/vector inputs and generated artifacts, rerun the unmodified
netlist, and reject input changes during the check. A failing baseline cannot
count as detection of its mutants. The full `test_*.py` command above includes
these regressions in `test_physical_prepare.py` and `test_physical_receipt.py`.

The sampled and prefetch runners terminate the command's process group on
timeout, escalate to SIGKILL, reap the direct child and retain diagnostics.
Termination means no live group members remain: Linux zombies have already
terminated even while their process-table entries await reaping.
Linux checks group membership, state and thread count through `/proc`; other
hosts require group disappearance. Restricted or incompatible `/proc` views,
incomplete reads and uncertain thread state stay unconfirmed.
The runner does not adopt orphaned descendants. `test_process_group.py` checks
normal failures, graceful cleanup, TERM-ignoring descendants, zombie-only
groups and uncertain observations. Linux fixtures retain zombie descendants
until assertions finish, then reap them without relying on the container's
PID 1. `test_fit_wire_rc.py` checks route parsing
across line breaks and multiple `NEW` segments, and excludes patch rectangles
from via counts; see the [dated correction](physical-correlation-study.md#parser-correction-2026-09-19).

## Foundation review order

The [shared physical target](physical-targets.md) is the current intake for
the control and paired organization. `prepare-chip-physical.py --target PATH`
binds validated mappings, pinned macro views, typed state owners and semantic
path roles. The existing import checker verifies exact signal connections;
`--placed-macros` additionally verifies actual macro/power/corridor geometry
before cell placement, and `--check-tag` preserves failed collection receipts.
The runner requires the corresponding verified checkpoint for continuation.

Fresh diagnostics verify role endpoints in OpenDB and compare STA path presence
with mapped combinational reachability. They distinguish unused unannotated
drivers from consumed nets and reconcile clock/signal fanout classifications
with actual connectivity. `--target-bundle` supplies these checks to an older
run only when its mapping, libraries, package and SDC match the prepared target.
The standard physical pin oracle also accepts the paired selection and its
512×64 behavioral macro. Reusing an earlier pin trace requires byte-identical
exported Verilog with unchanged vectors, bench and models. See the dated study
for the matched eight-load flow overrides and bounded commands.

`check-mapped-physical.py --repair-probe PATH` independently remeasures a passed
local repair derived from the selected physical checkpoint. Admission verifies
the parent database/tag, unchanged producer inputs, stopped producer containers
and candidate database hash; the collector reads the actual repaired database
with the original target configuration. Successful collection alone does not
mean timing closure. The [paired repair](physical-targets.md#clock-and-status-repair)
requires positive measured setup/hold, passing electrical limits and complete
consumed-net estimates separately.

The local probe and independent collector each accept `--nominal-layer-rc` to
initialize explicit layer RC from the pinned technology LEF when the source
has no layer/via override. Existing overrides cannot be replaced through this
option. Reports distinguish the producer's optimization RC from independent
measurement RC. The paired repair uses nominal RC for optimization and the
retained flow configuration for measurement: explicit nominal initialization
in fresh placement STA left 308 partially unannotated drivers even on its
unchanged control. Those measurements are preserved but unqualified. Always
check actual annotation completeness; changing the RC policy is not itself a
successful measurement.

`physical_buffer_repair.compare_buffer_repair` checks complete connectivity
after contracting known noninverting buffers. Its default permits added
buffers only; explicit `allow_resizing=True` additionally permits known buffer
strength replacements with unchanged pins and parameters. Changed state,
inverters, rewiring, missing original cells and no-op repairs fail. Combined
with independent Verilog readback, exact source-export identity and unchanged
oracle inputs, this can transfer an existing zero-delay pin trace to a buffer
repair. It does not transfer timing, prove arbitrary behavioral changes, or
replace the required fresh physical geometry and timing checks.

For a target with a completed buffer-resize validation, the routing selection's
schema 3 binds that closure receipt, its reference/selected measurements and
the independently read-back netlists. `physical_route_intake.py` recomputes
buffer identity, checks unchanged geometry and source pin-oracle inputs, and
requires positive placement margins with complete wire estimates and passing
electrical checks. It carries only the exact repaired ODB and empty metrics
into one `OpenROAD.GlobalRouting` step, capped at 600 seconds with automatic
repair disabled. The [paired route](physical-targets.md#bounded-coarse-route)
then records fresh global-route qualification separately: passed intake and
completed routing do not imply positive routed timing. The existing diagnostic
schema 2 retains its explicitly unqualified-placement use case.

The [local coarse-wire repair](physical-targets.md#local-repair-with-coarse-wire-estimates)
uses `probe-physical-repair.py` to add only declared noninverting buffers, freeze
all original cells during legalization and incrementally refresh coarse wires.
`check-mapped-physical.py --repair-probe REPORT --verify-nominal-layer-rc`
independently reexports the saved candidate and checks all three corners.
Fresh Yosys readback and `compare_buffer_repair` preserve functional identity;
macro-pin geometry, all original locations, new power-terminal bindings, complete
wire annotation and exact container termination are checked separately. A nearby
replacement driver may reuse an identical coarse guide block, so changed guide
bytes are not required for every edited net. No prior congestion or pin-access
result transfers to the edited candidate.

Schema 4 now admits that candidate through `physical_added_route.py`, separately
from the resize-only contract. It binds the local measurement/producer, parent
checkpoint, independent netlist readbacks and original pin oracle; recomputes
the full resize-plus-insertion identity; and checks every original cell/location,
macro shape, corridor and new power-terminal connection. All configured corners
must have positive finite setup/hold margins, zero electrical violations, complete
coarse wire estimates and verified nominal RC. Shared PDK views and recorded
tool/library aliases remain hash-checked; candidate artifacts stay in the checkout.
The continuation carries only the exact ODB and empty metrics into one 600-second
GlobalRouting step with repair disabled. Forty-nine focused tests include bad
clock wiring, moved cells, missing power, partial RC, stale or altered inputs,
invalid timing and expanded routing-scope rejection controls.

The [whole-chip reroute](physical-targets.md#whole-chip-reroute-of-local-repair)
demonstrates why intake success is separate from final qualification: setup/hold
remain positive, but 27 signal nets violate fresh electrical limits. Its report
records setup/hold and electrical verdicts separately. Pin access and congestion
are newly measured; neither is a detailed-route or extracted-timing proof.

The [connection preparation](physical-targets.md#connection-diagnosis-and-checked-repair-plan)
adds three narrow helpers. `physical_connection_probe.py` reads saved OpenDB
pin/grid/rule information and uses the existing fresh-STA harness to collect
per-net load, library-limit and min/max path reports. It does not route or repair.
`physical_connections.py` joins those reports to exact consumers and typed state,
stopping at state, SRAM and package boundaries while retaining shared owners.
`physical_repair_plan.py` validates additive driver/receiver operations and
generates Tcl from that checked description. Historical recipes remain unchanged.

The plan binds an exact database digest, driver types, complete consumer sets,
buffer masters, row footprints, routing policy and acceptance gates. Missing
ownership/measurements, multiple drivers, clocks, stale checkpoints, dropped
consumers, colliding names, occupied rectangles and weakened gates are rejected.
Thirty-five focused tests cover the new helpers and the existing buffer/route
intake contracts. Stored NDR bindings must be compared separately from effective
router warnings; guide overlap and saved-grid overflow are diagnostic evidence.

The [saved plan](../physical/experiments/paired-signal-repair-plan.json) and
[preparation manifest](../physical/experiments/paired-repair-plan-results.json)
record **zero executed repairs and zero new routes**. Regenerate its recipe
offline with `physical_repair_plan.render_tcl(plan, context, database_sha256)`
after hashing the actual source ODB and checking the context's provenance.
Generation and a Tcl completeness check do not validate CAD execution. The
existing bounded probe can later consume the generated file. Candidate execution
must be followed by independent buffer-contracted readback, original-cell and
macro/corridor checks, legal added cells with power bindings, complete fresh RC
and positive setup/hold with zero electrical failures in all corners. Report all
affected connections, not only the originally failing nets. A passing local
result still requires fresh whole-chip route qualification.

The [executed signal-plan probe](physical-targets.md#bounded-probe-of-the-checked-signal-plan)
demonstrates these checks on the actual saved candidate. Independent readback
verifies both its buffer-only identity and every declared driver/receiver
connection; all 342 clock nets and original instances remain unchanged. A
deliberately grounded new buffer input must be rejected. The complete chain to
the original pin oracle is recomputed, including prior resizes/additions. Keep
that ancestry distinct from the immediate source-to-candidate edit in future
routing intake; a previously repaired source already contains added buffers.

All 54 changed/new nets receive library-limit and min/max path reports in every
corner, alongside the normal whole-chip STA checks. A separate read-only
OpenROAD `check_placement` verifies the saved ODB; exact row/overlap geometry and
new power-terminal bindings are also checked independently. Guide geometry is
compared as sets of rectangles because serialization can repeat rectangles
without changing their coverage. Complete fresh RC remains required. Neither a
local timing/electrical pass nor a zero incremental-grid overflow count replaces
fresh whole-chip routing, congestion and pin-access qualification.

The [signal-repair whole-chip qualification](physical-targets.md#whole-chip-qualification-of-the-signal-repair)
extends schema-4 intake to a repaired source without weakening its earlier form.
Fresh native readbacks bind the original oracle, immediate parent and candidate.
Recompute cumulative resize/insertion identity and immediate buffer-only identity
separately; require the parent export to match its independent measurement and
the immediate edit to match the executed local plan. Placement, original-cell
retention and added power bindings use that immediate edit. The current case is
242 prior additions plus 27 new ones, with 168 earlier resizes. Preserve the
old helper bytes and receipts when the intake implementation changes.

The 41-test focused gate includes corrupted ancestry with refreshed hashes,
unlinked source exports, changes to prior buffers, false local proofs and missing
power bindings. After the single route, exact export/context identity retains
functional and placement evidence. New all-corner timing/electrical, saved-grid,
pin-access and clock-rule reports independently determine physical qualification.
Collection passes while electrical and congestion qualification fail. Read-only
reports for the 15 residual nets reproduce both checkpoints' global metrics and
separate unchanged pin capacitance from changed wire capacitance. All nine exact
containers are independently absent at final reconciliation. Neither measured
load ratios nor minimum pin access establish detailed-route closure.

The [distribution contract](physical-targets.md#measured-distribution-contract)
adds family coverage and numeric experimental gates above the existing repair
generator. `physical_distribution.py` selects all branching matches for declared
typed owners and every explicit macro input, then includes neighboring buffer
and hold-chain connections. Families overlap; consumers and shared ownership
remain explicit. The inventory binds the exact saved database, and regeneration
must reproduce its scope and every connection before plan compilation.

Each covered net has per-corner limits and measured pin/wire load, including
passing members. The assessor rejects missing nets/corners or changed pin loads
between the two unchanged-netlist checkpoints. It distinguishes an actual
electrical failure from a passing connection below the trial reserve. The
contract checker requires the exact selected set, a bounded area cost, positive
per-corner setup/hold floors, and independent post-edit checks for the complete
inventory plus new branches. Checked planning does not establish those post-edit
results or admit routing. The observed wire-load ratio is descriptive only.

The additive generator accepts a validated namespace and rejects any collision
with prior buffers/nets; its default preserves earlier plan generation. The
original helper and test source are archived with their prior hashes. **54 tests**
cover this change, family completeness, low-margin passing neighbors, weakened
gates and existing connection/identity/intake contracts. Syntax checking the
generated Tcl does not execute it. The current 33-operation contract and plan
are bound by the [distribution manifest](../physical/experiments/paired-distribution-results.json).

The [local execution](physical-targets.md#local-qualification-of-the-distribution-contract)
adds `physical_distribution_acceptance.py` as a quantitative post-edit gate.
It requires exactly the original coverage plus every declared new branch in
every corner, matching measured drivers and consumer counts. Missing evidence,
duplicate coverage, nonfinite values and invalid whole-chip counts are rejected;
measured reserve, timing-floor or area failures remain explicit failed gates.
The caller separately verifies the immutable contract and candidate database,
buffer identity, tree membership, placement, original cells/clocks/hold cells,
power bindings and measurement quality. Numerical success alone admits no route.

The exact 33-buffer execution passes **61 focused tests**, fresh netlist
readbacks and a grounded-new-buffer corruption control. Complete ancestry
retains the 331,401-edge oracle through 302 cumulative buffer additions and 168
earlier resizes. Independent OpenROAD checks cover all **1,100 connections**,
with **3,300 corner records and 6,600 min/max paths**, and reproduce whole-chip
STA. All eight containers are independently absent. The
[distribution-repair manifest](../physical/experiments/paired-distribution-repair-results.json)
binds the successful local checks without rewriting the preparation receipt.
All prior source/evidence identities remain; only five existing documentation
pages change. Fresh whole-chip routing, effective clock policy, congestion,
pin access and extracted timing retain their separate gates.

The [whole-chip follow-up](physical-targets.md#whole-chip-requalification-of-the-distribution-contract)
adds `physical_distribution_route.py` to schema-4 intake. Admission reconstructs
the source and candidate inventories, reparses the raw candidate measurements,
recomputes the fixed numerical gates, and checks the exact compiled driver/
receiver edit against independent buffer identity. The existing intake still
owns original-cell geometry, clocks, power, immutable ancestry and route limits.
A receipt claiming a local distribution pass cannot bypass these checks.

`physical_congestion.py` reconciles native GRT marker categories, grid coordinates,
actual capacity/demand, named crossing nets and the flow overflow total. It
distinguishes those crossings from wider guide-rectangle overlap and rejects
missing, duplicate, mismatched or stale markers. The source/candidate negative
control demonstrates why an ODB's inherited marker bytes alone cannot establish
freshness: 21 old markers coexist with the local incremental grid's zero count.
Saved capacity and usage both include capacity reductions, so displayed 17/18
can represent actual 0/1; the pinned OpenROAD source is bound in the study.

The new admission and congestion checks bring the focused suite to **73 tests**.
One complete route passes collection, independent identity, placement and pin
access, then **fails** the unchanged distribution/timing/electrical/congestion
gates. All 1,100 connections are measured in three corners; all 66 changed/new
connections pass reserve, but complete global checks detect status setup and
SRAM read-enable failures outside that family. Hold is positive but below its
retention floors. The
[distribution-route manifest](../physical/experiments/paired-distribution-route-results.json)
records these failures separately from successful collection; it admits neither
another route nor detailed routing. All fourteen exact containers are absent,
and the prior intake-helper bytes and earlier receipts are preserved.

The [path/control follow-up](physical-targets.md#local-qualification-of-path-and-control-guards)
extends the existing repair compiler with schema 2: explicit pinned buffer
sizes and one to four serial stages per operation. The legacy schema and its
generated recipes remain byte-identical. Every stage must have a unique name,
the exact library footprint and an unoccupied row location. Signal-only
connections preserve original consumers and package ports; a declared hold
operation must terminate at a state FF's data input. Generated placement holds
original cells fixed. This is an additive physical transform with no new state.

The exact-edit checker verifies every intermediate branch, driver/receiver
connection and buffer cell, alongside the existing independent functional,
geometry and power checks. The quantitative checker requires every old and
new branch in every corner. A missing second stage, altered shared consumer,
clock edit, overlapping footprint, unsupported cell, weak branch reserve or
grounded hold-stage input is rejected by tests or the actual-netlist negative
control. **74 focused tests** pass, including legacy plan and intake checks.

The study retains all original distribution families and adds nineteen declared
status, input-hold and SRAM-control/address connections. Source roles must
survive insertion: classifying only the immediate sink would mislabel an input
guard once a buffer replaces its direct FF sink. An independent metadata check
carries the seven input-hold roles through fourteen new stages while retaining
the original collection and unchanged measurement selectors. The resulting
**1,145 connections / 3,435 corner records / 6,870 min/max paths** pass the local
budgets and reproduce global STA. The area reference remains the original
**358,297.5456 µm²**, with cumulative added area checked against 0.3%; the 20%
reserve and all timing floors remain fixed. New source versions, archived prior
helper bytes and exact recipe/database hashes are bound in the
[path-repair manifest](../physical/experiments/paired-path-repair-results.json).

All ten exact containers are independently absent. Fresh readbacks and buffer
contraction transfer the 331,401-edge oracle through 328 additions and 168 prior
resizes. No new whole-chip route occurs. Before another route, shared admission
must reconstruct this expanded scope and stage-aware edit, reparse raw evidence
and preserve the original cumulative budgets. The current local pass alone
does not perform or bypass that intake. Fresh congestion, effective clock rules,
pin access, extracted timing and physical power continuity remain separate.

The [whole-chip path/control follow-up](physical-targets.md#whole-chip-requalification-of-path-and-control-guards)
implements that admission in `scripts/physical_path_contract.py`, reached through
the existing added-buffer route intake. Source declarations are reconstructed
from exact connectivity. The complete macro-input census rejects missing dynamic
controls, false static labels and omitted clock/static pins. Declared path roles
propagate through every serial stage even where a distribution-family label
already exists. Fresh exact-edit and raw-measurement checks retain the original
area reference, reserve and timing floors. New mutation tests bring the focused
suite to **90 passing tests**; legacy admission remains covered.

One admitted coarse route retains all six setup/hold floors and reserve on all
45 changed/new connections. Fresh checks cover **1,145 connections / 3,435 corner
records / 6,870 min/max paths**, with complete nominal consumed-wire annotation.
The checker correctly rejects full qualification: four connections miss reserve,
two fail capacitance, and nine slow slew pins share one of those two nets.
All global electrical failures are covered. Identity, placement, power bindings
and minimum pin access pass; no extra simulation repeats the retained
331,401-edge oracle. All eleven exact containers are independently absent.

Congestion validation also fails closed. The final flow reports 22 overflow
units and native JSON has 22 markers, but the saved grid supports only 21.
The complete shared reconciliation raises an error; the diagnostic artifact
separately labels the matching subset and the unmatched horizontal marker.
It neither waives the remaining marker nor invents its layer from the flow's
Metal4 aggregate. Runtime clock-rule relaxations are recorded separately from
unchanged stored bindings. The
[path-route manifest](../physical/experiments/paired-path-route-results.json)
distinguishes successful collection/timing retention from failed electrical,
reserve and congestion qualification. Detailed routing and extraction remain
unadmitted. Earlier receipts and the archived prior intake helper are preserved.

The [organization-policy screen](physical-targets.md#physical-organization-policy-and-saved-chip-screen)
reuses those settled artifacts without CAD. `check-physical-organization.py`
verifies source, database, netlist and pinned-library identities; reconstructs
all 211 distribution trees; and retains the complete 1,145-connection path
contract. The four affected trees contain 64 branches. Independent Liberty
pin-capacitance calculations match **192 saved STA corner records**, including
common-edge aggregation for mixed receiver types. Shared trunks, upstream
resize loads and cumulative area are counted once. Candidate footprint checks
identify exact occupied cells but do not stand in for legalization or power
and pin-access checks.

Seventeen new organization tests bring the focused suite to **107 passing
tests**. They reject changed endpoints/checkpoints, missing or repeated tree
membership, a forged electrical source, dropped/duplicated or protected
consumers, stale pin loads, inconsistent areas, cross-candidate footprint
collisions and over-budget combinations. Virtual scalar-input exchanges are
applied only to in-memory copies of the independently saved Yosys readback;
whole-circuit buffer contraction confirms identity and a wrong-source mutation
is rejected. Actual physical regrouping still requires fresh independent
readback and exact-edit validation. No existing edit compiler or route-admission
rule is extended to accept these candidates.

The **7.330 s** screen produces eighteen costed choices and no complete portfolio
under the current placement rules. Its successful status means the comparison
completed; every candidate keeps execution/electrical/timing qualification
false. The original 20% reserve, timing floors and 0.3% cumulative area budget
remain. The unresolved congestion-marker discrepancy is excluded from ranking.
The [organization manifest](../physical/experiments/paired-organization-results.json)
records the final screen, tests, earlier rejected screen and source preservation.

The [local organization follow-up](physical-targets.md#local-qualification-of-the-organization-policy)
extends that policy with one named buffer's bounded same-row move and weak-branch
grouping. Pinned LEF dimensions/site geometry reproduce both source pin locations;
every incident signal enters the screen. Three further tests bring the focused
suite to **110**. Six independent preflight mutations reject altered source,
protected resize, invalid displacement/footprint, duplicate consumer, occupied
receiver net and false area. A virtual combined plan preserves full bufferless
connectivity before one bounded local probe is allowed.

`physical_organization_repair.py` separately compiles the exact edit and verifies
fresh physical/Yosys readbacks. It compares every net and original instance,
including unchanged clock and power bindings, both allowed resizes, the one
permitted translated cell and the exact receiver footprint. A grounded receiver
and a wrong physical displacement are rejected after fresh readback. The complete
inherited path inventory is reconstructed from its original declarations and
stage roles; one receiver branch expands **1,145 → 1,146** connections.

All **3,438 corner records / 6,876 min/max paths** pass the original numerical
budgets. The derived [contract](../physical/experiments/paired-locality-contract.json)
advances source identity and edit selectors while retaining the original area
reference, timing floors, scope and 20% reserve. No numerical threshold is reset.
Fresh global STA, actual guide changes, placement and minimum pin access agree;
all nine exact containers are independently absent. The 331,401-edge oracle is
transferred through fresh complete-netlist identity rather than resimulated.
The [manifest](../physical/experiments/paired-locality-results.json) binds the
screen, exact plan, local probe and independent checks.

The [shared edit follow-up](physical-targets.md#shared-physical-edits-and-whole-chip-requalification)
now adds independent schema-5 admission for this candidate. The four-operation
checker is separate from search and the historical recipe builder. Different
operation counts are tested; both sides of changed buffers enter coverage.
Admission reconstructs the exact edit, complete functional ancestry, original
role declarations, raw connection records, full timing, area reference and pin
access. The older add-only path cannot accept an organization receipt, and its
unchanged-cell guard remains. Eleven new tests bring the focused suite to **121**;
six actual receipt mutations with internally updated hashes are also rejected.

The single admitted GlobalRouting step completes under **600 s / four CPUs /
6 GiB**, with no further physical repair. Fresh whole-chip checks reject the
result: **1,142 / 1,146** connections retain 20% reserve, three fail and one is
below reserve; independent global STA finds a fourth failing net outside that
inventory. Slow setup is **−0.055813 ns** and fast hold **+0.064551 ns**, below
their original retained floors. The six original repair targets still pass.
All **33** new native congestion markers reconcile with flow and saved-grid
overflow. Exact identity, placement/power, area, complete consumed-net annotation
and minimum pin access pass; ten containers are absent. The
[manifest](../physical/experiments/paired-locality-route-results.json) distinguishes
successful evidence collection from failed physical qualification.

Saved matched hold paths isolate unchanged data delivery and **39.834 ps** later
capture-clock arrival. Setup's worst path changes, and the older top-1,000 report
does not contain the same new mode-to-status path. The
[matched follow-up](physical-targets.md#matched-clock-control-and-capacity-diagnosis)
now closes that measurement gap: four exact paths across both chips and all
three corners require the same pin, transition and cell sequences. Mode/status
loses **2.318466 ns**, split into **2.299226 ns data / 0.019240 ns launch clock**;
SRAM/status loses **0.307090 ns**, split into **0.101463 ns data / 0.205627 ns
launch clock**. Input hold loses margin through later capture clock; a matched
self-hold path retains its margin. A changed worst-path source is not used as a
substitute for these matched comparisons.

The read-only collector measures all **118 connections** in five complete
transport trees, including six previously uncovered control branches. All pin
loads and geometry are unchanged; before/after reserve counts are **118 passing**
versus **113 passing / four failing / one below reserve**. Fresh global timing
and electrical counts reproduce the saved values and consumed-net annotation is
complete. The **33** native edges reconcile again; the families cross 21,
ordinary clocks cross nine, and none directly contains an NDR-bound net.
Four negative controls reject changed transitions, missing/ambiguous paths and
a mismatched grid. Six collector and two source-route containers are absent.

The [manifest](../physical/experiments/paired-coupling-results.json) binds a measured
watchlist proposing the inherited scope plus six control branches (**1,152**),
four exact paths and thirteen clock nets. It does not alter production admission
or authorize repair. Pinned source inspection distinguishes stored rules from
runtime softening without claiming a causal policy experiment. No production
source changes, new route, physical edit or new pin simulation occurs. Local
success does not establish extracted timing, detailed routability or physical
power-grid continuity.

For the current hybrid fetch investigation, use the functional/mapping gate
with `--organization combined --fanout-limit 8`, then the retained-netlist timing
gate described in the [fetch contract study](fetch-contract-study.md). The saved
flat-repair comparison remains a cost probe. Timing requires the pinned local
Docker image and uses no network, synthesis, placement or routing. Each STA
command has a 120 s cap, two CPUs and 2 GiB RAM;
the runner confirms container termination. Choose fresh tags:

```sh
python3 -B scripts/check-sram-timing.py --retained physical/experiments/combined-chip-results.json --tag NAME
python3 -B scripts/check-sram-timing.py --retained physical/experiments/local-load-results.json --tag LOCAL_NAME
python3 -B scripts/check-electrical-distribution.py --comparison physical/experiments/combined-chip-results.json --timing build/storage/sram-timing/NAME/report.json --tag REPAIR_NAME
python3 -B -m unittest discover -s test -p 'test_sram_timing.py'
python3 -B -m unittest discover -s test -p 'test_map_distribution.py'
```

The retained mode checks immutable artifact identities, not equality with every
current Lean source: later proof-only additions do not invalidate a saved
netlist's timing. Hardware changes still require a new functional/mapped
comparison. The distribution probe includes complete-controller SAT and a
negative buffer control. A passed diagnostic may contain timing violations;
it must not be advertised as physical closure. `FetchContract` is included in
the foundation regression, and its proofs in the standard-axiom audit.

The [mapped physical comparison](chip-physical-study.md#exact-mapping-placement-and-hold-repair--september-22)
uses `prepare-chip-physical.py --mapped-role baseline|tiled` with the selected
load-budget receipt. This opt-in path stages exact mapped Verilog/JSON and an
initial checkpoint, then starts after synthesis. `check-mapped-import.py`
compares every original cell/pin connection in a fresh floorplan ODB export and
the saved netlist before the runner admits placement. The mapped-input tests
reject clock/address/constant/logic rewiring, changed receipts and unchecked
continuations:

```sh
python3 -B -m unittest discover -s test -p 'test_mapped_physical.py'
python3 -B -m unittest discover -s test -p 'test_chip_physical_prepare.py'
```

For a settled mapped physical run, `check-chip-physical.py --mapped-export PATH`
accepts a verified fresh ODB export receipt and the selected mapping via
`--comparison`. It verifies database/export identities, reuses the original
independent vectors and requires a compiled public-output mutation to fail.
The old netlist-view mode remains available and retains its inherited-view
limitation. Fresh physical STA must clear inherited state metrics, identify
placement versus coarse-route RC, and confirm propagated clocks at each
corner. Compare the same physical stage; do not compare a timed-out baseline's
placement estimates with a candidate's coarse-route estimates as a matched
timing result. Diagnostic success is distinct from zero reported violations.

Use the shared checkpoint collector for that physical measurement. It verifies
that the run is settled, selects a completed checkpoint, exports its actual ODB,
checks the corridor and invokes fresh per-corner STA in the pinned image:

```sh
python3 -B scripts/check-mapped-physical.py --physical-tag RUN --tag FRESH_NAME
python3 -B scripts/check-mapped-physical.py --physical-tag RUN --tag FRESH_STAGE \
  --step 26-openroad-globalrouting
python3 -B -m unittest discover -s test -p 'test_mapped_physical_diagnostics.py'
```

The default is the final completed checkpoint; `--step` must name a completed
directory in that same run. Changed final states/databases, incomplete steps,
unpropagated clocks and ambiguous RC modes are rejected. The worker
`physical_checkpoint_sta.py` runs inside the pinned image with only the selected
ODB as its input state. Diagnostic commands each have a 120 s cap, two CPUs and
2 GiB, with read-only design/PDK mounts and independent container termination
checks. They do not run placement or routing. `--mapped-export` in the pin oracle
gate still requires the final reported ODB, even if earlier checkpoints have
also been measured.

For repair experiments, compare before/after netlist and placement identities
alongside timing. The [clock/SRAM result](chip-physical-study.md#clock-budget-and-post-routing-repair--september-22)
shows that a reported repair counter can coexist with unchanged cells and
connections. Its annotation audit also accounts for unused ports/dummy outputs
without treating consumed unannotated nets as measured timing.

The [local repair study](chip-physical-study.md#local-clock-and-sram-repair--september-22)
adds `physical_buffer_repair.compare_buffer_repair` for independently read-back
netlists. It requires every original cell and parameter to remain, allows only
added pinned noninverting buffers, rejects shorts, floating inputs and buffer
cycles, and compares every retained signal connection after buffer contraction.
Existing CTS dummy cells may omit their unused outputs, but their inputs must
still resolve. This structural check complements the independent external-pin
oracle; it establishes neither analog timing nor physical closure.

Before trusting repair, verify that the optimizer's layer RC is initialized,
then confirm actual changed cell/pin identities. Legalize new cells, audit
original geometry and the reserved corridor, and remeasure both original and
candidate with the same RC mode and empty inherited timing metrics. The retained
local recipe uses global-route geometry to choose SRAM buffer insertion, then
explicitly switches all comparison measurements to placement RC. Old routing
guides cannot serve as fresh routed evidence for changed nets. The experiment
passes these local checks; the subsequent
[coarse-route comparison](chip-physical-study.md#coarse-routing-the-local-repair--september-22)
clears all seven targeted SRAM output capacitance failures while retaining
other electrical and congestion failures.

For this selected repair, `run-physical.py --repair-selection` consumes the
frozen local-repair receipts. `physical_route_intake.py` admits only an
ODB-only state with empty metrics, the same prepared design/PDK, and exactly
one `OpenROAD.GlobalRouting` step capped at 600 s. It rejects stale ODB/export/
oracle identities, a new CTS pass, later stages, changed constraints and custom
RC replacement. Explicit layer values come from the pinned nominal technology
LEF in kohm/pF/µm. This gate is scoped to the local-repair receipt schema.

The [data-buffer follow-up](chip-physical-study.md#local-data-buffering-and-complete-wire-estimates--september-22)
adds a schema-2 **diagnostic** admission. Independent buffer-contracted
connectivity, preserved clocks/geometry, exact ODB/export identity and the pin
oracle are required. It explicitly marks placement timing as unqualified and
permits one bounded GlobalRouting step to obtain complete wire estimates, with
all repair stages disabled and the preceding route's controls unchanged. It
cannot authorize CTS, detailed routing, altered RC or inherited timing metrics.

Check `report_parasitic_annotation -report_unannotated` before using any timing
result: reject partial or consumed unannotated nets; individually account for
unused ports and unconnected dummy outputs. A reported RC mode and positive
slack alone are insufficient. In this study, placement-only estimation leaves
513/524 partial annotations on control/candidate; the subsequent fresh coarse
route has zero partial annotations. Preserve the failed timing receipt and
its useful independent structural evidence separately. A collector's `passed`
status means the measurement completed, not that its timing is qualified.

`probe-physical-repair.py` runs one local Tcl recipe against the final completed
checkpoint of a settled, reported physical run. Its 120 s/two-CPU/2 GiB container
has read-only source/PDK mounts, explicit nominal RC verification, copied
execution inputs and termination receipts. The selected recipe
`physical/experiments/local-data-buffer-repair.tcl` is tied to `local-route-01`'s
29 target nets; it is not a general repair policy for arbitrary netlists.
Probe success requires separate connectivity, geometry and timing validation.

The [electrical-cost diagnosis](chip-physical-study.md#electrical-cost-and-sram-interface-geometry--september-22)
demonstrates the failure boundary: its last repair progress line reports seven
buffers, but OpenROAD exits with `GRT-0183` before saving the edited ODB. No
candidate or functional improvement is accepted. Preserve the error, cap,
pre-edit export, unchanged source hashes and independent container termination;
classify it separately from a timeout or completed repair.

Saved GCell capacity/usage can localize congestion cheaply. Bind the arrays to
the exact database and compare their grid and capacity identities before
interpreting usage changes. Report their sum separately from the flow's final
overflow when the two differ. Assigning cell centers to macro rectangles and
counting guide overlaps are spatial screens; neither establishes detailed-track
accessibility or attributes a DRC failure to a particular connection. The pinned
OpenROAD exporter stores reductions in both capacity and usage: equal stored
capacity arrays alone do not prove equal remaining capacity or blockage effects.

`scripts/sram_interface.py` binds `--context`, `--geometry`, `--guides` and
`--grid` to completed `--guide-receipt` and `--geometry-receipt` inputs, and
requires a new `--output` file. It classifies traffic through known buffer/delay
cells, checks rectangular pin escapes, and includes all incident signal/clock
connections in fixed-neighbor mirror projections. Ten focused controls run with
`python3 -B -m unittest discover -s test -p test_sram_interface.py`.
The [interface receipt](../physical/experiments/sram-interface-results.json)
retains the exact extraction worker and invocation; the screen does not replace
legal access generation or foundry DRC.

`python3 -B scripts/upload_locality.py --source physical/experiments/sram-interface-results.json --windows FILE.json --output NEW.json`
checks those settled inputs, follows directed buffer/delay paths to every leaf,
binds the stage's 71 FFs and actual D-driver cells to the saved mapping, and
screens free row intervals and complete affected payload nets. Windows are DBU
rectangles; the recorded study uses two disjoint pin-face bands. The 13 focused
controls run with `python3 -B -m unittest discover -s test -p test_upload_locality.py`.
The [locality receipt](../physical/experiments/upload-locality-results.json) also
preserves the relaxed FF-allocation worker and its 48 exhaustive small-case
comparisons plus primal/dual optimality checks. That certifies the assignment
model, not physical placement: logic, clock/hold repair and possible center
overlap must remain explicit. A negative screen does not require resynthesis
or another functional simulation when circuit and oracle inputs are unchanged.

`python3 -B scripts/check-compact-execution.py --tag NEW_COMPACT_STUDY` runs the
[bounded compact-model gate](storage/compact-execution-study.md): independent E64 and
wire-formula tests, two conditional Lean schedule lemmas, four behavioral
mutants, a compiled-environment axiom audit and its negative control. It retains
images, capacity/operation counterexamples, source hashes and prior receipt
identities. Standalone tests need no physical fixtures. The complete gate needs
the retained architecture, word-region and local-slew receipt files, but runs
no CAD tools, synthesis, RTL emission or containers. It establishes model
evidence; the candidate is rejected before implementation.

`python3 -B scripts/word_region.py --inputs build/validation/word-region-01/inputs-final.json --output NEW.json`
replays the hash-bound received-frame census and three bounded site-exchange
screens. It reconciles fresh physical readback, binds all FFs to retained typed
state, stops private ownership at mixed-state consumers and charges all incident
nets of displaced cells. Fourteen rejection/accounting controls run with
`python3 -B -m unittest discover -s test -p test_word_region.py -v`.
The [word-region receipt](../physical/experiments/word-region-results.json)
also binds an independent complete-chip span, footprint and clock-pin audit.
No CAD process is launched by the replay. Unchanged hold cells do not imply
unchanged hold-wire delay; guide overlap and HPWL do not replace routed timing.

The upload-stage oracle includes one-cycle programs, distinct contents in the
opposite bank, immediate start after each dictionary push and cancellation.
It must reject an unconditional pending-write mutant for a state mismatch;
compilation failure is not sufficient. Earlier weak mutation fixtures are
retained as failed attempts. The final validation reuses the 508,252-edge pin
trace only after current complete-chip RTL, models, oracle and tools match its
positive evidence, while rerunning the strengthened core/mutation gate. Local
queue proofs and finite RTL traces do not establish a composed chip refinement.

The collector's `--pins FILE.json` adds per-net load reports for literal pin
names. `--verify-nominal-layer-rc` independently compares OpenROAD's actual
per-layer R/C with its technology LEF for every fresh corner; it fails on a
missing or different table. These flags do not initialize or repair the design.
Keep the run's executed worker copy as part of the immutable receipt.

After a route that changes no cells, compare the freshly exported netlist bytes
and full cell/terminal/placement context with the validated candidate. If the
netlist and the oracle's model/vector inputs are identical, bind the existing
external-pin trace by hash instead of repeating simulation. The local-route
study uses this rule for 508,252 edges and one rejected corruption. This reuse
establishes only the same zero-delay functional evidence; fresh wire/clock
measurements remain necessary, and neither result is extracted timing.

For physical-only diagnosis, use the [cheap routing checks](routing-diagnostics.md)
before repeating routing search. They validate exact snapshot/report identities,
resolve truncated logs, compare fresh DRC and saved geometry, and require resolved
routing limits and matching timing stages. They do not replace the affected
functional checks, foundry DRC, antenna checks or extracted timing.

1. **Protocol semantics and compilers:** exact pin edges, capture order, bounded
   protocol scope, and compiler theorem hypotheses.
2. **Machine and storage:** reset/start priorities, atomic image replacement,
   capacity rejection, cache invariants, and exact-edge refinement.
3. **Translation and independent checks:** structural expressions, emitter wiring,
   malformed input coverage, defined-output comparisons, and detected mutations.
4. **Measurements and research records:** baseline identities, fixed constraints,
   default versus experimental backends, and remaining physical limitations.

Preserve historical experiment identities when integrating new work. The hardware
closure and optimization studies record their own artifact-specific evidence;
new physical timing closure or default promotion is not a prerequisite for
merging those functional proofs and experimental variants.


## Timing and communication organization study

The [organization study](physical/physical-organization-study.md) reuses the matched
saved-chip diagnosis through `report-physical-organization.py`. It verifies
source/report/database/library identities, checks all 1,152 inherited/watchlist
endpoints, reconciles 354 net/corner input loads and recomputes family budgets
from the raw connection reports. Conditional timing obligations retain exact
path and clock identities; a shared launch/capture endpoint cancels a common
clock shift. Opposite checks and unmeasured physical effects stay explicit.

```sh
python3 -B scripts/report-physical-organization.py \
  --study physical/experiments/paired-organization-study.json \
  --check-tag organization-comparison-next
python3 -B -m unittest discover -s test -p 'test_physical_organization*.py' -v
```

The selected saved-chip comparison takes 4.112 seconds with no CAD commands.
The focused suite has 42 passes, including eleven new helper cases. Four
integration controls reject a changed diagnosis hash, missing path role, added
pipeline cycle and attempted state replication. The full exchange portfolio
preserves virtual buffer-contracted identity for twenty rewired scalar inputs,
but has no complete conditional wire-budget pass. Local decoder-copy costs
include their additional upstream pin load; two parents reuse full-inventory
raw measurements and two remain missing. No production admission or numerical
budget changes. The [manifest](../physical/experiments/paired-organization-study-results.json)
binds the source study, selected report and test receipts. Fresh tags preserve
prior attempts; the helper tests are portable, while replaying the study needs
its bound local physical artifacts and libraries.
