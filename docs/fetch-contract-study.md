# Fetch deadlines and electrical cost

Applying the library load budget during mapping produces a better candidate
than repairing the completed flat netlist. The chip now meets fanout eight at
290,943.9540 µm² of standard cells, 0.559196% below the original hybrid, with
slow **cell-only setup** slack of +10.52 ns and hold of −0.86 ns. The
[physical follow-up](chip-physical-study.md#exact-mapping-placement-and-hold-repair--september-22)
now preserves that mapping through placement, clock and hold repair. It retains
a 2.52% placed-area advantage, but coarse wires reopen two upload hold violations
and expose clock/SRAM electrical failures. Neither stage establishes final fit.
The [clock-budget follow-up](chip-physical-study.md#clock-budget-and-post-routing-repair--september-22)
clears the measured hold failures at a further 9,925 µm² cost. It leaves four
upper clock fanout failures and SRAM electrical problems; the generic repair
stages change no cells or placements. Subsequent local repairs and the
[SRAM interface study](chip-physical-study.md#sram-interface-geometry-and-upload-staging--september-22)
now identify upload distribution as an organization target and cost an
experimental upload stage; the original execution loop remains unchanged.
The [local-load receipt](../physical/experiments/local-load-results.json) records
this follow-up. The earlier semantic and timing diagnosis below explains why
the SRAM return path, actual load budgets and minimum delays guide the work.

The [selected receipt](../physical/experiments/fetch-contract-results.json)
links the immutable timing, distribution and validation reports. The
[tile study](map-tile-study.md) owns the earlier mappings;
[research status](research/status.md) owns the next allocation.

## Availability and deadlines in the existing loop

Use `SramAssembly` for actual computations/state owners and `SramSchedule` for
edge obligations. Let edge E produce the current state and SRAM Q, which are
available after their clock-to-output delays. The logic between E and E+1
must determine both the state captured at E+1 and that edge's SRAM requests.
The pin sampler's existing latency is upstream of this interface; it is not
another cycle available to the fetch loop.

| Operation at E+1 | Available before E+1 | Required by E+1 | Existing digital evidence |
| --- | --- | --- | --- |
| Running without dispatch | Cached record, PC/mode and both candidate responses | Retain current execution; renew candidate requests | `candidates_ready`, `candidates_after_edge`, `running_reads` |
| Dispatch, including a one-cycle branch | Current terminal-capture fields, old samples, sampled input and both candidate SRAM words | Select the word being entered, update execution, compute that word's two candidate PCs and look up their indices | `Fetch.address_choice`, `Dispatch.candidate_correct`, `candidates_after_edge` |
| Commit | Admitted complete inactive image and its index-zero entry | Switch bank and issue the word-zero read; mark its response pending | `commit_pending`, `response_edge`, `request_on_read` |
| Immediate start after commit | Q0 from the commit edge and pending flag | Enter that start word and issue its following candidate reads | `commit_bypass`, `start_ready` |
| Later restart | Saved start word | Enter word zero without relying on Q left by unrelated writes | `commit_saved`, `start_ready` |
| Dictionary upload, reference assembly | Accepted command, inactive bank, cursor and payload | Broadcast one write to both replicas, holding Q | `one_access`, `broadcast_write`, `active_bank_untouched` |

The current record's two candidate addresses are independent of the incoming
sample. **The addresses required for the following edge can depend on it**:
the capture chooses which word is entered, and that word determines the next
two candidates. Consecutive one-cycle branches leave no spare edge for an
unaccounted pipeline register. Existing proofs renew availability every edge;
`test/FetchChoice.lean` exercises 128 such branches and detects stale selection
on 63 edges.

The [experimental upload pipeline](#experimental-upload-pipeline--september-22)
spends idle upload time while preserving running/start reads. It changes the
physical write edge; the reference schedule in this table remains the baseline.

Digital availability is only one half of the contract. Setup constrains the
latest arrival; hold constrains the earliest. For a same-clock path, the
approximate inequalities are

```
clock_to_Q_max + path_max + setup + uncertainty <= period
clock_to_Q_min + path_min >= hold + uncertainty
```

Actual STA uses the characterized, signed library arcs, transition/load
dependence and I/O constraints. Geometry adds wire resistance/capacitance,
clock skew, buffering, legal placement and routing capacity. None of those
physical quantities follows from a Lean-level operation count.

## What the dependency proofs establish

`Reactive.captureRead_correct` proves, for arbitrary
inputs and register bits, the read-after-capture identity

```
read(updated_samples, branch_slot)
  = if capture_enabled && capture_destination == branch_slot
    then incoming[capture_input]
    else read(old_samples, branch_slot)
```

`Fetch.forwardedBranchExpr_eq` connects this alternative expression to the
existing branch expression. The alternative is available for experimentation;
the scheduler and SRAM emitters still use their original definitions.
`test/FetchContract.lean` enters two valid programs from rest. They differ only
in bit 35, and take different branches on the same edge with identical incoming
pins. It also checks the next candidate address. This is a real semantic
dependency, not permission to discard a long path.

`Storage.FetchContract.entered_metadata` proves that the entered-word candidate
calculation uses only kind (3 bits), finish (2), yes (8) and no (8). The other
43 bits are outside that address calculation, although execution still uses
and validates them. `checked_or_sequential` proves that a valid non-checked
record has zero finish; `entered_valid` then reduces this calculation to the
18 finish/target bits under an explicit valid-word premise.

This restricted result is useful when designing an earlier metadata boundary.
It is **not** arbitrary-state equivalence of a simplified controller. Invalid
uploads, faults, reset/idle behavior and speculative macro requests still need
their existing behavior or an explicitly proved observational contract.
Multi-bit transitions can also sensitize timing paths even when stable valid
values have a restricted dependence. No false paths or multicycle exceptions
were added. All new proofs pass the standard-axiom audit; the initial native
SAT proof was replaced by kernel-checked mask and case reasoning.

## Retained complete-chip timing

`scripts/check-sram-timing.py --retained` checks the selected mapping receipts,
Verilog/JSON hashes, complete-chip metrics, standard-cell and SRAM libraries,
and the pinned local OpenSTA image. It performs no synthesis, network access,
placement or routing. Each container has read-only inputs, two CPU cores,
2 GiB RAM and a 120 s cap; termination is checked independently.

All runs use a 20 ns ideal clock, 0.2 ns uncertainty, 0.15 ns clock transition,
4 ns maximum and 0.2 ns minimum I/O delays, a `sg13cmos5l_buf_2` input driver
and 0.010 pF output loads. Pin loading and SRAM clock-to-Q/setup/hold arcs are
included; wire parasitics and a clock tree are absent. A completed diagnostic
can report negative slack: `status: passed` means the measurement completed,
not that timing closed.

| Mapping | Typical setup slack, ns | Slow setup slack, ns | Typical / slow hold slack, ns | Fanout violations, each corner |
| --- | ---: | ---: | ---: | ---: |
| Original hybrid | +13.55 | +10.26 | −0.58 / −0.86 | 1,300 |
| Separate controller/tiles | +13.77 | +10.03 | −0.56 / −0.83 | 687 |
| Combined controller/selection | +13.50 | +10.11 | −0.54 / −0.81 | 685 |

No max-slew, max-capacitance, min-pulse-width or min-period violations were
reported under these assumptions. The slow-corner worst setup path in all
three chips is SRAM Q → controller/selection → map → SRAM address. The
cached-word-to-address slack is +12.58, +12.61 and +12.41 ns respectively.
In the combined path, `memory.storage0/A_DOUT[1]` arrives at 5.21 ns, and
`memory.storage1/A_ADDR[3]` at 10.27 ns. Two heavily loaded map buffers alone
contribute about 1.18 ns. These are rounded path samples, not a physical limit
or a proof that the path is sensitized in every execution.

Worst hold paths run directly from upload-data registers to SRAM `A_DIN`.
For the combined slow sample, data arrives at 0.37 ns while the requirement
is 1.18 ns, including uncertainty. Slowing the clock does not resolve this
same-edge minimum-delay requirement. Wire/clock effects and deliberate hold
repair must be measured at the physical stage; suppressing the check would
hide an interface obligation.

The selected six-run report is `build/storage/sram-timing/fetch-contract-03`:
5.087 s total, with the same numeric results as the first successful 3.983 s
run. An earlier attempt stopped at a pin-name validation error: Yosys had
renamed private cells in Verilog. The final checker resolves actual saved
Verilog Q drivers and verifies their positions against the JSON state map.
The failed attempt and its confirmed container cleanup remain preserved.

## One controlled distribution change

The old structural budget of ten came from the original mapping's observed
fanout. The pinned library instead declares `default_max_fanout: 8` and unit
fanout loads. `scripts/check-electrical-distribution.py` tests this distinction
on the exact combined mapping, inserting noninverting buffers with a separate
namespace. It preserves all state, original logic functions, clock connections
and SRAM terminals; it adds no execution cycle. This flat repair has no
placement or locality model.

| Combined chip | Before | Fanout-eight probe |
| --- | ---: | ---: |
| Added repair buffers | 0 | 1,369 |
| Standard-cell area, µm² | 289,427.1156 | 299,362.7700 |
| Maximum signal sink count | 10 | 8 |
| Address gate depths | 30 / 29 | 37 / 36 |
| Slow setup slack, ns | +10.11 | +10.13 |
| Slow hold slack, ns | −0.81 | −0.86 |
| Fanout violations | 685 | 0 |

The two-corner probe completes in 15.094 s, with a longest command of 4.041 s.
Mapped Verilog read-back agrees with its JSON metrics. Two complete-controller
SAT checks establish arbitrary-state output/next-state equivalence; an inverted
inserted buffer is rejected. Both corners report zero electrical violations
in the categories above, but hold remains unresolved. All containers are absent.

The 9,935.6544 µm² repair increases standard-cell area by 3.432869%, making this
chip 2.318244% larger than the original hybrid. Do not adopt it wholesale.
Its seven extra gate levels barely change setup, illustrating why a strict
depth reduction must not be required before spending a few seconds on STA.
The experiment provides a measured repair cost for this particular mapping,
not a lower bound on the cost of every legal implementation.

## Local mapping with the library budget — September 22

The pinned ABC `buffer` command defaults to maximum fanout ten. An isolated
tile comparison changes that limit to eight while preserving the constrained
mapping recipe, logic, 80 state bits and both readers. Each corner adds nine
buffers: tile area grows 7,664.0256→7,729.3440 µm², and read depth grows 4→5.
Its write-data input load falls seven→two pins. All four control/candidate
checks against the independent arbitrary-state tile oracle pass in 1.218 s.

`check-tiled-chip.py --organization combined --fanout-limit 8` applies this
recipe inside the tiles and surrounding logic, then accounts for every
controller, tile and fixed SRAM consumer at the same eight-load budget.
The historical default of ten remains reproducible. The new option requires
the complete combined boundary and checks that the pinned library has unit
loads and a uniform limit of eight. Baseline mapping remains unchanged.

Across 32 tiles, local mapping adds 288 buffers. Mapping the surrounding logic
adds 50, while shared distribution needs 225 buffers instead of 354. The net
increase over the earlier combined chip is **209 buffers**; every nonbuffer
cell count is unchanged. This costs 1,516.8384 µm², versus 9,935.6544 µm² for
the flat repair. The input interface's lower load makes its composition cheaper.
Logical hierarchy still imposes no physical placement constraint.

| Complete chip | Standard-cell area, µm² | Slow setup slack, ns | Slow hold slack, ns | Fanout violations |
| --- | ---: | ---: | ---: | ---: |
| Original hybrid | 292,580.0514 | +10.26 | −0.86 | 1,300 |
| Earlier combined mapping | 289,427.1156 | +10.11 | −0.81 | 685 |
| Flat fanout repair | 299,362.7700 | +10.13 | −0.86 | 0 |
| Local eight-load mapping | **290,943.9540** | **+10.52** | **−0.86** | **0** |

Both corners have 2,895 FFs, two unchanged SRAMs (100,978.2656 µm²), and maximum
signal sink count eight. Address depths become 31/29; next-state depth is 25
typical and 26 slow. Typical setup/hold slack is +13.50/−0.58 ns. Both corners
report zero fanout, slew, capacitance, pulse-width and period violations under
the same cell/SRAM-only assumptions above. Slow cached-word-to-address slack
is +13.48 ns; the limiting setup path still starts at SRAM Q. The worst hold
path remains an upload-data register directly driving SRAM `A_DIN`.

The complete functional/mapping gate takes 252.468 s, with a longest command of
67.035 s against the 180 s cap. Four complete-controller SAT checks and two
rejected mutations pass, followed by 1,536,596 independent core/package-pin
edges at RTL and mapped corners. Lean sources, original/tiled emissions and
state projections stay unchanged; the standard-axiom audit passes. Thirty-two
focused Python tests cover the existing checks and reject mismatched library
budgets or an incomplete organization. The six-run STA comparison takes
5.125 s, reproduces both retained controls exactly, and independently confirms
all six containers absent. No routing was run.

Reproduce with fresh tags:

```sh
python3 -B scripts/check-tiled-chip.py --organization combined --fanout-limit 8 --tag NAME
python3 -B scripts/check-sram-timing.py --retained physical/experiments/local-load-results.json --tag TIMING_NAME
```

The second command times the selected immutable mapping. To time a fresh first
command's result, supply a new selection JSON with `report` and `report_sha256`
pointing to its completed report. Preserve the existing selection and receipts.

## Decision and next discriminator

Adopt the edge/dependence/Liberty checks as the cheap gate. Keep semantic
ownership, synthesis boundaries and physical regions independently selectable.
No new all-purpose IR is needed: the existing assembly, schedule, expressions
and mapped reports already provide the useful seams.

Retain the local eight-load mapping. Its mapped area is 8,418.8160 µm² below the flat repair
and 1,636.0974 µm² below even the unrepaired original baseline. The latter
margin was small enough to require measured buffering, clock distribution and
hold-repair cost. A one-level increase in maximum address depth did not prevent the
measured setup improvement.

That comparison is now [completed and retained](chip-physical-study.md#exact-mapping-placement-and-hold-repair--september-22).
The preparer bypasses synthesis for a selected mapping, and a fresh floorplan
ODB read-back checks every connection before continuation. Matched placement
and repair preserve a 12,218 µm² candidate advantage. Candidate coarse routing
finishes with congestion, while the baseline reaches its fixed cap. Fresh
timing separates placement RC from coarse-route RC: both placement hold screens
pass, but the latter leaves two candidate fast-screen violations at −0.105 ns.
The next discriminator is clock and SRAM interface repair, including actual
wire loads and both arrival bounds. SRAM pin access, internal Metal4 markers,
antenna closure and extracted timing remain separate obligations.

The subsequent clock experiment makes that discriminator more precise: an
explicit leaf budget clears most clock fanout and the measured hold failures,
but upper branches and SRAM wire loads remain. Before another full run,
demonstrate that the intended local repair changes those drivers/connections;
the enabled generic post-route repair made no netlist or placement change.

Future successful `check-tiled-chip.py` runs report `eligible-for-timing-screen`;
the previous structural score remains in the report as a diagnostic. Historical
receipts are unchanged. The final validation passes 30 focused Python tests,
the valid-program witness, 128 consecutive-branch checks, and the standard-axiom
audit (14,847 declarations / 7,543 theorems). Fresh original/tiled core and chip
MLIR plus the assembly manifest match the previous emission byte for byte.

The capture-forwarding expression and valid-word metadata reduction remain
proved options if a later measured path calls for them. Current evidence does
not make the cached-word path the setup bottleneck. Placement has now been
measured; routability, antenna checks, extracted setup/hold and complete
external-macro/package trace proof remain unfinished gates.

## Experimental upload pipeline — September 22

[`Storage.UploadPipeline`](../Pinwheel/Hardware/Storage/UploadPipeline.lean)
adds an opt-in register boundary on dictionary upload. It reuses
`SramController.core false`, the typed `Observer`, existing serial/pin feeders
and host-result observer. `SramAssembly` and its default emitters are unchanged.
The added state is one valid bit, six address bits and 64 payload bits.

| Edge | Stage action | SRAM action |
| --- | --- | --- |
| Accepted dictionary push | Capture new address/data; an old entry can drain concurrently | Write old queued entry if present; otherwise preserve the original read request |
| Eligible idle edge | Drain pending entry; become empty without a new write | Broadcast the queued write to both copies |
| Start or running | Hold the queued entry | Preserve the controller's execution read request |
| Accepted commit | Queue invariant requires no pending entry | Preserve the word-zero read needed for immediate start |
| Initialization | Clear valid | Issue no queued write; contents remain uninitialized until uploaded |

An immediate start after a push is the critical case. Unconditionally issuing
the queued write on that edge would hold SRAM Q instead of producing the
candidate response required by a one-cycle program. The implemented grant
therefore uses the actual core's busy, start and commit observations. Upload
may wait through arbitrarily long execution; execution gains no extra edge.
New accepted dictionary writes imply a drain opportunity, so one entry suffices
without a new UART command or backpressure signal. Reset/abort/restart histories
retain the loader's bank ownership; an abandoned pending write cannot commit an
incomplete replacement.

The Lean results have deliberately separate claims:

- `enqueue_drains` prevents replacement of an undrained accepted write.
- `bounded_next` preserves the invariant that a pending dictionary write has
  cursor at most 32; `commit_empty` excludes it at accepted cursor 322.
- `view_next` proves that physical contents plus the pending write match the
  logical contents after each accepted write, for a non-initializing edge.
- `reserved_read` checks the abstract grant; `observer_read_priority` checks
  the actual expression emitted at the macro write port.

These are queue/schedule and expression proofs. The existing `SramExecution`
theorem does not automatically cover the changed request/response schedule.
Full refinement still needs the stage invariant related to the emitted
registers, initialized-word coverage and actual SRAM Q at every usable read,
then composition with the complete chip. Physical timing is a separate gate.

`scripts/check-upload-pipeline.py` emits the variant and checks independent
atomic-reference traces with the pinned digital macro models. The final
fixture passes 14,200 core edges, including 32 immediate starts, distinct old
bank contents and four cancellation/replacement categories. A mutant bypassing
the shared write grant is rejected for an execution-state mismatch at edge
12,494. The current chip RTL matches the earlier 508,252-edge positive pin
trace byte for byte, allowing that trace to be reused. The standard-axiom audit
covers 14,932 declarations and 7,573 theorems.

Matched synthesis adds exactly 71 FFs and raises total mapped area by
7,580.4876 µm² (1.926141%) against the shared reference hybrid assembly.
The [physical study](chip-physical-study.md#sram-interface-geometry-and-upload-staging--september-22)
connects that cost to upload traffic at the real macro pins. The stage supplies
a placeable state boundary, but does not reduce the 64-bit communication width.
It remains experimental until a complete locality/clock/hold comparison justifies
its cost. A pipeline in the execution feedback loop remains a different change:
it must account for consecutive one-cycle branches and the next-response deadline.

The [completed locality screen](chip-physical-study.md#upload-stage-locality-and-available-placement-space--september-22)
rejects insertion of this stage into existing SRAM pin-face gaps. Shared word
consumers and row fragmentation defeat the intended locality: even a relaxed
allocation of the 64 data FFs raises the affected-net span estimate 50.52%.
This is a physical-organization rejection, not a failure of the checked schedule.
Broader repacking or a region including received-word decoding requires a new
complete-boundary cost. The experimental RTL and all its prior evidence remain intact.
