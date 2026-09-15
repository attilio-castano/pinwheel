# Successor-fetch experiments

The general 32-entry dense cached core misses the 20 ns target at the slow
corner. Its worst measured path starts at a captured input, selects the next
address, looks up its instruction, and writes the current-word cache. This
study seeks a shorter implementation of that operation while preserving the
same protocol observations on every clock edge.

The committed [result manifest](../physical/experiments/fetch-results.json)
retains final measurements and hashes of the primary run, netlist and regression
receipts for both physical controls and both architectural screens.

## Fixed contract and baseline

Preserve every program accepted by the current backend, its capacity checks,
and every defined output: pin levels and enables, capture, status, faults,
loader behavior, and diagnostic reads. Reset, start, commit, same-address
branches, terminal capture feeding a branch, and consecutive one-cycle
branches are part of the contract. Speculative reads must have no effects.

The baseline is `routed4`, retained under `build/physical/core/runs/` and
documented in [physical validation](physical-validation.md). The RTL SHA-256 is
`1664dc719bff05307e3f17a6a8c611aba520917d49be132f1bf164bf1c53548b`.
The diagnostic core uses the same 6×4 rectangle, 20 ns clock, input/output
constraints, pinned tools and PDK for all flow controls. Neither the official
8×4 wrapper nor an external serial loader is included.

`python3 scripts/report-fetch-paths.py --tag routed4` examines the retained
slow-corner extracted maximum-path report and records source hashes in
`build/successor-fetch/routed4/paths.json`. Of its 1,000 reported paths, 112
have negative slack; report counts need not equal unique endpoint counts.
The worst 20 end at cached-word bits. The worst path ends at
`r_cached_word[49]`, with arrival 26.871183 ns, required time 20.617083 ns,
and slack −6.254101 ns.

| Worst-path contribution | Delay (ns) |
| --- | ---: |
| External input delay | 4.000000 |
| Logic-cell arcs | 12.406310 |
| Buffer-cell arcs | 10.185289 |
| Wire arcs | 0.272971 |
| Input-port arc | 0.006611 |

There are 56 output-cell arcs. The largest data-path fanout is nine and the
largest reported slew is 1.493079 ns. Excluding external input delay, 8.055636 ns
precedes the observed `read_b` net and 14.815547 ns follows it. This named-net
split does not separately identify address-map and dictionary costs.
Cell delay includes output-load and slew effects: the small wire-arc total
does **not** establish that wiring is unimportant. The path's clock leaf drives
15 loads. Buffering and electrical limits therefore merit a controlled test
before changing the fetch architecture.

The parser checks that delay contributions sum to arrival time. It separately
accounts for dedicated delay cells and register clock-to-Q, excluding the launch
clock tree from data-path totals. Validation covered 3,000 baseline setup paths,
50 register-launched hold paths, and rejection of a corrupted external delay.

## Experiment gates

1. **F1: fanout control.** Use `physical/experiments/fanout.json` to set the
   synthesis fanout constraint and CTS sink clustering size to eight. Clustering
   is a flow control, not a guarantee that every clock branch satisfies eight.
   Measure the resulting clock-tree area, hold repair and extracted timing.
2. **F2: post-global-route repair.** Continue from F1's global-route checkpoint
   with `physical/experiments/fanout-repair.json`. Enable design and timing
   repair after global routing. Compare with an unrepaired continuation from
   the same checkpoint. Keep repair cost separate from F1's effect.
3. **Combinational architectures, if needed.** A reads both candidate address-map
   indices, selects an index late, then reads the dictionary once. B reads both
   complete candidate records and selects a record late. C moves 55-to-64-bit
   expansion after record selection, if measured logic identifies expansion as
   useful to move. Each candidate must cover sequential, branch and idle paths;
   only the chosen successor can affect state.
4. **Proof and screening.** Prove lookup equivalence, then complete step/trace
   correspondence using the [timed contracts](timed-components.md). Run independent
   RTL regressions and a deliberately faulty variant before comparing full-core
   mapped area and timing. Preserve the baseline; reject candidates dominated in
   both area and timing. Route at most two architectural candidates, recording
   where the worst path moves and whether register-started paths become limiting.
5. **Physical acceptance.** Require fresh extracted setup and hold at all three
   PVT corners, electrical-limit checks, routing/Magic DRC, antenna checks, LVS,
   and the implemented-netlist regression. Report functional cell area before
   fillers and preserve failed results. A pass with negligible slack needs a
   margin review before further architectural work can be dismissed.
6. **Latency-changing storage only if necessary.** First prove availability and
   bandwidth for arbitrary accepted programs, including an endless sequence of
   one-cycle input-dependent branches. A registered prefetch or SRAM proposal
   cannot silently insert stalls or weaken the sampling schedule.

If the flow controls close timing and electrical limits with useful margin,
stop at that evidence gate and assess the value of architectural complexity.
The experiment list is conditional; it is not a commitment to build every
candidate.

## Proof foundation and flow results

The pure foundation for A and B is implemented in
`Pinwheel/Hardware/Reactive/FetchChoice.lean`: eight audited theorems establish
candidate-address independence, address selection and complete scheduler-input
equality after either index or record selection, and structural expression
correctness that composes with parent-machine registers and readers. A focused 128-edge sequence
checks uninterrupted one-cycle branches and detects stale selection on 63 edges.
`Pinwheel/Hardware/Storage/FetchChoice.lean` integrates both arrangements with the
logical writable stores and complete cached circuit. Its refinement composes
with the reference machine, preserving all pre/post-edge outputs and register
updates under the existing cache invariant. The full contract suite audits 95
declarations and confirms unchanged baseline MLIR/RTL. The dense physical
emitter remains a separate translation boundary, checked by RTL regression.

F1's extracted timing and netlist regression are complete. Its slow-corner worst
slack is **−6.254080 ns**, effectively unchanged from the baseline. The reported
worst path now starts at **`data[1]`** and ends at **`r_cached_word[0]`**. The
worst reported protocol-input path is `incoming[0]` at **−5.463827 ns**. The
retained 1,000-path report contains 95 violating paths from `data[1]` and 17 from
`incoming[0]`; it does not enumerate every alternative path to every endpoint.

| Extracted measurement | Baseline | F1 | F2 |
| --- | ---: | ---: | ---: |
| Cells before fillers (µm²) | 736,821 | 749,175 | 749,721 |
| Instances before fillers | 45,913 | 46,357 | 46,363 |
| Fast setup slack (ns) | +7.020443 | +6.940689 | +7.444266 |
| Typical setup slack (ns) | +2.184279 | +2.059968 | +2.746583 |
| Slow setup slack (ns) | −6.254101 | −6.254080 | −5.055013 |
| Worst hold slack (ns) | +0.041695 | +0.071192 | +0.022140 |
| Worst slew violation count | 48 | 45 | 51 |
| Fanout violation count | 443 | 36 | 34 |
| Worst capacitance violation count | 9 | 8 | 7 |

F1 has zero final router and antenna violations, and zero filtered unannotated
nets at all three extracted corners. The implemented netlist passes 21,409
edges and 3,510,998 defined output-bit comparisons; output inversion is rejected.
F1's full Magic DRC and LVS also pass. F2 likewise has zero final router and
antenna violations, zero filtered unannotated nets at all three corners, and the
same successful netlist regression counts and rejected mutation. Its full Magic
DRC and LVS also pass. Both flow invocations finish with exit code 2 because the
slow-corner setup check fails. Neither control closes timing or electrical limits.
The path reporter groups results by startpoint to expose movement between
protocol-input and loader-input paths.

F2's worst path starts at `data[45]` and ends at `r_cached_word[0]`; its worst
reported protocol-input path is `incoming[0]` at −1.298986 ns. Its retained report
contains 104 violating paths from `data[45]` and eight from `incoming[0]`.
Post-global-route repair improves worst setup slack by about 1.20 ns relative
to F1, while reducing hold margin and increasing slew violations. It is an
experimental flow setting, not a newly qualified default.

F2's intermediate fanout diagnosis found antenna-diode loads on all 13 listed
violating drivers, with eight or fewer non-antenna loads each. This explains a
flow interaction without waiving the library limit. The intermediate receipt is
`build/successor-fetch/fetch-repair/fanout-diagnosis.json`; final counts must be
checked after detailed-route antenna repair. In the final slow-corner reports,
all 18 listed F1 drivers and all 20 listed F2 drivers have antenna-diode loads
and no more than eight non-antenna loads; none is a clock buffer. These listed
driver counts differ from the flow's violation-count metric in the table above;
they are retained as separate quantities. Final receipts are the
`fanout-diagnosis.json` files under each routed tag in `build/successor-fetch/`.

## Architectural screen

Both A and B are implemented as optional dense-emitter variants; the default
emitter remains byte-identical to the baseline. No program-format, capacity,
clock-cycle, sampling, register-count or host-interface change is involved.

Each variant passes **21,864 independent oracle edges**, **13,444,072 storage
observations**, and **3,585,618 defined baseline output-bit comparisons** on both
sides of the clock edge. The extension includes 128 uninterrupted one-cycle
branches with self branches, terminal-to-entry capture ordering and rejected
host commands during execution. Branch-selection inversion and output inversion
are detected. This complements the universal structural E64 proof; it does not
prove the emitter or CIRCT.

| Full-core mapping | Baseline | A: late index | B: late record |
| --- | ---: | ---: | ---: |
| Typical cell area (µm²) | 561,587 | 588,567 | 606,659 |
| Typical ABC combinational delay (ns) | 7.70355 | 7.12096 | 7.43034 |
| Slow cell area (µm²) | 561,952 | 588,779 | 607,479 |
| Slow ABC combinational delay (ns) | 9.95114 | 9.95779 | 10.02479 |
| Flip-flops | 6,226 | 6,226 | 6,226 |

These use the existing separate-corner mapping recipe: buffer-2 input driver,
10 fF output load and a 10,000 ps ABC target. They are combinational estimates
without setup, clock-to-Q, placement or extracted interconnect. Tiny differences
near the mapping target do not establish a physical speed difference.

B is larger and slower than A in both mapped corners and is screened out.
A buys a 7.6% typical-corner delay improvement for about 4.8% more cell area,
but offers no measured slow-corner gain. Because the physical limit is at the
slow corner and the worst path now originates in loader data, A is not promoted
to a full routing run on this evidence. This is a decision about the next
experiment's value, not proof that A could never help after placement.
Neither candidate has been physically routed. C's expansion change and
latency-changing storage are deferred: the observed loader dependency deserves
investigation before changing the storage format or execution schedule.

Reproduce after the contract audit, using a fresh tag for each new run:

```sh
python3 scripts/check-timed-contracts.py
python3 scripts/check-fetch-choice.py late-index --tag screen
python3 scripts/check-fetch-choice.py late-record --tag screen
```

Receipts, frozen MLIR/RTL, oracle vectors and mapped netlists are under
`build/successor-fetch/late-index-screen/` and `late-record-screen/`. The earlier
`late-index-initial` artifacts are retained: its comparisons passed, then the
output-mutation harness stopped because it expected a mapped scalar net instead
of an RTL vector port. The harness now supports both forms; both `screen` runs
completed their mutation and mapping checks.

## Targeted launch-family timing

Independent extracted STA queries now cover each launch family in all three
retained implementations. Every rerun reproduces its original all-path worst
slack within 2 ps, using the same pinned container, libraries, netlist, SPEF and
SDC. No case analysis or timing exceptions were added.

| Slow-corner setup slack (ns) | Baseline | F1: fanout | F2: repair |
| --- | ---: | ---: | ---: |
| Protocol inputs | -6.254101 | -6.080494 | -4.927642 |
| Loader data | -6.018224 | -6.254080 | -5.055013 |
| Loader command | -4.547978 | -4.581484 | -3.861475 |
| Init/reset | -3.957737 | -4.738444 | -3.884335 |
| Register launches | -5.016371 | -4.933728 | -4.091041 |

The earlier F2 protocol row of -1.298986 ns was only an observed row in the
unrestricted report, **not** the worst protocol-input path. The targeted query
finds -4.927642 ns: protocol and loader paths remain nearly tied. F1 similarly
has a -6.080494 ns protocol path, worse than the previously observed row.
Removing the loader dependency alone cannot establish timing closure.
Each family report is capped at 1,000 paths; its negative-path count is not a
complete violation count. The protocol family returns 120 paths in each run.

The compact committed receipt is
[`fetch-launch-families.json`](../physical/experiments/fetch-launch-families.json).
Full reports and hashed inputs are retained under
`build/physical/core/targeted-sta/{baseline,fanout,repair}-families/`.
Reproduce with a fresh output tag:

```sh
python3 scripts/check-targeted-timing.py --run fetch-repair-route --tag repair-families-new
```

## Command-decoder experiment

Inspect the path from the small-store capacity check through command decoding
and bank/cache selection. `Storage.Small.inputs` rewrites a rejected push command
to command 6, then all loader gates decode that transformed command. This is a
concrete candidate for an unnecessary data dependency in commit/start logic.
The new `Small.adapt_command_predicate` theorem proves that every command
comparison except push (2) and reject (6) is unchanged by capacity adaptation,
including commit (3) and start (5). The generated baseline RTL nevertheless
feeds `checked_command` into those comparisons. This establishes a useful
algebraic simplification to investigate in the mapped cone, not grounds for
declaring timing paths false. A follow-up should isolate push validation from
unrelated control decisions, prove complete command/loader correspondence, and
measure under the same constraints. Antenna-induced fanout and the remaining
protocol-input path stay separate closure issues.

## Reproducing the physical controls

The runner allows only the four controls above in `--overrides`. Clock period,
I/O constraints, floorplan and RTL cannot be changed through that option. Each
run gets a new tag, frozen config/RTL/SDC, and a receipt with source identities.
Resume states must come from the matching implementation and configuration;
the runner records the checkpoint hash, but does not prove resume compatibility.

```sh
python3 scripts/run-physical.py --tag fetch-fanout --overrides physical/experiments/fanout.json --to OpenROAD.GlobalRouting
python3 scripts/run-physical.py --tag fetch-fanout-route --overrides physical/experiments/fanout.json --from-step OpenROAD.CheckAntennas --state build/physical/core/runs/fetch-fanout/39-openroad-globalrouting/state_out.json
python3 scripts/report-physical.py --tag fetch-fanout-route
python3 scripts/report-fetch-paths.py --tag fetch-fanout-route
```

Both physical controls and both architectural screens are complete. No
architectural candidate was promoted to routing, and the default implementation
and physical configuration remain unchanged. Mid-PnR states can inherit stale
corner metrics; only final extracted STA supports a routed timing comparison.
