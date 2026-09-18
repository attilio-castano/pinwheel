# Research status

Updated 2026-09-17 with the hardware closure, [cache-enable follow-up](../cache-enable-study.md),
UART receive capability from main, the flow-correlation diagnosis and the pin-sampler comparison.
This is the current decision brief; [results](results.md) owns completed
conclusions and [journal](journal.md) routes historical evidence.

## Objective and current belief

Build a general reloadable protocol engine whose implementation preserves
specified pin timing, input capture, branching, and atomic program replacement,
then establish physical feasibility under the [competition constraints](../competition.md).
Keep the reference execution semantics steady while closing implementation gaps.

The formal work now connects the emitted RTL of one explicitly composed 32-entry
dense cached Lean netlist to the reference machine. Its initialization, per-edge
state relation, and every pre/post-edge
observation refine the atomic machine with the existing 322-word capacity
restriction. The serializer consumes that netlist. The legacy dense cached
emitter remains the default and physical comparison baseline.

Completed validation distinguishes the two translation endpoints:

- **Countdown:** actual emitted RTL is interpreted back into Lean, with
  kernel-checked transition/trace equality and rejected corrupted artifacts.
  Yosys proves all 19 RTL/generic-gate comparison points.
- **Composed backend:** Lean checks the actual emitted RTL against the complete
  netlist refinement, covering 607 registers, 33 outputs and initialized traces.
  Its audit permits only standard axioms. Yosys proves
  all 6,315 old/new RTL and 6,309 RTL/generic-gate comparison points under the
  recorded state correspondence. Independent loader/storage regression and two
  mapped corners pass. The Verilog frontend/JSON adapter remain explicit trusted
  boundaries; technology-mapped sequential equivalence remains open.
- **External interface:** a proposed two-register sampling pipeline and
  open-drain interpretation have Lean contracts. They add no latency to the
  current core; the wrapper, serial transport and electrical assumptions remain
  integration work.

The [bank-selection experiment](../bank-selection-study.md) applies that method
to a composed command-split control and one candidate that selects between
completed bank reads. Both full circuit refinements and actual emitted-RTL
read-backs pass, including initialization, all 607 register updates and all 33
outputs. Each passes legacy/generic-gate equivalence, independent loader/storage
regressions, focused bank-switch cases and corruption checks. The actual circuit
can now be changed and measured with an explicit proof for each emitted variant.

The [cache-enable follow-up](../cache-enable-study.md) preserves the shared read
and every register update while simplifying the update decision. Both fresh
control and candidate pass complete emitted-RTL read-back, the standard-axiom
audit, equivalence and independent regressions. Exact-cache cases cover stopped
and running edges, faults, reset, self-branches and busy commit rejection. The
result removes direct control dependencies from the enable, while an indirect
cursor/command path remains through successor decoding.

The earlier portable gate passed 109 modules, 9,125 declarations / 4,665 theorems using
only standard Lean axioms, and all 20 executable suites. See the owning
[closure record](../hardware-closure.md) for exact hashes, initial-state
assumptions and failed attempts.

## Physical finding

The matched `command-split-closure` candidate completed routing and final
three-corner extracted timing with unchanged F2 controls and constraints.
Worst setup is **−5.049 ns**, essentially unchanged from F2's **−5.055 ns**.
Cell area excluding fill falls about 0.91%, while setup violations rise from
112 to 1,426 and the worst hold margin shrinks to about 2.9 ps. Electrical
violations remain. The implemented-netlist regression passes.

The worst path now starts at `loader_cursor[5]` and ends in the current-word
cache. Loader-data timing improves, but that does not close the core. The
[matched comparison](../successor-fetch-study.md#matched-command-split-physical-comparison)
owns launch-family measurements and the final layout-check disposition. The
one-hour attempt stopped during Magic DRC with exit 124. Magic DRC, LVS and later
checks are incomplete; routing/antenna checks report zero violations. The
[physical manifest](../../physical/experiments/command-split-physical-results.json)
pins that partial flow result. No candidate is promoted to the default.

The new bank-selection candidate stops at the matched mapping gate. Cursor-to-cache
logic depth falls from 32 to 25, but protocol-input depth grows from 35 to 38.
Area rises about 2.1%; typical ABC delay worsens 6.6% and the slow estimate improves
only 0.15%. This does not justify routing under the agreed gate. No new physical
run was started, and the conditional two-run allocation was unused. The
[bank-selection manifest](../../physical/experiments/bank-selection-results.json)
retains the proved candidate and exact receipts. These mapping measurements
do not replace the legacy artifact's extracted physical timing.

The cache-enable candidate improves the matched mapping screen: typical/slow
cell area falls 0.375% / 0.452%, and ABC delay falls 9.108% / 1.312%. Cursor logic
depth drops 32 → 28; protocol depth drops 35 → 32. Commands and reset also get
shallower, with unchanged maximum fanout. Retain this experimental variant; the
modest slow-corner gain supports a fresh matched physical comparison but does
not establish routed improvement. No physical run or default promotion occurred.
The [cache-enable manifest](../../physical/experiments/cache-enable-results.json)
pins eight completed receipts and 914 verified source/artifact hash entries.

## Flow-correlation finding (2026-09-17)

The [physical correlation study](../physical-correlation-study.md) re-reads the
retained command-split run without a new physical run. The resizer sees the slow
corner and finishes at **+0.055 ns** on global-route estimates; extraction then
reports −5.049 ns. A fit over 10,410 routed nets (R² 0.986) puts extracted wire
capacitance at 1.5–2.1× the technology-LEF values used for estimation. Separately,
6,423 hold-delay cells — about one per flip-flop — make timing-repair buffers
18.6% of functional area and lift utilization from 70% to 82%. A scratch
synthesis-only screen with integrated clock gates cuts mapped area 12.5%.
The earlier logic-depth candidates were therefore compared through a flow that
could not see the dominant delay term. This is a diagnosis, not closure.

The authorized `rc-calibrated-01` run (same RTL, constraints and floorplan; only
calibrated `LAYERS_RC` and Metal2/Metal3 estimation layers added to F2) moves
extracted slow setup from −5.049 ns to **−0.153 ns**, violating endpoints from
1,426 to 56, and slew/capacitance violations from 49/3 to 0/0, for +0.6 points
of utilization. Timing is still not closed and layout checks were not run. The
remaining worst path launches from the `incoming[1]` input port, inside the 4 ns
input-delay budget.

Clock-gated storage on the calibrated control cuts cell area **18.5%** after
clock-tree and hold repair (604,627 versus 742,324 µm²; utilization 67% versus
82%). The first two attempts do not route: `clock-gated-01` overflows Metal3 by
515 at the first global route, and the 62%-density retry `clock-gated-02` fails
later with a total overflow of 3. With marginal overflow left to the detailed
router, **`clock-gated-03` routes with zero violations: 608,454 µm² of functional
cells (−18.7%), 67.4% utilization, 13% less wire**, slow setup −0.617 ns with 16
violating endpoints (all launched from `incoming` ports) and hold met by only
3.4 ps. The routed netlist passes the oracle regression, and with vectors
extended to fill and execute every dictionary word in both banks, all 134
stuck clock-gate-enable mutants are rejected (84 with the earlier vectors: a
coverage gap in the shared regression, now closed). Metal3 is the only horizontal signal layer under the
template's Metal4 ceiling, and even the calibrated control runs it at about 70%
of derated capacity. Horizontal routability of the wide floorplan, not cell area,
may be the binding fit constraint; that is a hypothesis, not a measurement.

## Pin-sampler finding (2026-09-17)

The [pin-sampler study](../pin-sampler-study.md) inserts the contract's
two-register pipeline in front of `incoming` structurally, leaving every inner
expression unchanged. Lean proves that every pre/post-edge observation of the
wrapped netlist equals the reference machine's on the delayed pin history, for
arbitrary pipeline contents, with pair traces expressing the post-edge view of
the one combinational `incoming`-dependent output (`read_b`); registered outputs,
including pin levels and enables, are proved unaffected. The UART single-frame
and continuous `Safe` bounds survive the uniform two-RX-tick delay when both
stages hold idle at receiver start. The inner emission is byte-identical to the
read-back-proved command-split control; the sampled RTL is proved sequentially
equivalent to that RTL behind a hand-written pipeline (6,319 points), wrong
depths are rejected, and the independent oracle passes 28,165 edges with pins
presented two edges early. The sampled RTL has no direct Lean read-back.

Matched physical comparison on the calibrated flow: the composed control misses
slow setup by **0.797 ns**; the worst path into each of its 67 violating endpoints
launches from an `incoming` port, and the per-family query shows register-launched
paths into the same endpoints also missing by 0.294 ns. The sampled candidate's first attempt fails global routing with an
overflow of one; with marginal overflow left to the detailed router
(`pin-sampled-02`) it routes with zero violations and **meets extracted setup and
hold at all three corners: slow setup +0.090 ns, no violating endpoints**, 1.5%
less functional area, and a passing implemented-netlist regression. The limiting
path is now the register-to-register `r_cached_word` successor loop
(12.6 ns logic, 6.1 ns buffers). This is one run with no margin against the
observed 0.6 ns spread between equivalent RTLs; electrical-limit violations
remain, layout checks were not run, and the boundary is still the diagnostic
6×4 core. No frequency, fit or default claim follows.

**Combining the sampler with clock gating does not stack for timing.**
`combined-03` (after a Docker failure and a one-hour timeout, resumed from a
verified checkpoint with a 90-minute cap) routes cleanly at 67.4% utilization
with 608,058 µm² of cells, +0.059 ns worst hold and passing functional and
clock-gate mutation checks, but slow setup is **−2.251 ns**, and register-launched
paths alone miss by **2.054 ns**. Every family's worst path ends at the clock gate
of `r_cached_word`: gating moves the endpoint of the critical successor loop up
the clock tree (about 0.3 ns more adverse skew), and this run's path delay is a
further 1.8 ns longer than in the sampled-only or gated-only runs, which is not
attributed. Detailed routing needed 58 iterations and 71 minutes; gated designs
are consistently harder to detail-route despite lower utilization.

## Structural model (2026-09-17)

[Structural timing](../structural-timing.md) moves the recurring structural
questions into Lean. Arrival levels over expressions and netlists come with a
composition law, a wrapper law, and the theorem that an endpoint no launch point
reaches is semantically independent of it; for every inner netlist the pin
sampler provably leaves no combinational path from a pin to any inner register or
output. The compiled report takes seconds and needs no CAD tool. It reproduces
all 13 operation depths earlier studies measured on emitted MLIR, correlates at
r = 0.954 with twelve technology-mapped cone depths with every candidate change
in the same direction, and ranks the routed control's port families exactly as
extracted slack does. It shows that the successor loop spends 28 of 101 gate
levels in the storage lookup and **41 decoding the fetched word into the next
address**, and that the cached word's data arrives at level 50 while its enable
arrives at 99. 6,172 of 6,233 register bits recirculate through one multiplexer,
against 6,192–6,208 hold-violating endpoints found by the ungated flows.
Levels are ordinal; buffering, wire and placement stay outside the model.

## Register enables (2026-09-17)

[Register enables](../register-enables.md) makes the enable of a register a
certified object. By definitional unfolding, all 581 storing registers of the
proved bodies already have the shape `mux enable data hold` (index entries under
a slice); Lean reads the enable and data off those expressions and proves each
view describes the emitted next-state, so MLIR, RTL and read-back proofs are
unchanged. Gating policies are Lean definitions with two theorems: only
certified registers are gated, and the cached word never is. Storage enables
arrive at level 23–29 against 99 for the cached word, so gating them is
structurally timing-safe. `gate-clocks.py` applies a plan to the read-back-proved
RTL, checks the netlist against the plan bit by bit, passes the oracle with every
storage register observed, and rejects every stuck-enable mutant
(1,160 of 1,160 for the 580-gate plan). Mapped typical area falls from 546,149 to
497,263 µm² (dictionary) and **457,577 µm² (−16.2%)** (all storage) with mapped
delay unchanged; only 64 bits then recirculate, against 6,172, which predicts a
further large fall in hold-repair area that no routed run has yet measured.

## Input latency (2026-09-17)

[Input latency](../input-latency.md) makes the sampler's delay a parameter of the
pin-level contracts. `Latency.delayed` and a bridge theorem tie the structural
pipeline to cycle-indexed histories; because protocol and compiler theorems hold
for every input history, pin-level statements follow by substitution. **UART**:
unchanged up to age bounds two RX ticks later. **SPI**: samples are taken `d`
cycles before each rising edge, so a mode-0 peripheral with output delay `tco` is
read correctly whenever **`d + tco ≤ halfCycles`**, proved for the reference and the
compiled program and tight in execution; with the sampler that is SCK at most one
sixth of the system clock. **I²C**: the controllers observe their own drive, and
three hazards were proved for every target — under the former guarded STOP hold, a
false `busFault` for any `d ≥ 1`; `d` units of wait budget spent per clock rise;
and a premature high phase when `d > phaseCycles`. The first is now removed at the source: both reference
controllers **qualify** bus-free time after STOP as they already did before START,
and the explicit, counted and register-read programs use the existing `qualify`
instruction there (address 77, template 13, address 153). No instruction or
hardware changed, the emitted RTL is byte-identical, the compiler correspondence
theorems are re-proved for every input history, and the write images shrink to
713 and 203 bytes. Closed-loop executions of the references **and the compiled
programs** succeed for `d ≤ phaseCycles`, `d < waitCycles`, including stretching
and NACKs. The pin-sampled RTL, byte-identical to the routed candidate, replays eight
closed-loop writes and register reads with the bus seen two edges late
(35,824 edges); the former guarded record faults there after a complete wire
transaction. For `d = 0` one outcome changes: a line held low after
STOP now ends in `timeout` after the wait budget instead of an immediate
`busFault`.

## Memory abstraction (2026-09-17)

[Memory abstraction](../memory-abstraction.md) gives storage a contract:
`Memory.spec a w p ℓ`, one write port, `p` read ports, read latency `ℓ`,
read-first. Flip-flops refine latency zero and registered ports latency one,
each proved once for every size, and an output register on latency `ℓ` is
latency `ℓ + 1`. The atomic loader's image is two such memories written from the
decoded cursor, its instruction fetch two read ports of their composition, and
the routed backend's dense words per bank step as `Memory.Flops 5 55`; no
expression changed. The **prefetch machine** answers the primitive review's
scheduling gate in Lean: reading both candidate successors of the next edge from
next-state values, on two read ports, into two registers, the reference machine
runs against a latency-one memory with no added cycle — proved as an edge-for-edge
refinement of the atomic reference for every request and input history, with
commit refilling the fetch from the newly selected bank and initialization owing
nothing. Built structurally on the general backend, the prefetch machine's
addresses waited for the next-state decode (fetched registers at 103 gate
levels). The **decoupled machine** (`Storage/Decoupled.lean`) takes them from
the dispatch decision and the target instead, with a start-word register loaded
on commit; it refines the reference edge for edge and its structural netlist
(`Storage/PrefetchBackend.lean`, 610 fields, 6,425 bits, emitted alone and
behind the pin sampler) brings the deepest register endpoint from 101 gate
levels to **63**, the cached word from 101 to 38 and the core state from 91 to
59. Closed-loop execution against the reference: 5,161 edges, 12 transactions,
24 taken branches, for both machines. The emitted netlist passes RTL/gate
equivalence and the independent oracle (35,824 edges, alone and behind the
sampler); mapped, it is 19% larger than the sampled candidate (a second read
tree and three registers) with 15% less combinational delay at the typical
corner. Routed under the sampled candidate's contract, two attempts reached no
extracted timing: the calibrated overlay failed detailed placement at 81%
utilization, and the sampler-plus-clock-gating overlay placed at 80.7% but
global routing ran 858 congestion iterations without converging inside the
90-minute cap (the same-overlay control: 66.9%, 29 iterations). The structural
gain is unconfirmed after routing; at the diagnostic floorplan area binds
before depth, and the physical question that follows is area (a one-port
backend, or a floorplan with room).

**Fetch organizations** are now a parameter (`Storage/FetchPolicy.lean`): a
policy with `p` read ports and its own registers, fed from registers only, with
three obligations (`covers`, `preserved`, `initial`) from which the refinement
of the atomic reference is proved once, under an optional rule on inputs
(`Timed.RuleRefinement`). The backend is parametric in the policy too
(`Storage/PolicyBackend.lean`): the general backend with the successor as a
wire input is proved once, and a policy contributes its fed word, two wires and
its registers' updates (`Realization`). Three organizations are instances, each
with a proved, emitted and mapped backend; re-basing the two existing backends
halved them and left their emitted RTL byte-identical:

| Behind the sampler | Ports | Rule | Deepest endpoint | Mapped area | Typical ABC delay |
| --- | ---: | --- | ---: | ---: | ---: |
| Sampled candidate (same-edge lookup) | 1, combinational | none | 101 levels | 547,995 µm² | 6,803 ps |
| Decoupled | 3 | none | 63 | +19.4% | −14.5% |
| Two ports | 2 | none | 63 | +12.8% | −26.1% |
| One port | 1 | `Ready` | 65 | **+5.3%** | −22.5% |

The port parameter made the decoupled backend's third read tree (its start
word) visible; the other two share a candidate port on commit edges. The
one-port rule — no branching `checked` record with a zero duration — is asked of
push commands only, can be **enforced** by a push filter exactly like the
capacity check (`Storage/Admission.lean`: the refinement is then unconditional
against the reference behind the same filter; the capacity check is such a
filter by definition), and is **proved of the compilers**
(`Storage/Readiness.lean`): the I²C write and register read are ready for every
request whenever a phase lasts at least two cycles, UART and SPI transmission
always, and the UART receiver never — it polls with one-cycle branching records.
All four machines match the reference closed-loop on 5,161 edges; the one-port
RTL passes the independent oracle in ready mode and is rejected on the
unrestricted vectors, the two-port RTL passes the unrestricted ones. The
gate-equivalence harness now re-exposes registers that synthesis narrows, which
name matching had been leaving out; `prefetch-05` repeats the decoupled check
with every register matched.

**Routed, one run** (`oneport-sampled-01`, sampler plus clock-gating overlay):
the one-port backend places and routes at 69.2% utilization with zero routing
violations, hold met at all corners, and Magic DRC, LVS and the antenna check
passing — the first run of this design to finish its layout checks. Slow setup is **−0.187 ns** (9
endpoints) against **−2.251 ns** (40) for the same-overlay control
`combined-03`; the register-launched family — the recurrence this work attacks —
goes from −2.054 ns to **−0.053 ns**, and the command-launched clock-gate enable
path that limited `combined-03` is met at +0.473 ns, as its fall from 99 gate
levels to 36 predicted. The worst register path ends in the port's word
registers, the endpoint the level model ranks deepest. The slow corner is not
closed: all nine violating endpoints launch from the loader's data port, which
reaches the port's address through the capacity check on the command — the
dependency the command-split form removes and `Backend.Policy.core` does not
yet apply. Against the ungated sampled candidate (+0.090 ns at 81% utilization)
this design is 0.28 ns short with 14.7% less cell area. One run; 0.6 ns
run-to-run variation has been observed under this flow.

**The command split in the generic backend (2026-09-18).** `Backend.Policy`
now lifts loader-level expressions in the command-split form
(`BankSelect.lift`), so commit, start and bank selection decode the raw command
and all three policy backends inherit it with no change to their own files.
The level model had ranked the data port into the fetched words at 71 levels,
above the register family at 65, before the first routed run; that row was not
read. It now reports no path, `check-structure.py` asserts it for every policy
backend and prints the deepest family of each, and `Storage/DataPort.lean`
proves it: for every two-wire realization with data-free pieces, no register of
the fetch path has a structural path from the data port
(`DataFree.next`), hence its next value does not depend on the presented word
(`DataFree.step_independent`); the three organizations are instances. All three
re-emitted RTLs pass gate equivalence, the independent oracle and the required
rejections (`oneport-04`, `twoport-04`, `prefetch-06`); mapped area of the
sampled one-port emission is +1.8% over the sampled candidate (was +5.3%), of
the two-port +14.8% (was +12.8%) — the recipe's noise is a few percent.
Foundation gate `command-split-policy-01`: 173 modules, 6,528 theorems,
standard axioms only, 29 suites.

**Routed repeat, one port** (`oneport-split-01`, same contract as the first
run): setup is met at all three extracted corners with clock gating — slow
**+0.602 ns**, no violating endpoint — hold met, zero routing violations after
17 passes instead of 51, Magic DRC, LVS and antenna clean, flow exit 0 in 55
minutes. The data port's worst path now ends at the loader's `rejected` output
(+4.383 ns); every other family's worst path ends in the port's word
registers, the endpoint class the model ranks deepest. The register family
moved from −0.053 to +1.100 ns although its depth changed by one level of 65:
more than the 0.6 ns spread between equivalent RTLs, cause not isolated.

**First routed run, two ports** (`twoport-split-01`, same contract): did not
finish. At 75.2% utilization global routing spent 2 h 3 min in 71
one-clock-net-per-round congestion rounds (the one-port runs needed none),
completed with 57% more estimated wire than the one-port design, and the
150-minute limit ended the run in the repair step after it: no detailed routing,
no extracted timing. On this test rectangle and overlay routability ends between
69% and 75% utilization. The rectangle is not the chip: see
[the whole chip](../whole-chip.md).

## The whole chip in Lean (2026-09-18)

Every routed result above is the core alone on a 6×4 test rectangle, with its
67-wire loader port and about 130 observation wires as stand-in pins and an
assumed 4 ns arrival at them. The [whole chip](../whole-chip.md) is now one Lean
netlist with Tiny Tapeout's ports: pin map, two-register samplers on every
input, a three-pin serial loader (72-bit frames: command byte, 64-bit word),
any proved core, an output map. A layer in front of a netlist is a `Feeder`,
with one theorem for what the inner netlist then does; the receiver is proved
equal to its functions; any host session delivers exactly its commands to the
core among quiet edges; no pin has a combinational path past one flip-flop; with
a fetch-policy backend as the core the pins show the atomic reference machine on
the fed history. The upload theorem closes the chain: begin, 322 words and
commit, however spaced, leave exactly those words as the active image with the
engine stopped; the words a host builds from a program make the bank read as
that program and pass validation and, with at most 32 distinct records, the
capacity check; a held program is the one the engine runs, edge for edge; and
`chip_runs_upload` states all of it from the serial pins, for the two-port chip
(any fitting program) and the one-port chip (fitting, ready programs). An
executable host in Lean (`test/SerialUpload.lean`) delivers the compiled I²C
write's 325 frames through the sampler and receiver models and rejects driver
mistakes. Mapped, the whole one-port chip is 562,152 µm² (+0.8% over the
test-boundary core, +2.6% over the sampled candidate) and the two-port chip
614,555 µm²: the loader, samplers and pin map cost about what the observation
logic did. Not done: simulation and gate equivalence of the emitted
`tt_um_pinwheel` against an independent serial driver, and any placed or routed
run of it; the announced 8×4 outline is absent from the pinned Tiny Tapeout
files. Foundation gate `whole-chip-01`: 183 modules,
6,873 theorems, standard axioms only, 30 suites.


## Next discriminators

0. Screen structural questions with `check-structure.py` before any mapped or
   routed run. The calibrated flow and the matched composed control are the
   comparison baseline for physical work. Open flow-level questions, each needing its own
   allocation: repeatability of the sampled result (placement/seed variation or
   a modest clock margin); one routed confirmation of a Lean gating plan
   (`dictionary` or `storage`, cached word ungated) behind the sampler, which
   tests the predicted hold-repair saving and whether 580 gated branches route;
   the proved cache-enable variant, since the cache-update decision is the
   limiting endpoint; and a routability
   experiment on the official 8×4 outline, where Metal3 capacity rather than
   area may bind. Use `check-targeted-timing.py --design` for every comparison:
   the default report hides all but the worst launch point per endpoint.
   The `r_cached_word` successor loop is the path the architectural candidates
   should now be measured against, with the sampler and calibrated flow in place.

1. Extend sequential equivalence from generic gates to a selected technology
   mapping, explicitly accounting for initial-state correspondence and eliminated
   bits. Preserve independent tests with uninitialized storage.
2. Use the [cache-enable candidate](../cache-enable-study.md) for the next matched
   physical discriminator, with a separately accounted fresh composed control,
   unchanged 20 ns/I/O constraints and F2 controls. Keep the indirect shared-read
   dependency visible when interpreting the worst path. The current completed
   batch ends at mapping; the next physical allocation remains a separate step.
3. The test-boundary question is answered for now
   ([memory abstraction](../memory-abstraction.md#the-command-split-backends-routed)):
   with the command split the one-port backend meets setup at all corners with
   clock gating (+0.602 ns slow, one run), and the two-port backend does not
   route on the 6×4 rectangle (75.2% utilization). The open questions moved to
   the [whole chip](../whole-chip.md): (a) an independent check of the emitted
   `tt_um_pinwheel` — a serial driver outside Lean, RTL simulation against the
   direct-port oracle, gate equivalence; needs the hardware tools, no physical
   run; (b) one routed run of the whole one-port chip, which needs an allocation
   and an outline decision, since the announced 8×4 tile is not in the pinned
   Tiny Tapeout files — on it the two-port chip would sit near 56% utilization
   and may route, which would remove the program rule; (c) if the one-port
   organization is adopted, the UART receiver needs a two-cycle poll or the
   readiness filter beside the capacity gate; (d) a level-model candidate for
   the remaining register path: taking the target's increment at the leaves of
   its choice moves the port address from 34 to 29 gate levels (proved-equal
   rewrite, not built).
4. Decide whether SPI keeps the `d + tco ≤ halfCycles` rate condition of
   [input latency](../input-latency.md) or the compiler captures `d` cycles later,
   and whether the compilers should reject a `Config` that violates a declared
   latency's conditions (I²C: `d ≤ phaseCycles`, `d < waitCycles`). Resolve the actual wrapper/I/O budget and loading transport, then compose the
   [external timing contract](../external-interface.md) with protocol assumptions.
   Synchronizer delay must appear in those bounds; no asynchronous or analog
   detection guarantee follows from the digital two-edge theorem.

The completed command-split physical attempt used four CPUs, a 6 GiB limit and a
one-hour cap; its receipt records the end state. The bank-selection and
cache-enable follow-ups consumed no additional physical run. Historical cumulative
resource use remains unknown. This status record grants no additional run or
external action.

## UART receive capability

The [one-byte UART receiver](../uart-receive.md) now compiles to the existing
reactive engine and runs through E64, the atomic loader, and the default dense
cached core. It adds a digital receive contract without changing core circuitry.
All supported period/input configurations fit the current storage capacities.
TX and RX remain separate loaded programs. The [link contract](../uart-link.md)
now proves communication between independent program instances under clock and
observation-age bounds, including successive frames under the strengthened
continuous bound. Continuous buffering has a Lean supervisor contract;
its structural circuit and loader composition, a concrete input wrapper, and
concurrent execution still need their own designs and evidence. These capability
results add no physical closure evidence to the comparison above.

## Next proposed Lean question: receiver lifecycle and program replacement

Continuous listening keeps the current RX program busy, so stopping, resetting,
and reloading need an explicit supervisor contract that composes with
[atomic program replacement](../atomic-loader.md). It must also define ownership
of a pending result. The present theorem assumes one fixed RX program; this
lifecycle contract is the proposed follow-on.

## Deferred questions

- Synchronous SRAM/latches need a proved availability/write schedule for arbitrary
  accepted programs; average protocol idle time is insufficient.
- The bounded I²C repetition prototype has narrower scope than the general engine.
- The official 8×4 wrapper, package pins, electrical limits and physical timing
  closure remain separate obligations.

Reopen these when evidence changes the allocation, using the conditions in
[results](results.md). Preserve detailed limitations and frozen comparison contracts.
