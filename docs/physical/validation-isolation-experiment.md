# Upload-validation lookup isolation

The 2026-09-26 continuation tests one architectural change: give upload
admission its own read of the inactive parameter bank. The retained controller
shares a read with execution, creating a structural path from SRAM response to
the live command-rejection output. The previous calibrated physical screen
missed that output's setup requirement by 2.572 ns.

This experiment preserves the 290-word image, 32-entry parameter banks, state,
execution edges, package pins, 20 ns clock and I/O constraints. It adds no timing
exception. Any area increase is an explicit implementation cost.

The subsequent [balanced-distribution experiment](buffer-balance-experiment.md)
keeps this RTL and all nonbuffer mapped logic. It clears coarse congestion and
completes physical repair with positive screening timing; seven electrical nets
still need repair. This page retains the preceding experiment's measured
unrepaired layout and stopped repair as historical evidence.

## What is checked

`Pinwheel/Hardware/Storage/PairedValidation.lean` changes only the named `push`
computation. `isolatedPush_correct` proves that expression equals the retained
one under its upstream binding equations, for arbitrary register values and
inputs. Its proof distinguishes parameter uploads, row/boot tokens and the idle
word; malformed data is included. This is a local expression theorem, not a
proof of the graph lowerer, RTL emitter or complete paired execution semantics.

`test/PairedValidationEmit.lean` emits the opt-in implementation. The original
emitter remains the baseline. `scripts/check-paired-validation.py` reproduces
that baseline's RTL and declaration bytes, compares complete core and package
outputs and surviving next-state bits with unconstrained SRAM response and
current-state inputs, and checks both typical and slow saved mapped netlists.
The six unused reserved token bits are recorded explicitly in the state
projection. A deliberately inverted rejection output must fail equivalence.

The checker also uses the existing independent core/package traces, physical
cell models, exact one-macro terminal and flip-flop ownership checks, and a
structural reachability test from SRAM response pins to rejection. These checks
have separate scopes; neither SAT equivalence nor zero-delay pin replay proves
physical timing or closed-memory refinement.

## Completed functional and mapping screen

`build/validation/paired-validation-check-06/report.json` passes in 72.579
seconds. Both complete emitted-circuit comparisons and both saved mapped
comparisons pass. The independent core oracle checks 173,359 edges; RTL and
mapped package replays each check 331,401 edges / 1,517 frames. Axiom injection,
inverted rejection output and inverted mapped buffer are rejected for their
intended reasons. The library build/audit checks 15,556 declarations and 7,794
theorems with standard axioms only; four state-intake corruption tests pass.

| Measure | Retained shared lookup | Isolated validation |
| --- | ---: | ---: |
| Typical mapped cell + SRAM area, µm² | 302,239.2384 | 320,742.0360 |
| Added typical area | — | 18,502.7976 µm² / 6.1219% |
| Physical flip-flops / SRAM macros | 1,572 / 1 | 1,572 / 1 |
| Slow cell-only setup margin, ns | +3.93 | +7.99 |
| Slow cell-only hold margin, ns | −0.90 | −0.90 |
| Mapped signal fanout limit | 8 | 8 |
| SRAM response reaches rejection, typical and slow | Yes | **No** |

Cell-only timing has zero reported electrical violations. Hold still requires
physical repair. The area increase adds combinational lookup logic, without new
state or storage. This result supports the architectural hypothesis and admits
one fresh physical screen; it does not establish physical feasibility.

The checker retains five earlier failed attempts: an installed model-name
mismatch, a native-evaluation axiom caught by the audit, an incomplete proof,
explicitly trimmed reserved core bits, and an incorrectly imported negative
control. The final proof uses kernel-checked cases. The corrected negative
control changes both the JSON port and its named net; the original passing
negative test remains a failed checker receipt, not a successful circuit result.

## Allocation and provenance

The user's approval extends the first design-iteration phase by one opt-in
architecture candidate. The original eight-hour CAD budget, four-CPU/six-GiB
physical limit and one remaining A full-flow attempt stay in effect. The source
snapshot, explicit request and retained failed checks are under
`build/validation/paired-validation-isolation-01/`. Its starting charged CAD
balance is 2,640.603 seconds. A physical continuation requires passing the cheap
functional and structural screens first.

The [previous detailed layout](design-iteration-experiment.md) remains evidence
for its exact old netlist. No old routed result is attributed to the new design.

## Physical screen and decision

**Retain the equivalent architecture experiment; do not admit this coarse
layout to full routing.** The [result manifest](../../physical/experiments/validation-isolation-results.json)
binds the source, all failed attempts, physical checkpoint, independent checks
and resource ledger. A remains unaccepted; the 64-record B iteration remains
behind that gate.

The new target starts from its own checked mapped circuit. Exact import,
macro placement, power binding and the reserved SRAM corridor pass. Placement,
clock-tree synthesis and initial hold repair complete on the original 6×4
outline. Wire capacitance uses the prior extraction-derived calibration; the
20 ns clock, package pins and timing constraints stay fixed.

The first strict-congestion route was stopped. A congestion-retaining retry
then exceeded its 600-second cap. Inspection of the pinned FastRoute source
shows that relaxing a congested nondefault-width clock net restarts the
iteration counter. `GRT_ALLOW_CONGESTION` changes final admission, not that
loop. Thus the initial explanation attributing runtime to strict admission was
incomplete; neither interrupted attempt establishes unroutability.

One causal control clears exactly **ten clock width-rule bindings** in a fresh
copy of the saved database. Independent exports require an identical circuit,
placement, package, macro and power geometry. This changes the clock routing
policy explicitly; it adds no timing exception. The completed coarse route
reports **8,911 overflow units**: Metal2 1,254; Metal3 6,636; Metal4 1,021.
Subsequent post-route repair was stopped to measure this completed checkpoint.
Its unfinished work is retained separately and is not credited as a repaired
candidate. The observed checkpoint is before post-global-route electrical and
timing repair, not the endpoint of a completed physical flow.

Fresh measurements of that exact saved database use propagated clocks and
coarse-route parasitics, with no inherited corner metrics:

| Corner | Setup, ns | Hold, ns | Cap / slew / fanout violations |
| --- | ---: | ---: | ---: |
| Typical | −0.002695 | −0.377100 | 221 / 459 / 0 |
| Slow | **−9.286980** | −0.293061 | 217 / 1,103 / 0 |
| Fast screen | +4.882420 | **−0.409959** | 224 / 191 / 0 |

All consumed nets have wire estimates. The 198 unannotated drivers per corner
are independently reconciled unused outputs/inputs; there are no partially
unannotated drivers. Fast standard cells remain characterized at −40 °C and
SRAM at −55 °C, so that row remains an unqualified screen. These are calibrated
coarse estimates, not extracted final timing.

The targeted SRAM-to-rejection path is absent in both actual-netlist reachability
and all three timing reports. The new worst slow path is `r_active[0]` →
`r_cached[10]`, through **nine minimum-strength buffers already present in the
mapped source**. One of those buffers drives 0.920389 pF and has 5.713761 ns
output slew in this estimate. SRAM-to-entry setup is also negative, at
−7.479763 ns. SRAM-to-address setup remains +10.744295 ns; the scoped SRAM write
hold path remains positive. Removing the original dependency does not settle
the cost of distributing bank/control signals across a physical layout.

The placed circuit has **12,183 instances / 376,176.6432 µm²**, including SRAM,
in the same **1,289.28 × 710.64 µm** outline. It exceeds the historical repair
cell-area allowance of 359,372.4382368 µm² by **16,804.2049632 µm²**. That
allowance is an experimental comparison rule, not the competition die limit.
The fresh layout and the old repaired layout are not a matched one-variable
placement comparison; the evidence does not attribute every physical regression
solely to the duplicated lookup.

## Check the circuit that was actually measured

`implemented-check-01/report.json` checks the fresh OpenDB Verilog export
against the validated mapping. It exposes the exact **1,572 FFs and one SRAM**:
1,636 independent state/response bits drive the comparison, and every one of
the **5,000 sequential input bits**, including clocks and resets, is observed
alongside all package outputs. SAT equivalence passes under the pinned Liberty
functions. Adding a hidden FF is rejected; inverting an observed clock input
fails SAT. This check neither prunes extra physical state nor assumes that a
buffered clock is identical to the package clock without checking it.

The same actual circuit passes **331,401 external-pin edges / 1,517 frames**
with the pinned functional cell/SRAM models. Independent OpenDB inspection
confirms state endpoints, macro placement, power binding and the reserved
corridor. Routing preserves the preceding checkpoint's complete exported
placement/connectivity/power context. These results do not prove closed SRAM
execution, analog clock behavior, final layout legality or timing closure.

## Next discriminator and replay

The next useful comparison is the **distribution of active-bank/control
signals under physical loads**, including the long chain of small buffers.
Use matched mapping/placement controls to distinguish topology, drive strength
and wire distance. Preserve the new functional checks and record area costs.
Complete the resulting physical repair and routing stages before considering
the remaining A full-flow attempt; neither this negative preliminary screen
nor its interrupted optimizer is an impossibility proof.

The portable architecture gate is:

```sh
python3 scripts/check-paired-validation.py --tag NEW_TAG \
  --baseline-root /path/to/retained/paired-checkout \
  --cell-model-dir /path/to/pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/verilog
python3 -m unittest discover -s test -p 'test_paired_validation.py'
```

`physical/targets/paired-validation.json` binds the immutable successful mapping
selection. The result manifest binds the run-local physical requests, workers,
checks and pinned input paths. Replaying those physical recipes needs the exact
declared artifacts; a clean-source physical workflow is still unfinished.

Total charged CAD/check time is **4,080.913 seconds / 68.02 minutes**, including
the prior phase and all failed work. This extension uses 1,440.310 seconds.
The eight-hour budget and **one remaining A full-flow attempt** are preserved;
no new detailed route or extraction was run. Every owned CAD container is absent.
