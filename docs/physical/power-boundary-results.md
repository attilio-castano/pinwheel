# Power delivery depends on the declared integration boundary

Measured 2026-09-29 on the unchanged filled A chip. The saved nominal IR result
reproduces exactly, but depends strongly on how power enters the block. With
four explicit contacts per rail, modeled loss is about sixteen times the
distributed-source baseline. All three finite workload traces now annotate
every signal pin. **This completes the sensitivity experiment, not package
qualification.** A remains unaccepted and B is not admitted.

The [frozen protocol](power-boundary-experiment.md),
[result manifest](../../physical/experiments/power-boundary-results.json),
[audit recipe](../../physical/fixtures/power-boundary/README.md) and
[machine-readable report](../../build/validation/power-boundary-01/report.json)
retain the assumptions, failed attempts, measurements and costs. The prior
[qualification assessment](physical-qualification-assessment.md) remains the
source for the unresolved SRAM and fast-library conditions.

## Measured comparison

All cases use nominal extracted parasitics, typical 1.2 V / 25 C libraries and a
20 ns clock. External resistance applies independently to each of the four
resolved nodes on **each** rail; it is not one lumped package resistance.

| Activity / supply geometry | Resistance per source node | Modeled power (mW) | Worst VDD drop (mV) | Worst ground rise (mV) | Conservative rail loss (mV) |
| --- | ---: | ---: | ---: | ---: | ---: |
| Default / distributed block pins | 0 Ω | 9.119424 | 0.256722 | 0.285071 | 0.541793 |
| Default / four contacts per rail | 0 Ω | 9.119424 | 4.331130 | 4.305360 | 8.636490 |
| Default / four contacts per rail | 1 Ω | 9.119424 | 6.322650 | 6.312140 | 12.634790 |
| Default / four contacts per rail | 10 Ω | 9.119424 | 23.604200 | 23.620300 | 47.224500 |
| Clocked idle / four contacts per rail | 0 Ω | 6.817498 | 3.307040 | 3.295560 | 6.602600 |
| Replacement upload / four contacts per rail | 0 Ω | 7.028776 | 3.409230 | 3.416550 | 6.825780 |
| Running branch loop / four contacts per rail | 0 Ω | 6.835193 | 3.316520 | 3.302840 | 6.619360 |
| Replacement upload / four contacts per rail | 10 Ω | 7.028776 | 18.294700 | 18.325400 | 36.620100 |

The last row combines the highest **observed total-power workload** with the
10 Ω sensitivity. It gives a conservative local differential of 1.163380 V in
this model. It is not a lower bound across all programs or operating conditions.
The default-activity case happens to be higher than these three observed
workloads; that does not establish a universal bound either.

Rail loss adds extrema that may occur at different locations. This is a
conservative bound within the solved static model, not a simultaneous measured
voltage at one cell. These runs do not model package inductance, transient
droop, regulator tolerance, temperature dependence, electromigration or a
timing derate from local supply loss. Functional gate simulation supplies
activity without SDF; its event counts do not qualify physical glitch activity.
The SRAM model and its internal power characterization remain trusted inputs.
Its modeled power is 0.286033 mW for default activity, 0.000396 mW at idle,
0.014491 mW during replacement and 0.018081 mW for this constant-input loop.
These values do not independently validate the macro's energy model.

## Actual source geometry

The default solver resolves **7,912 VDD nodes and 7,832 ground nodes** from block
power terminals, including Metal4 and TopMetal1. It does not use a separately
declared package bump pattern. The four-contact diagnostic uses 1 × 1 µm
squares on TopMetal1, centered at the Cartesian products below:

| Rail | x coordinates (µm) | y coordinates (µm) |
| --- | --- | --- |
| VPWR | 27.88, 1257.88 | 13.78, 701.78 |
| VGND | 27.88, 1257.88 | 19.78, 691.78 |

The DEF audit places every square inside an actual exported power-pin shape.
Native PG exports resolve exactly the four requested coordinates in every
case. This matters because the pinned solver can silently select the nearest
node when a requested shape does not contain one. The source validator refuses
a displaced contact instead of accepting that fallback.

The pinned solver inserts the declared resistance separately for every resolved
source. Its PG SPICE exporter omits those external resistances, so the exports
are used only to inspect source identities, not to replay the resistance
experiments. Both behaviors are visible in the
[pinned solver source](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/psm/src/ir_solver.cpp).

## Workload and annotation evidence

The retained final signal netlist runs against the independent package oracle.
Both banks are loaded before measurement. Initialization and all intervening
commands remain in each simulation, with before/after external-pin checks.

| Window | Cycles | Duration | Meaning |
| --- | ---: | ---: | --- |
| Idle | 8,192 | 163.84 µs | Completed UART, clock running, unread result retained |
| Replacement | 63,656 | 1,273.12 µs | BEGIN, 290 legal PUSH frames and COMMIT; old bank retained until commit |
| Execution | 8,192 | 163.84 µs | Busy sampled-input branch loop with input held at 1 |

The final three simulations check 136,218, 200,092 and 208,510 edges respectively,
including warmup. They capture cell pins at the 20 ns constraint period.
Each native analysis reports **38,497 VCD-annotated pins and zero unannotated
signal pins**. The waveform audit also checks the period, exact window and
clock-transition count. All 70 unknown retained wire bits have no cell or
top-port connection. The other 1,572 unknown declarations are library-model
timing notifiers, not physical ports. No connected circuit bit is unknown.

The first trace set left an unused bank uninitialized; it is retained but not
used for the final comparison. A second set initialized both banks, but the
first three activity analyses used a dotted scope and captured only top-level
nets. OpenSTA accepted the file, annotated **zero pins**, and produced the
default estimate. These are **rejected measurements**, despite successful
process exits. The corrected traces capture leaf pins and use `power_tb/dut`.
The [pinned VCD reader](https://github.com/The-OpenROAD-Project/OpenSTA/blob/857316ff001b2a8dbbdc5996944d08a6d38c87ab/power/VcdReader.cc)
resolves slash-separated scopes and pin names. Corrected workers refuse to
calculate workload power unless every signal pin is annotated.

## What the integration contract must supply

The useful next gate is a declared parent/package boundary, not another route.

| Required evidence | Why it changes acceptance |
| --- | --- |
| Exact parent connection geometry and ownership for both rails, tied to this layout | Establishes which block terminals really receive supply and where |
| Supply minimum/maximum, temperature range and reference point | Establishes usable headroom against the qualified library conditions |
| External resistance or distributed RLC model, including return path | Replaces the illustrative 1/10 Ω values and enables transient analysis if required |
| Supported workload/activity envelope, clock assumptions and credible macro energy model | Replaces three finite observations with an applicable operating bound |
| A compatible timing/power qualification rule and component evidence | Connects allowed local voltage to valid logic and SRAM behavior |

The voltage-budget rule must account for source minimum minus VDD drop and
ground rise, with any required transient allowance. If the source may reach
1.08 V while 1.08 V is the lowest qualified local supply, there is no positive
drop budget. The nominal measurements above cannot establish a slow-corner
margin by simple subtraction; current and resistance must be evaluated under
the qualified conditions. Provider questions remain local and unsent.

## Cost and decision

Sixteen bounded invocations add **430.957 CAD seconds / 7.18 minutes**, including
two failed runner setups, all three trace sets and all three rejected activity
analyses. Every native container is absent after its invocation, and every
frozen input remains unchanged. Campaign cost becomes **8,843.120 seconds /
147.39 minutes** of the eight-hour cap. No full routing attempt, physical edit,
library edit or Lean change occurs. Three A routes remain used and two B routes
reserved.

The evidence audit verifies **273 input identities and 220 captured artifacts**,
reproduces the original worst rail drops exactly, rejects the zero-annotation
cases and binds all accepted source locations. The report replay is byte
identical. Five focused controls reject zero/partial annotation, displaced or
missing sources, and an unknown connected reset bit; 739 local documentation
links and 113 anchors pass across ten pages. The
[acceptance intake](../research/implementation-acceptance.md) is unchanged:
SRAM qualification, compatible fast conditions and qualified package power are
still required. The result is a checked way to evaluate a concrete integration
proposal when those inputs are available.
