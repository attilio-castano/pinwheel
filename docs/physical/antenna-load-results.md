# Antenna headroom: a rejected branch placement

**Reject the 41-buffer candidate before detailed routing.** It preserves circuit
behavior and positive coarse timing, but creates two capacitance failures. In
both cases the connecting wire alone exceeds the 0.300 pF limit. Reserving input
loads for antenna protection needs a simultaneous bound on routed wire load.

The [frozen experiment protocol](antenna-load-experiment.md) records the approved
September 27 allocation. The [manifest](../../physical/experiments/antenna-load-results.json)
binds the candidate, controls, complete measurement, diagnosis and resource ledger.
The preceding [detailed layout](balanced-detailed-experiment.md) remains the best
measured detailed artifact, with its one capacitance and 14 fanout failures.
[Research status](../research/status.md) owns the next decision.

## What was tested

Starting from the checked seven-buffer coarse circuit, partition the 15 affected
nets into spatial groups of at most three functional inputs. Minimize summed
receiver-group bounding-box wire length, place each noninverting buffer near its
group's median in a legal vacant site, and reroute only the affected signals.
This adds **41 buffers / 595.1232 µm²**. Original drivers and new leaves each have
at most three functional loads, leaving five of the library's eight fanout units
for later antenna inputs. This headroom is a design proposal; final antenna
insertion was not run and its effect is not established.

Every original cell and placement, all 340 coarse clock routes, package and SRAM
geometry, power connections and reserved corridor remain fixed. Exactly 56 signal
routes change: 15 existing nets and 41 added branches. Native and saved-grid
capacity/usage checks have zero overflow, including the inherited conservative
one-unit reservation. That edge is unchanged and no edited route touches it.
Import of this source reproduces its saved grid exactly; this does not erase the
older discrepancy from the source lineage.

Fifteen removal/replay controls and an actual edit/revert pass. Independent
readback verifies precisely the declared circuit edit. Arbitrary-state SAT checks
all 1,636 FF/SRAM output bits against all 5,000 state inputs and controls, including
clock/reset. Hidden-state and inverted-control mutations are rejected. Package-pin
replay passes **331,401 edges / 1,517 frames** against the retained oracle.

## What the complete coarse measurement says

| Corner | Setup, ns | Hold, ns | Cap / slew / fanout violations |
| --- | ---: | ---: | ---: |
| Slow | +0.845953 | +0.326675 | **2 / 0 / 0** |
| Typical | +6.655350 | +0.135776 | **2 / 0 / 0** |
| Fast screen | +9.780840 | +0.040186 | **2 / 0 / 0** |

All 64 SRAM write-input holds pass; minimum fast-screen write hold is
+0.100718 ns. SRAM-to-rejection reachability remains absent. Every consumed net
has a wire estimate. These are calibrated global-route estimates, not extraction.
The shared all-corner acceptance gate rejects the two capacitance failures.
The detailed-continuation preparer also rejects this actual receipt before
creating a route request or starting CAD. Pin access and final layout checks are
not reached and are not counted as passes.

A separate fresh source/candidate comparison verifies the exact existing
calibrated layer resistance/capacitance and reproduces every timing/electrical
metric. Its fast-screen measurements explain the failures:

| Parent net | Pin cap before → after, pF | Wire cap before → after, pF | Total cap before → after, pF |
| --- | ---: | ---: | ---: |
| `paired_balanced_148_17_out` | 0.021248 → 0.013016 | 0.236110 → **0.306268** | 0.257358 → **0.319284** |
| `_03354_` | 0.013280 → 0.008677 | 0.230130 → **0.300032** | 0.243410 → **0.308709** |
| `paired_balanced_5_4_out` | 0.029203 → 0.013016 | 0.256964 → 0.264038 | 0.286167 → 0.277054 |

Pin values are the maximum reported values. On the first two nets, reduced pin
load is outweighed by wire growth. Their serialized coarse wire lengths increase
**1,238.4 → 1,713.6 µm** and **1,209.6 → 1,720.8 µm**. Actual routes use more
vertical detours and different layers. Receiver-cluster distance did not account
for those connecting routes. The third net remains below its coarse limit; its
previous *extracted* failure has not been remeasured. The eight new branches of
these three nets all pass the measured electrical limits.

The next placement hypothesis should bound wire capacitance on both parent and
child branches, placing transport buffers along actual long routes and checking
congestion-dependent detours. Reducing logical fanout alone is insufficient.
No second candidate or automatic sweep is launched under this closed candidate
allocation. The newly allocated full-flow slot remains unused.

## Cost, failures and replay

The coarse candidate contains 12,230 cells and occupies **375,247.6704 µm²** of
signal-cell/SRAM area. This is **15,875.2321632 µm² / 4.4175%** above the historical
comparison allowance. The outline stays **1,289.28 × 710.64 µm**. No final antenna
or fill area is available for this candidate; do not compare this coarse area to
the preceding layout's filled area as a saving. Competition template admission
remains a separate obligation.

Controls, candidate measurement, actual-circuit checking and diagnostics charge
**126.399 CAD seconds**. Cumulative campaign usage is **5,052.680 seconds /
84.21 minutes** of eight hours. Two A full-flow attempts have been used; the one
newly allocated A slot and two B slots remain unused. B remains gated by A.

The first read-only load diagnostic rejected an inappropriate nominal-LEF
assumption for this calibrated flow (1.421 s). The next worker had a Python
format-string syntax error (0.183 s; no OpenROAD execution). Both failed receipts
are retained and charged. The final diagnostic checks all five calibrated layer
values explicitly and exactly reproduces prior source/candidate measurements.
No RC value or electrical limit is relaxed.

Recipes and immutable receipts live under `build/validation/antenna-load-01/`.
`prepare.py` records the single partition/placement plan, `launch-02.py` limits
controls and the candidate to 600 seconds each, `implemented-check.py` checks the
actual circuit, `verify-candidate.py` records the valid evidence and rejection,
and `closeout.py` binds the causal measurements and verifies the no-launch gate.
The frozen recipes refuse reused run identities; a new physical experiment needs
its own plan and fresh identity. Reading these receipts is artifact reuse, not a
clean-source or physical reproduction.

Fast cells at −40°C and SRAM at −55°C remain unqualified together. Complete
paired controller/loading/package refinement, accepted A, the capacity iteration
B and clean-source replay remain open. No Lean theorem or hardware language change
is claimed by this physical experiment.
