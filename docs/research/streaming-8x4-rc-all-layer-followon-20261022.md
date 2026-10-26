# Bounded all-layer RC follow-on proposal, 22 October 2026

This is a proposal, not an admitted experiment or model qualification. No new
field solve, solver, CAD process or recovered executable was run for this
assessment. The current frozen M1 producers and plans remain unchanged and must
remain available byte-for-byte for their independent reopeners after execution.

The existing two methods can extend to five-metal self capacitance and parallel
adjacent-layer coupling. The BEM builder extrudes arbitrary labelled rectangles
at their declared heights, and the independent FVM accepts one or two labelled
rectangles with separate unit excitations. A new case-plan/admission adapter and
a separately identified endpoint-preserving FVM producer are required. A third
physics method is not proposed. Completing this extension would broaden the
layered pilot; it would not close the full extraction-model gap.

## Cases and independent references

Use the retained merged ITF intake, exact routing-height convention and full
fox/nitride/oxide/passivation/air stack already declared by the
[M1 protocol](streaming-8x4-rc-layered-protocol-20261022.md). Derive every height
from the named source rows, rather than copying the table as new authority.

| Layer | Bottom / top (um) | Nominal minimum width (um) |
| --- | --- | --- |
| Metal1 | 1.04 / 1.46 | 0.16 |
| Metal2 | 2.00 / 2.49 | 0.20 |
| Metal3 | 3.03 / 3.52 | 0.20 |
| Metal4 | 4.06 / 4.55 | 0.20 |
| TopMetal1 | 5.40 / 7.40 | 1.64 |

The first optional extension has eight new TYP cases: four isolated minimum-width
wires on Metal2, Metal3, Metal4 and TopMetal1, and four centered parallel pairs
Metal1/2, Metal2/3, Metal3/4 and Metal4/TopMetal1. Each pair uses the separate
minimum width of each layer and its actual ITF vertical gap. Together with the
closed existing M1 self case this would cover nominal self C on all five layers
and one parallel vertical-coupling geometry across every adjacent gap.

Each new case needs a genuinely independent FVM matrix at both meshes and both
domains, not a scalar fit to FasterCap. The FVM must retain separate excitation,
true residual, energy/terminal-flux, cross-energy and reciprocity checks. BEM
must independently construct closed conductor surfaces and every material
interface, preserve the exact binary32 SI/S20 coordinate witness, and retain the
complete matrix and raw Native logs. A planar series-capacitor equation remains
an analytic equation control; it does not replace any wire/pair reference.

Do not add all corners and ranges to the first extension. After a complete
nominal pass, predeclare a separate held-out stage: doubled TYP widths on all
five layers, an offset adjacent-layer pair across each gap, and MIN/MAX on each
self/pair geometry for which a corner claim is sought. The existing M1 held-out
width may be joined only by its unchanged original receipt and scope. MIN/MAX
must remain unmeasured until their geometry, materials, policies and thresholds
are frozen; they cannot be used to tune the nominal fit.

These are parallel extruded-wire cases. Orthogonal crossings, line ends,
diagonal interactions, three-or-more-conductor shielding, wide power wires and
substrate/contact effects are outside this two-dimensional independent
reference. Their absence must remain visible in the coverage ledger.

## Known HOST admission limits

A geometry-only inspection used the current `_axis` function on nominal ITF
anchors; no operator assembly or field solve occurred. Fine h=0.02 um, E=32 um
self grids contain 31,239 / 35,581 / 35,581 / 37,247 / 36,765 nodes for Metal1
through TopMetal1. The centered Metal3/4 pair has 41,055 nodes and exceeds the
current 40,000-node limit. The limit cannot silently be raised in a case file;
a new resource-reviewed producer and frozen policy are needed.

The centered Metal4/TopMetal1 pair also exposes a future-case mesh bug. In the
linear subdivision of x anchors -0.82 and -0.10 um, recomputing the final
endpoint emits -0.09999999999999998 alongside the original -0.10. The resulting
2.78e-17 um interval rejects at both current mesh steps. The current M1 cases do
not encounter this seam. A new producer must preserve original endpoints and
generate strict interior subdivision points only, with focused endpoint and
all-new-case geometry checks. Keep the original frozen producer intact; record
the exact adaptation/source identity and unchanged operator body explicitly.

Upper-metal domain/length adequacy remains unknown even after those HOST fixes.
The current E16/E32 grounded FVM boxes may perturb TopMetal1 more than M1, and
10/20/30 um finite lengths may not give stable TopMetal1 end cancellation.
Failing domain or length gates require a separately frozen larger-domain/length
experiment with reviewed resources. They do not authorize looser tolerances.

## Execution admission and budget

Finish the existing six-case M1 experiment and its independent readback first.
A first Native point or a partial mesh/case prefix is not its pass. Review the
measured slowest call, total wall time, peak resources and convergence before
admitting any extension. No layered M1 timing measurement existed at this
proposal's 22:20 UTC assessment; the declared budgets are ceilings, not measured
runtime estimates.

Keeping the current five meshes and five length/extension combinations requires
25 BEM calls per physical case. The eight new nominal cases therefore require
200 BEM calls and 32 FVM calls. At the current 120-second leaf limits, their
per-call ceilings alone sum to 7 hours 44 minutes, before setup/cleanup. Actual
completion may be much faster; linear scaling from the M1 budget is not
evidence that it will be. All nine self/pair geometries at all three corners
would require 675 BEM and 108 FVM calls, before held-out ranges or controls.
That blanket campaign is not a credible remaining-night commitment.

If M1 passes quickly enough, the bounded follow-on is two independently complete
nominal batches: first Metal2/3/4 self plus Metal1/2 and Metal2/3 pairs (125 BEM,
20 FVM calls); then TopMetal1 self plus Metal3/4 and Metal4/TopMetal1 pairs
(75 BEM, 12 FVM calls). Freeze both case sets and thresholds before their first
measurement. Admit the second only if the first closes and measured cost fits.
Each batch preserves explicit call and whole-work deadlines, fresh outputs,
Root GO, one shared heavy lease and actual cleanup. Report incomplete membership
on timeout. Do not pool a successful subset into an all-layer pass.

The campaign's new-RC-experiment cutoff is 05:00:35 UTC and heavy cutoff is
08:00:35 UTC on 23 October. These experiments compete with routing, the final
actual-M proof, private audit and public-wire regression for the same heavy slot.
Admit no new batch that consumes their reserved time. If the eight-case extension
does not fit, a closed first batch is useful scoped progress and the second
remains a written, unexecuted proposal. Neither branch changes the hard stop.

## Gates and qualification boundary

Retain the M1 numerical gates: two successive complete BEM matrix changes at
most 2%; two length slopes within 5%; ground-extension changes at most 2%; FVM
mesh/domain changes at most 2%; and every self, ground and coupling slope within
10% of its independent fine reference. Exact case/mesh/length/domain/excitation
membership, all-warning rejection, source/runtime custody and cleanup remain
mandatory. No averaging across layers may hide a failed element. Any new domain,
length or tolerance policy needs a distinct premeasurement plan and identity.

The retained ITF MIN/MAX variants change routing dielectric ER, but the draft
extraction process also changes effective linewidth. For example its Metal1
drawn width 0.16 um corresponds to capacitance geometry widths 0.096 / 0.160 /
0.176 um for MIN/TYP/MAX; TopMetal1 1.64 um corresponds to 1.340 / 1.640 / 1.740.
Thus a nominal-geometry ER-corner pass does not qualify the installed draft
corner model. A process-authorized corner definition must state which geometry,
thickness, ER, sheet/via resistance and correlated variations each model bounds.
Monotonicity alone is not an accuracy or process-envelope reference.

Full qualification still needs the [eight-field coverage
ledger](streaming-8x4-rc-coverage-20261022.md): applicable R/via behavior, independent
C references over the final design's observed layer/width/spacing/via ranges,
consumer capacitance units and ground/coupling semantics, actual table
interpolation/extrapolation, and complete final-net annotation. Bind exact
model/LEF/process/consumer/corner/reference hashes and measured errors. The same
final ODB then needs extracted setup/hold/electrical checks at the qualified
corners. A successful all-layer pilot supplies none of those missing gates by
implication; `model_qualified` and tapeout acceptance remain false.

## Source basis

The relevant current sources are the [M1 case/threshold
builder](../../scripts/streaming_8x4_rc_layered_plan.py), [independent FVM
operator](../../scripts/streaming_8x4_rc_layered_reference.py), [finite BEM
geometry](../../scripts/streaming_8x4_rc_layered_geometry.py), [complete raw-file
analyzer](../../scripts/streaming_8x4_rc_layered_analyze.py), and [process/corner
audit](../../scripts/streaming_8x4_rc_process.py). The numeric linewidth examples
are retained in `build/campaigns/8x4-20261022-01/rc-process-review-01.json`; the
input layer rows are hash-bound by `rc-process-intake-01/manifest.json` in that
same campaign. This document neither revises those records nor changes their
original claim scope.
