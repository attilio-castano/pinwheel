# Buffered SRAM: remaining experiments and acceptance gates

Recorded 2026-10-16 after the [overnight campaign](../physical/tt-buffered-overnight-campaign.md).
**C14 is the retained routing reference; the chip is not physically accepted.**
These are proposed allocations, not launched work or standing permission.
The [result manifest](../../physical/experiments/tt-buffered-overnight-campaign-results.json)
binds existing evidence. Preserve failed attempts and each experiment's source,
constraints, evaluator, caps and actual completion separately.

## 1. Test the SRAM restart mechanism — proposed 25 minutes

**Question:** does net7845's internal wire split cause the empty local access
set? The original fatal callback measures both fresh M2 access points 130 nm
beyond the worker boundary. Their exclusion is observed; the selected internal
endpoint's causal role remains unproved.

Starting from exact C14, merge only its two collinear M2 legs at x = 611.760 µm,
y = 142.380→144.000→144.130 µm. Prove equal conductor union, 0.200 µm width,
outer endpoint styles, vias and default/NDR semantics. All other nets, cells,
placement, SRAM/PG geometry, clock topology, RTL, ABI and constraints stay exact.
Do not suppress pin-access failures or broaden the edit into a router patch.

**Prerequisite:** prepare and independently review a new immutable positive
acceptance wrapper. The frozen observer03 diagnostic launcher intentionally
requires a failed producer and the historical two-error ledger; a successful
repair would fail that old gate. The new wrapper must require producer success,
no native or terminal-wrapper errors, actual completed iteration 4 (or verified
completed early-zero), measured observer context, full header reconciliation,
custody, frozen-scope checks and owned cleanup. No positive launcher is prepared.

Allocate one minute preflight, six for a strict normalized no-edit control,
sixteen for one ordinary end4 restart and two for closeout. The control must
retain full geometry/rules and the original 1,731-marker table. Compare complete
iteration 0–3 prefixes; unexplained divergence prevents causal attribution.
Persistent DRT-1231 rejects this repair; timeout/incomplete work accepts no
candidate. Error disappearance supports representation sensitivity only. Any
completed layout needs separate same-source timing, GDS DRC/LVS and antenna.
The [source-bound proposal](../../build/physical/tt-overnight-campaign-20261015/analysis/C14/restart-pin-access-observed-03/future-positive-acceptance-card.json)
contains the prospective union proof and original diagnostic bindings.

## 2. Test one NWell finishing repair — separate approval, 15 minutes

The [one-filler proposal](../../build/physical/tt-overnight-campaign-20261015/analysis/C14/one-filler-proposal-01/README.md)
places one unmodified `sg13cmos5l_fill_1` at (774.24, 351.54) µm, R0, on a
witnessed vacant site, with VDD→VPWR and VSS→VGND. Its predicted well union
bridges one measured 0.480 µm gap. This changes cell inventory and supply
connections, outside the closed campaign's authorization.

Require native legal placement, unchanged original cells/routes, actual
streamout, disappearance of the exact NW.b witness under the same full deck,
and no added conductor short or attributable DRC. The filler includes active,
poly, contacts and M1 supplies; it is not just a well polygon. This tests one
mechanism, not all 2,053 records. Existing rail collapse prevents a chip-LVS
pass claim. Broader filling, diodes or rerouting need their own scope.

## 3. Qualify timing before choosing a logic repair

Calibrate the extraction stack against applicable CMOS5L data and reference
structures, investigate coupling/load contributions, and obtain justified
fast/slow logic–SRAM conditions and RC corners. Keep the present 20 ns clock
and I/O contract as the comparison target. Slower-clock characterization would
be separate and cannot repair hold failures.

Then compare mapping/resynthesis of the same RTL against C14's deep prospective
SRAM-address cone, requiring sequential/cycle equivalence and complete mapped
protocol checks. Address pipelining needs proof of prospective-data availability
at the actual SRAM edge or an explicit cycle-contract change; preserving packet
ABI alone is insufficient. C14's 67 cell arcs and large cell delay motivate
this study without proving that logic depth alone explains the model's delay.

Assess the three fast hold endpoints path by path before sizing or inserting
delay; require the declared 50 ps reserve across qualified corners without
spending setup headroom blindly. Recheck slew, capacitance, fanout and Liberty
table domains after actual antenna repair; logical receiver count alone does
not bound the extra loading from diodes and routed wires.

## 4. Close qualification and establish a reproducible submission

Repair demonstrated signal-to-PG bridges, qualify the actual SRAM's internal
extraction/comparison and applicable PDK rules, and rerun same-source DRC,
unique boundary LVS, timing and antenna. Keep extraction warnings explicit.
Qualify density and final power/connectivity with actual parent supplies and
activity; a nominal static sensitivity is insufficient. Install an isolated,
exact supported official TT precheck environment and compare pinned versus
captured-current whitelist behavior without stripping valid macro layers.

A future concurrency comparison must set threads in the actual Python Design
application, measure native worker context and compare fresh one/four-thread
controls. CLI configuration is not observed concurrency. Keep runtime,
determinism and layout quality separate; no speedup or quality gain is assumed.

Competition preparation follows the [recorded external requirements](../competition.md)
and [submission gates](../submission-plan.md), rechecked when preparing a real
submission: compatible TT ports/template, area, supported flow, open-source
package, reproducible build, documentation and required checks. Stronger research
also seeks initialized interpreter-to-packed-circuit refinement, general
source/compiler/serial composition, independent SRAM internals, calibrated
physical assumptions and repeatable capacity-changing A/B iterations. No new
formal theorem was proved overnight; these goals neither disappear on merging
nor become organizer requirements.
