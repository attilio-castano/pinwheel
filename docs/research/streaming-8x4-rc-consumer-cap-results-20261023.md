# Actual M1 capacitance readback and consumer-selection proposal

The four-call C1 measurement packet passed its strict consumer controls. A
separate provisional comparison shows a material ground-capacitance mismatch
with the independently stable FVM reference. The frozen full accuracy gate
remains **unmeasured** because the mandatory original BEM experiment failed.
Neither measurement completion nor the provisional comparison qualifies a model.

All generated paths below are relative to
`build/campaigns/8x4-20261022-01/`.

- `rc-consumer-cap-independent-readback-01.json`, SHA256
  `b89ee54c5c95a4880abc5108586733587c18e1c0637d830b5328dc618da7b9b3`,
  reopens every raw SPEF, copied input, written DEF and exact resource receipt.
- `rc-layered-reference-independent-readback-01/report.json`, SHA256
  `128681523cd638cf4ef8be0c1aa57cb601f07cef581b72bd62014b1d8c2e2906`,
  reopens all 25 FVM calls, their empirical gates and Root resource admission.
- `rc-consumer-cap-provisional-FVM-comparison-01/report.json`, SHA256
  `e90d52fb0b2e2be03009900b9223c9c08b0e245b218b7eb41238e879c8243532`,
  preserves all matrix cells, both length slopes, both spacing fixtures,
  unit conversions and conservative serialized-value rounding bounds. Its
  `readback.py` is HOST-only and reproducible.

The raw C1 packet has exact 50/100/150um lengths, default .16um M1 width and
.18um pair spacing. All D_NET totals reconcile with ground plus full incident
coupling; mirrored coupling is deduplicated correctly. There are no cells,
ITerms, routed vias or unintended inter-group couplings. Consecutive slopes
differ by at most 0.001482%; doubling fixture separation/padding changes them
by zero at the serialized precision. This isolation control is not a physical
ground-boundary test.

| Quantity | OpenRCX, pF/m | Fine FVM, pF/m | Relative difference |
| --- | --- | --- | --- |
| Isolated-wire self and ground | 45.0244 | 85.0550463 | -47.0644% |
| Pair diagonal, first slope | 156.78448 | 180.4540994 | -13.1167% |
| Pair coupling magnitude, first slope | 121.5002 | 129.0078353 | -5.8195% |
| Pair ground row sum, first slope | 35.28428 | 51.4462641 | -31.4153% |

The second pair slope is 156.7864 / 121.502 / 35.2844pF/m. Every matrix cell
and ground sum is retained rather than averaging the discrepancies. Printing
bounds are far smaller than the failed 10% provisional comparisons. These
bounds describe the OpenRCX writer's rounding, not FVM continuum uncertainty.

The reference passed all six physical case groups at two meshes and two
domains plus its uniform limit. Maximum mesh change is 1.316004%, maximum
domain change 0.243027%, maximum reported true residual 9.991928e-10 and maximum
reported energy/terminal-flux error 4.331996e-14. Geometry-only dry grids and
Maxwell signs, row sums, reciprocity and positive energy were independently
recomputed. Potential and edge arrays were not retained: scalar residual and
energy errors remain source-bound producer diagnostics. Empirical mesh/domain
stability is not a rigorous continuum enclosure.

## Source-grounded cause

The rule file's `Version 1.2` describes its format. It is distinct from the
extraction command's `-version 1.0`. At pinned OpenROAD
`dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`, ext.i:70 enables the new extraction
flow only for command versions at least 2.0. The old netRC.cpp:1667 compatibility
reader detects open-section/VIARES markers and loads the newer format, including
OVER0, but its old extraction lookup still uses the regular OVER table.

[`extMeasure::getOverRC`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/rcx/src/extRCmodel.cpp#L2012)
uses `_capOver`, and a negative/no-neighbor distance calls getFringeRC.
The default index is -1; its
[`lookup`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/rcx/src/extRCmodel.cpp#L1698)
returns the last regular distance row. The retained table ends at .9um,
with no separately sampled infinite-distance sentinel. The M1 OVER context-0
row at .9um has coupling 0.0000328544 and fringe 0.0000225122fF/nm. Its .18um
row has coupling 0.000121501 and fringe 0.0000127722fF/nm.

Those selected coefficients explain the actual measurements without fitting:
self is twice the far fringe, 45.0244pF/m; pair ground is far fringe plus
near fringe, 35.2844pF/m; pair coupling is 121.501pF/m; pair diagonal is their
sum, 156.7854pF/m. The small differences in the first serialized slope are
within the declared writer-rounding bounds.

The populated separate `Metal 1 OVER0` section contains only one distance-zero
row: coupling zero and fringe 0.0000467172fF/nm. Its existence does not prove
the old consumer uses it, or that it represents a valid whole spacing range.
The causal primary-source intake is `rc-cap-causal-source-intake-01/manifest.json`,
SHA256 `ef1c7ae013237229066e66c7032bdd161c1702f9b1b0ecee4843a8067d03c5f8`.
It binds extRCmodel.cpp, extRCap.h, extmeasure_couple.cpp and extmeasure_dist.cpp
by exact Git blobs and SHA256, together with the earlier consumer intake.

## Source basis for the separate version-only diagnostic

Before coefficient calibration, prepare a separately typed command-version 2.0
diagnostic using the **same four C1 fixtures, exact table and all other flags**.
No table coefficient, process geometry, reference, tolerance or canonical
timing policy changes. Keep four fresh 30-second calls, 150 seconds work,
180 seconds outer, one CPU, 2GiB including 128MiB scratch, no extra swap,
warning-fatal raw parsing, complete attempted membership and exact cleanup.
Root GO and independently reviewed new source/plan identities are required.
The separately typed worker was subsequently admitted and measured as C2;
its actual results are recorded below.

The proposed change has a concrete lookup mechanism, not an assumption that
version 2 repairs the model. extFlow_v2.cpp dispatches to extMeasureRC, whose
OverUnder selects OpenEnded2 for two open sides and OpenEnded1 for one.
[`OpenEnded2`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/rcx/src/extmeasure_couple.cpp#L1452)
still fetches the regular far row but adds twice **coupling plus fringe** to
ground. That predicts 110.7332pF/m for the isolated wire if this branch executes.
For one open side,
[`getOverRC_Dist`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/rcx/src/extmeasure_dist.cpp#L146)
selects `_capOver_open[met][0]`, exposing the current single zero-distance
OVER0 row to a .18um request. Its resulting lookup, coupling and warning/failure
behavior must be measured; a valid nonzero pair coupling is not implied.

Preserve failures and report measurement custody separately from numerical
controls. Full accuracy remains unmeasured while the original BEM prerequisite
is false. A later complete replacement BEM policy would require a distinct
typed accuracy join naming its actual new hash. No coefficient fit is proposed
for execution until consumer selection and table-format applicability are
resolved. All observed C1/FVM values are development data for any later model
research; independent held-out widths, spacings, layers and corners remain
necessary and cannot be promoted from a successful fit to these cases.

## Frozen version-2 HOST preparation

The new worker and reader are `streaming_8x4_rc_consumer_cap_v2.py` and
`streaming_8x4_rc_consumer_cap_v2_readback.py`. They preserve and reopen a
complete immutable C1 preparation copy. Every non-Tcl input file is identical;
the only measurement policy change is the extraction version token. The
worker retains C1's fixed four-call body with only its typed receipt schema
changed. The reader differs only in the bound module and typed schemas.
Geometry, SPEF parsing, Maxwell reconstruction and slope/isolation arithmetic
call the original frozen C1 functions. Four focused normal and optimized-Python
adaptation controls pass alongside C1's eight strict parser/physics controls.

- `rc-consumer-cap-v2-preparation-01/plan.json`, SHA256
  `4e47a2b8628016221b2c231cea18a18bae47b4ac075f10eed115411dec2898e5`.
- `rc-consumer-cap-v2-command-proposal-01.json`, SHA256
  `79387a8a9560f6c622bc7deb0aad11b7afab5a3483cf52ff0a2ee5463a385868`.
- `rc-consumer-cap-v2-HOST-readiness-01.json`, SHA256
  `d04f3831229f67829aeec4fd869f36d50b4b951200384cd4bdf6d77b0fc1d6af`.

The source predictions above are explicitly retained as hypotheses in the new
plan, not guaranteed repairs. No coefficient was changed or calibrated.

## Actual version-2 readback

C2 completed all four calls. Both isolated cases pass the strict scalar
consumer parse, while both pair cases fail `Missing intended coupling or
incident total differs` despite OpenROAD exit zero. Frozen independent readback
`rc-consumer-cap-v2-independent-readback-01.json`, SHA256
`72c1155e8287230a2b1a527050478bac4bf46d225811c297558dec65d36b0721`,
joins all four raw leaves and the exact failed resource terminal, unchanged
input seals and empty process/container cleanup. Measurement controls fail;
full physical accuracy remains unmeasured.

Both isolated length slopes in both spacing fixtures equal **110.7332pF/m**,
exactly the source prediction 2 × (last regular coupling + last regular fringe).
The pair SPEFs contain no two-node coupling rows and include zero or asymmetric
ground totals. They are retained as failed raw inventories, not reconstructed
as valid Maxwell matrices. The separate HOST source readback is
`rc-consumer-cap-v2-source-readback-01/report.json`, SHA256
`bf402ce5c3f67703d745e8836c933153b3f013a240a9f8384f0af2a4f950660e`.
Changing the command version does not repair this table's applicable accuracy.

## Finite-endpoint development study

Root approved and executed this distinct four-call development study after commit `c2de534`. All raw measurement controls pass; the candidate development gate fails the untuned larger-gap coupling comparison.
`rc-cap-far-row-development-proposal-01.json`, SHA256
`621baa705264eff5e68ecdc575a44e61893bf89a5ed57daf302d92869c787a65`,
describes one append-only change to the v1 regular M1 OVER context-0 table:
retain all five original rows and all other bytes; change DIST count 5 to 6;
append `9 0 0.000042527523152569435 0`. The prepared table SHA256 is
`28418aef896dbb35c404723cd23d6f00157a29a7527c9df55fe2b327261c051f`.

Only the isolated .16um fine FVM value trains the new last fringe: target
C_per_m divided by 2e-6 converts to half-capacitance in fF/nm. No pair or wider
reference enters that fit. The endpoint distance 9um is ten times the prior
largest spacing; it is a declared synthetic finite consumer policy, not a
measured isolated limit. Zero endpoint coupling and interpolation from .9 to
9um are unvalidated assumptions and excluded from accuracy claims. Reserved
99/100um sentinel lookup paths have different source assumptions and are
deliberately avoided. These limits must remain in any admitted protocol.

The proposed four-call universe is retained/new table × 512/1024um group
separation. Every call contains all three 50/100/150um lengths for isolated
.16um training, the already observed .18um-pair development control, a .36um
pair held-out consumer measurement, and isolated .32um wider stress. The
wider wire requires an exact DEF NDR declaration and semantic 320DBU width
readback. It cannot inherit a default-width geometry check. Existing FVM and
table predictions are already known; blind statistical validation is not claimed.

Preserve all original near-spacing coefficients and the 5% slope, 2% isolation
and 10% numerical comparison gates. Source arithmetic predicts .18um pair
ground 55.2997pF/m, about 7.49% high, with coupling about 5.82% low. The .36um
pair ground is predicted about 7.71% high, while its unchanged coupling is
**18.86% low** and should fail the numerical comparison. That held-out failure
must not trigger a coefficient or tolerance adjustment inside this study.
Training success supplies no independent validation. Full physical accuracy
remains unmeasured while the original BEM prerequisite is false; full model
qualification remains false. Proposed resources remain four 30-second calls,
150 seconds work and 180 seconds outer, one CPU, 2GiB including 128MiB scratch.


The frozen preparation03 plan is `rc-cap-far-preparation-03/plan.json`, SHA256
`c68adbaf9c7ce2374383db08e423b706a2c88f88abd5e062ed16b986a0033de5`;
its command proposal03 is SHA256
`4c441162be5c864f69943465c1d42450ef5fbd1bc5bfd622b63219f4d6f4290e`.
Physical independently reopened the exact packet and passed all ten focused
controls in normal and optimized Python. Exact 18-net/36-port NDR geometry,
complete Maxwell membership and the campaign/shared-lock/wrapper/supervisor
resource join are mandatory. Preparations 01/02 remain preserved unexecuted
and superseded before measurement. See [the complete frozen protocol and
readback command](streaming-8x4-rc-cap-far-20261023.md).


Actual far-row independent readback
`rc-cap-far-independent-readback-01.json`, SHA256
`bfc10aaacb56a4f6ae89aa6b5367b4faf51678c3928a4b89a05ab7bec8042051`,
reparses all four leaves and joins exact resource cleanup. Candidate .16 self
is 85.0552pF/m (training only); .18 pair diagonal/coupling/ground is
176.7998/121.5002/55.2996pF/m. The .36 pair's coupling 59.5318pF/m is
18.8569–18.8572% below FVM, so both spacing fixtures fail the unchanged 10%
gate as predeclared. Wider .32 self also gives 85.0552pF/m, 9.70892% below FVM;
its clamped-width result supplies no range qualification. Maximum slope change
is .00148146% and isolation difference is zero. Conservative writer uncertainty
.0176pF/m per slope cell cannot explain the held-out failure. All 24 resource
input seals and Root GO separately rejoin in
`rc-cap-far-independent-closeout-01/report.json`, SHA256
`de78c620cb9838c48e4b1b0664e208e849c609ef0f72bed1d7c665684c8ede05`.
No original near coefficient or tolerance changed. Full accuracy remains
unmeasured, with original BEM prerequisites false and model qualification false.
