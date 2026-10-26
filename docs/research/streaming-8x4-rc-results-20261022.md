# RC pilot results for the 8×4 campaign

**Status at 2026-10-22 22:06 UTC: the five-mesh historical uniform U block and
eight independent uniform FVM references pass their declared stability checks.
The complete finite-wire/held-out cross-solver pilot and CMOS5L model
qualification remain open. No layered field solve or consumer microfixture has
executed yet.**

The [predeclared protocol](streaming-8x4-rc-protocol-20261022.md) owns the cases,
flags, held-out width and tolerances. No shared PDK/model bytes were changed.
All paths below are relative to the ignored campaign owner
`build/campaigns/8x4-20261022-01/`.

## Actual observations

| Attempt | Actual result | Claim limit |
|---|---|---|
| `rc-native-outputs/rc-manualU-m0-01` | FasterCap exited zero and retained a warning-free complete matrix. The workflow correctly remained failed because its new parser did not recognize the pinned writer's parenthetic duration suffix. Cleanup and source/runtime continuity closed separately. | Failed workflow remains failed. Its log became a captured grammar control, not a promoted result. |
| `rc-native-outputs/rc-manualU-m0-02` | A fresh execution under the corrected full-footer parser passed. Actual solver time 0.156096 s; worker wall time 0.344294 s; observed sampled maximum RSS 16,336 KiB. Copied/original inputs and runtime remained unchanged, the process was reaped, and scratch availability was unchanged before/after; no out-of-core use was reported. | One manually selected mesh only. Requested inner GMRES tolerance and zero exit are recorded; this does not independently prove a continuum error bound. |
| `rc-native-outputs/rc-U-mesh-block-02` | All five plan04 U meshes passed. Complete matrix changes were 13.6341%, 4.72110%, 0.692622%, 0.271501%; the last two meet the unchanged 2% gate. Total worker wall time was 10.4819 s. | Empirical stability for this development geometry, not a continuum bound or complete pilot. |
| `rc-independent-reference-01` | All eight plan04 FVM cases passed strict true residual ≤1e-9 and energy/flux checks. Width 0.16 µm mesh/domain changes were 0.482272%/0.287271%; width 0.32 µm changes were 0.369093%/0.315456%. | Two uniform-medium infinite-length cross sections; no native length-slope/held-out comparison yet. |

The second attempt uses the unchanged historical aspect-U geometry as a new
experiment: Galerkin, manual mesh 0.000383703, interaction ratio 1, GMRES
tolerance 0.0005. The two conductors are the finite ground box and SIGNAL.
It produced 6,934 refined panels and 140,372 potential estimates. Its symmetric
energy form is positive definite; Maxwell signs and row sums pass. Maximum
relative reciprocity disagreement is approximately 0.000256667, below the
predeclared 0.01 limit.

The same combined policy previously completed in the first attempt; fixing its
footer parser changed the workflow, not the solver flags or geometry. The new
parser requires the complete duration suffix, verifies its integer breakdown
against the numeric seconds, and rejects truncated, inconsistent or extra
footer text. Fourteen normal/optimized protocol controls now include the exact
captured Native log; the first twelve synthetic controls had not exposed that
native-format gap.

The policy differs from the old automatic run both in manual mesh selection
and the tighter GMRES tolerance. Its success is evidence for that combined
policy, not an experiment isolating the mesh choice as the sole cause.

## Inspectable identities

- New execution plan: `rc-manual-preparation-03/plan.json`, SHA-256
  `b6767dfed8c7f2db5a0b8c4ee5222857347029aa920eb8c1675e9744d1600d39`.
- Actual second raw log: `rc-native-outputs/rc-manualU-m0-02/native.log`, SHA-256
  `bf900e267934a638f4de418f74de6e19dcd6bd180e41b366918e3725fd21840c`.
- Independent pure HOST readback:
  `rc-manualU-m0-02-independent-readback/report.json`. It reparses the actual log,
  checks flags/names/dimensions/physics/units against the fixed plan, and checks
  zero exit, reap and input-continuity facts in the execution receipt. The
  campaign owner joins the separate resource-supervisor cleanup receipt.
- First failed execution's raw log:
  `rc-native-outputs/rc-manualU-m0-01/native.log`, SHA-256
  `421cf2188f14265f768ab37629817336c7f55e150a4f78ae4197fbb3448a5f92`.
  Its exact captured control is retained in
  `test/fixtures/streaming-8x4-rc-manual-U-20261022.log`.
- First failed execution's producer bytes remain under
  `rc-manualU-m0-01-source-preservation/`, with their original hashes and the
  earlier committed source snapshot. Its separate later HOST interpretation
  explicitly leaves its workflow failed.
- Current plan04: `rc-manual-preparation-04/plan.json`, SHA256
  `2ae5d3b357b92677963eed5e27d4e847e3ffc896ab86f70c73ff5b861990f260`.
  It tightened the independent reference acceptance to the exact declared true
  residual bound before the first full reference measurement.
- Combined independent raw-log/reference readback:
  `rc-plan04-U-reference-independent-review/report.json`. Its
  `full_pilot_passed` and `native_benchmark_membership_complete` remain false.

## Remaining numerical obligations

The ten new native width/length/ground-extension cases still must run all five
declared meshes, satisfy their own refinement gates, and pass the third-length,
boundary-extension and held-out comparisons against the independent references.
An incomplete or failed case set cannot establish a pilot pass.

The separate [consumer R experiment](streaming-8x4-rc-coverage-20261022.md) is
frozen before measurement. Exact source arithmetic found that retained LEF wire
and via resistances equal ITF MAX while draft MIN/TYP rules have empty VIARES
stanzas. Six fresh consumer calls will measure that seam and an owned VIARES-only
repair without changing shared PDK bytes. The separate
[actual ITF layered M1 protocol](streaming-8x4-rc-layered-protocol-20261022.md)
adds lateral coupling, explicit dielectric interfaces and untuned width/spacing/
corner cases. Its FVM grids and finite 3D geometry have HOST witnesses only;
none has been measured. Source review caught scale-dependent FasterCap manual
mesh semantics before execution, so all native cases now share an exact S20
normalization and require a warning-fatal diagnostic before full admission.

Even a passing uniform-dielectric pilot would leave layered-process accuracy,
resistance, vias, diagonal/multilayer contexts, corner definitions, extraction
table/consumer coverage, SPEF annotation and final routed timing open. The
draft upstream RC model remains unqualified.
