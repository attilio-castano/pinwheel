# Model24 one bounded residual and interaction study

The exact two six-conductor full-stack smoke cases both completed but failed
the unchanged 1% full-matrix reciprocity gate. The near case has three of 15
failing unordered pairs (maximum 4.8987%); the far case has four (5.2403%). The
retained diagnostic includes every pair and the original failed raw/resource
receipt. No matrix is symmetrized or promoted.

The pinned FasterCap source separates these mechanisms. In
`SolveCapacitance.cpp:108`, interaction approximation uses
`m_dEps = m_dEpsRatio * m_dMeshEps`. The source explains relative residual near
line 2273, and GMRES's implicit residual stopping check appears near line 2499.
A residual target controls a global excitation solve; it does not certify a
relative error for each weak matrix coefficient. Some observed disagreements
are small relative to the largest coefficient, but substrate-to-selected-M4
reciprocity also fails. These observations support a falsifiable differential
experiment, not a causal conclusion.

Root approved exactly one complete two-by-two factorial on both unchanged
geometries. All eight calls are fresh, including the failed-policy baseline.

| Profile | GMRES tolerance | Interaction ratio |
| --- | ---: | ---: |
| Baseline | 0.0005 | 0.25 |
| Residual only | 0.000001 | 0.25 |
| Interaction only | 0.0005 | 0.125 |
| Residual and interaction | 0.000001 | 0.125 |

Mesh remains 0.000383703, with Jacobi, Galerkin, explicit in-core `-f0` and the
same S20 physical-unit witness. Every warning, nonconvergence, wrong role/name,
positive off-diagonal, negative row sum, nonpositive energy or reciprocity
failure remains fatal. This is a distinct typed parser/profile. The original
34 smoke producers and every historical receipt remain unchanged.

The hard bounds are one CPU, 6 GiB RAM without extra swap, 512 MiB tmpfs,
256 MiB polled owned output per leaf, 60 seconds per leaf, 540 seconds measured
work and 600 seconds outer supervision. The next leaf requires enough work
budget; resource or custody failure stops the suffix. Closed numeric failures
remain visible while the fixed factorial continues. A successful prefix does
not establish a complete packet or accepted profile.

The diagnostic passes only if the full eight-call packet and its resource
closeout complete and one predeclared profile strictly passes both geometries.
That verdict preserves every other branch failure. If no profile passes both,
no further conditioning or numerical tuning is admitted this campaign. Even a
passing profile remains unqualified for mesh, length, extension, independent
reference, heldouts, the full applicable universe or timing.

The original 310-pattern deck would require 27,900 calls for three corners,
three lengths, five meshes and two extensions. The observed coarsest average
alone projects about 60 hours. It is not admitted in this campaign. A finished
route census must define any complete applicable envelope before calibration;
no successful numerical subset may define the model's scope.

The separate owned process source policy is ITF_MIN/TYP/MAX derived solely from
the exact merged ITFs. It does not mix draft width deltas or scaled gaps.
Source corner arithmetic does not establish foundry corner correlation,
physical tolerances or all eight model-coverage obligations. The diagonal
exporter/consumer convention repair remains separate and must receive actual
consumer checks before any quantitative model claim.

## Executed result and mandatory stop

Root executed all eight declared calls. Full independent raw/source/resource
readback matches the terminal receipt; measured work was 110.67240334 seconds.
All resource/input/runtime/cleanup checks close. No profile passes both
geometries, so the predeclared stop applies: no further numerical conditioning,
mesh, residual or interaction tuning is admitted this campaign.

| Profile | Near maximum reciprocity error | Far maximum reciprocity error | Both pass 1% |
| --- | ---: | ---: | --- |
| Baseline | 4.898726% | 5.240293% | No |
| Residual only | 3.837943% | 5.395880% | No |
| Interaction only | 1.314971% | 1.717293% | No |
| Residual and interaction | 0.926316% | 1.010310% | No |

The joint far case fails one of 15 unordered pairs: selected M4 to the second
TopMetal1 wire. Printed raw entries are `-1.00331e-11` and `-1.01355e-11`; after
one S20 conversion their absolute discrepancy is `9.765625e-20 F`. The relative
error is `0.01010310295496028809629520004`, above the unchanged `0.01` gate.
Closeness does not confer a pass, and the near success is not a complete model
or a permitted successful subset.

All 120 pair comparisons and complete failed-profile evidence are retained in
`model24-conditioning-raw-observations-01.json`, SHA256
`948f508a682b77360fb3e90e266a65142dd243a03924687ce346e8c988918556`.
The terminal resource report is
`build/streaming-tt-resources/8x4-24-model-conditioning-02/report.json`, SHA256
`0c88eb67d203942d250b6447b16f6f9bebe4ce2c21be3855181e433c6c78200a`.
Model qualification and qualified timing remain false. Separate synthetic
import/consumer convention controls may diagnose software semantics without
resuming physical coefficient calibration or bypassing these failed gates.
