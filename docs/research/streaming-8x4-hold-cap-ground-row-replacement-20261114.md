# Frozen 8×4 ground-row replacement around FILLER_3_3251/VSS

The former **597 µA** Metal1 hotspot did not recur at its original
section in any geometry-replacement run. In the 50.4 µm, one-via-pitch
window, the retained heated-sheet I²C case gave **152.138 µA** there and
**154.202 µA** at the highest utilization anywhere in the window.
The IHP reference for the 0.440 µm Metal1 row is **440 µA**.
One 11.12 µm window crossed the reference elsewhere under a mixed
local-resistance sensitivity. The remaining exterior grid and parent
supply assumptions still matter to the EM decision.
[Prior coupled study](streaming-8x4-hold-cap-cut-sharing-20261114.md) ·
[IHP CMOS5L §3.5](https://github.com/IHP-GmbH/IHP-Open-PDK/blob/2bbec755dc67ca3db0261c3d6163e15735d66710/ihp-sg13cmos5l/libs.doc/doc/SG13CMOS5L_os_process_spec.pdf#page=19)

## What changed in the electrical model

The candidate remains the frozen `dc654986…` ODB and `d4cd48f0…` GDS.
The full retained ground-grid dump supplies the I²C workload's signed
load and the original four sparse 1 Ω returns. The replacement cuts
the ground Metal1 row at two verified 0.440 µm faces. Each crossing's
resistance is split by physical length. All 12 exterior stubs exactly
match the drawn stripe, and the new mesh accounts for the interior
half-cell at the seam.

All lumped Metal1 edges inside each window and all idealized terminal
stars touching its interior are removed. When a terminal straddles a
seam, its load is divided by original attachment count. Exterior shares
go to their retained grid nodes and interior shares go to the cell's
verified VSS geometry. This preserves the native signed total and avoids
an artificial 1 mΩ bridge across the new mesh. The target decap has a
drawn contact model, with the net leakage applied to its body-tap
component. Neighboring cells attach their fixed leakage at Metal1.

Five windows include the nearby two-cut Via1 at (1567.400, 18.900) µm.
The original 10 Ω lump is removed and both 0.190 × 0.190 µm cuts
connect the exact Metal1 footprints to the retained Metal2 node. The
Metal2, Via2 and higher-layer paths remain in the exterior. The largest
window has one Via1, with left and right boundaries approximately
halfway to the neighboring Via1 arrays at X = 1517.400 and 1617.400 µm.

A reinsertion control restores the complete native lumped graph with the
same seam splits. It reproduces the original voltages within 33 pV and
the original return currents within 10 pA. At X = 1565.935 µm the
native graph carries **697.184 µA** across the section by a node-coordinate
accounting cut. **0.101 µA** crosses ordinary Metal1 resistors and the
rest crosses idealized terminal stars. Those currents are solver branch
flows. The new result comes from solving the exterior and replacement
together, with no original interior branches in parallel.

## Results

The table uses a 20 nm maximum tile, 0.17195244 Ω/□ heated Metal1,
20 Ω per Via1 cut and the typical target-contact model. The reference
section at X = 1565.935 µm uses the left-to-right mesh face. Three
interior sections at X = 1565.700, 1565.800 and 1565.900 µm also have a
verified 0.440 µm width and essentially the same flux in each window.

| Window length (µm) | Removed terminal stars | Reference section (µA) | Via1 |
| --- | ---: | ---: | --- |
| 3.400 | 3 | 222.804 | Outside |
| 6.700 | 5 | 307.152 | Two cuts |
| 11.120 | 8 | 402.378 | Two cuts |
| 19.830 | 13 | 232.563 | Two cuts |
| 26.650 | 17 | 207.070 | Two cuts |
| 50.400 | 31 | 152.138 | Two cuts |

The section current rises through the 11.12 µm window and falls for the
three longer windows. With 0.135 Ω/□ Metal1 and 5 Ω per Via1 cut **inside**
the replacement and the same heated exterior, the 11.12 µm window
gave **432.588 µA** at the original section and **465.122 µA** near
its right seam at X ≈ 1570.130 µm. The 50.4 µm window under the same
variant gave **188.282 µA** at the original section and **190.287 µA**
peak. This sensitivity test varies the resistance on one side of the
seam while holding the exterior parameters fixed.

The 56-case sweep includes 80, 40 and 20 nm maximum tiles, plus 10 nm
tiles for the five shorter windows. It also includes a Metal1-only control, target-contact variations and
5/9/20 Ω Via1 alternatives. In the 50.4 µm window, 40 to 20 nm changed
the original-section current by 0.391 µA. At 20 nm its two Via1 cuts
carry approximately **10.182** and **9.283 µA** toward Metal2. An
independent sparse solve stamped the exterior port admittance directly
into the mesh and reproduced the heated baseline results. Independent
vertical-slice current balance also closes against the left-of-section
sources, contacts and Via1 transfer. The worst local section balance
residual is 64.6 fA, and the worst ground-return balance residual is 23.8 pA.

The original 597 µA indication disappears in the replacement diagnostic.
The short-window boundary sensitivity near 1570.130 µm remains, and
the exterior uses lumped power-grid elements. Qualified EM requires the actual
parent supply boundary, device and interconnect models and operating
envelope. Local rehearsal remains GO. Fabrication remains NO-GO.

## Reproduction

The raw results are ignored local files under
`build/8x4-hold-cap-20261107/trial-02/power-dc/`. Use the retained
precheck Python 3.12 interpreter with KLayout 0.28.17-1, NumPy 1.26.4
and SciPy 1.17.1 available on `PYTHONPATH`.

| Receipt | SHA-256 |
| --- | --- |
| `m1-exterior-04.json` | `9a00b40675bf41775e27147f2c547749b758a46e9ec3f28c69383a73e4d31e06` |
| `m1-replacement-02.json` | `7b4acee76170d7159a06c09d59aea33fcbbd54c65dbde1f801c5b57877f31cec` |

```sh
POWER=build/8x4-hold-cap-20261107/trial-02/power-dc
"$PINWHEEL_GEOMETRY_PYTHON" -B scripts/streaming_8x4_hold_cap_local_m1_grid.py \
  --out "$POWER/m1-exterior-verify-01.json"
"$PINWHEEL_GEOMETRY_PYTHON" -B scripts/streaming_8x4_hold_cap_local_m1_solve.py \
  --out "$POWER/m1-replacement-verify-01.json"
```

The solver consumes the pinned `m1-exterior-04.json` receipt. The
first command independently reproduces that exterior response. The
original receipts and verified rehearsal bundle stay in place.
