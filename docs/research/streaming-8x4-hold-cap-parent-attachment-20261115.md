# Frozen 8×4 parent power attachment rehearsal

The published TT0004 CMOS5L parent layout has named tile power attachments
that can be recovered at the actual placement and cross-checked against
the separate project views. Replaying two of its historical strap phases
against the frozen 8×4 candidate gives an illustrative contact map for
both Metal4 rails. The TTIHP27a staging repository was empty when checked
on November 15. An assigned 27a placement and its power boundary remain
open.
[TT0004 foundry release](https://github.com/TinyTapeout/tinytapeout-ihp-0p4-foundry-submission/tree/66fb0eb377f4e565a6f7b275ad748bc21783f57a) ·
[TTIHP27a staging](https://github.com/TinyTapeout/tinytapeout-ihp-27a-staging)

## Published placement controls

The reader uses the TT0004 release OASIS hierarchy and separate project
OASIS/LEF files from the public shuttle source. The source and placed leaf
Metal4 drawing, pin polygons and named labels agree. It transforms each
LEF rail pin through the placed instance's actual orientation and checks
complete containment of the parent landing pad, bounds of all 22 TopVia1
cuts per array, and the associated parent horizontal TopMetal1 strap.
The parent `odb_power.py` maps leaf VPWR to `vdpwr` and leaf VGND to
`vgnd`. The named factory-test attachment establishes the two strap
families by span. The three held-out projects agree independently with
those rail names, and every published rail pin has a complete array.
[Pinned shuttle projects](https://github.com/TinyTapeout/tinytapeout-ihp-0p4/tree/dae4c4eaf3a404a4ba5ecf4cd8b65d01e85294a2/projects) ·
[Pinned parent power binding](https://github.com/TinyTapeout/tt-multiplexer/blob/3e496494ee9f543ec4b84e5e71bdaee25e958ce1/ol2/tt_top/odb_power.py) ·
[Pinned PDN recipe](https://github.com/TinyTapeout/tt-multiplexer/blob/3e496494ee9f543ec4b84e5e71bdaee25e958ce1/ol2/tt_top/pdn.tcl)

| Placement in TT0004 | Orientation | Rail pins per rail | Parent arrays per rail | Physical cuts per rail |
| --- | --- | ---: | ---: | ---: |
| `tt_um_factory_test` | R0 | 4 | 8 | 176 |
| `tt_um_2048_vga_game` | M0 | 13 | 52 | 1,144 |
| `tt_um_lisa` | R180 | 17 | 153 | 3,366 |
| `tt_um_urish_sic1` | M0 | 13 | 117 | 2,574 |

The 10 µm horizontal ground straps span X = 370.280–3229.720 µm.
The corresponding supply straps span X = 400.280–3199.720 µm.
The remaining strap family is outside this rail assignment. Choosing
Via3 instead of TopVia1 leaves the scoped attachments empty. Swapping
the named parent families and shifting the factory instance by 1.8 µm
each fails the corresponding attachment check.

## Frozen 8×4 historical strap projections

Each candidate rail has 105 exported LEF rectangles representing 35
continuous full-height Metal4 stripes. Their union agrees with the
frozen macro's pin and drawing layers, and each named label lands on its
rail. Each projected phase crosses all 35 stripes on each rail with nine
parent straps, giving 315 intersection rectangles per rail. The verified
resolver finds **665 VPWR and 630 VGND** native Metal4 nodes for either
phase. The two 4-tile-high historical placements supply only the phase
and orientation. The 8×4 projection crosses the real TT0004 occupancy.
Allocation, routing coexistence and parent via generation are outside
this projection. Even a valid future placement needs independently
reviewed voltage, feed and return impedance and transient allowance.

## Stock hardening PDN comparison

The clean stock hardening run's step 21 DEF records 35 Metal4 stripes
per rail, each 2.1 µm wide. The DEF boundary-pin rectangles agree exactly
with their named `SPECIALNETS` stripes. Centers start at 12.880 µm for
VPWR and 16.980 µm for VGND, at 50.000 µm pitch. All four known TT0004
macros use the same local widths and respective center sequences. On the
two 4-tile-high macros the vertical span agrees exactly at 3.560–707.080 µm.
Projecting the stock rectangles onto the same two historical phases
produces 315 complete 2.1 × 10 µm intersections per rail.

The frozen custom design starts its same-width stripes at 16.400 µm
and 24.080 µm at 49.880 µm pitch and carries its pin rectangles to the
macro boundaries. Both geometries give full same-rail stripe coverage
in the historical overlap projection. The stock geometry reproduces
the older projects' local coordinates. No 27a evidence establishes if its
parent requires those coordinates or regenerates attachment from other
accepted macro power pins.

## Static power sensitivity

The restamp uses the retained heated I²C read case's exact conductance
edges and fixed instance currents. It removes the original external
source equations and solves both rails for three source arrangements.
The previous OpenROAD result is reproduced with the four sparse
1 Ω sources per rail, to a maximum 1.275 nV node-voltage difference
and 0.309 nA source-current difference. A separate distributed-ideal
solve applies the same heated sheet resistance, so geometry and series
resistance are the only changed electrical inputs between these cases.
The unchanged current load is 19.306429 mA on both rails.

| Source arrangement | VPWR nodes | VGND nodes | VPWR drop (mV) | VGND rise (mV) | Sum (mV) | Minimum instance differential (V) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Four sparse, 1 Ω each | 4 | 4 | 21.244 | 20.873 | 42.117 | 1.157913 |
| TT0004 projected, 1 Ω each | 665 | 630 | 0.636 | 0.619 | 1.255 | 1.198745 |
| Distributed ideal | 5,215 | 5,215 | 0.553 | 0.525 | 1.078 | 1.198922 |

The projected VPWR and VGND peak geometric branch currents are 72.95
and 75.86 µA, respectively, both on Metal4. Peak modeled source currents
are 56.95 and 54.63 µA. The prior native distributed comparison gave
1.004 mV at the room-temperature sheet settings. This run gave
1.078 mV with the same distributed contact locations and heated sheets.
The observed source-count sensitivity includes a much smaller aggregate
feed resistance when hundreds of independent 1 Ω branches are supplied.
It leaves the shared package impedance, physical cut sharing and
transient voltage drop open.
[Earlier native comparison](streaming-8x4-hold-cap-ir-em-20261112.md#static-ir-drop)

## Evidence and replay

The geometry and restamp receipts each match their repeats byte for byte.

| Ignored receipt | SHA-256 |
| --- | --- |
| `build/tt-parent-attachment-20261115/parent-attachment-02.json` | `dc95506f75f2fafa6a60a88eabfb546e73ba96d248afc233a53f511377beba90` |
| `power-dc/parent-tt0004-projection-resolved-01/resolved.json` | `d34fc6e3a042297b12cdd16cef902e52f77d8f63495b7aebf519cf3cc4afa75f` |
| `clean-tt-04/project/runs/wokwi/21-openroad-generatepdn/tt_um_pinwheel_streaming_ready_d2.def` | `6689b7857d574410d859ebe67c03fc54fbe3f4f52ee9a4a0d45183a354929ccd` |
| `power-dc/tt0004-parent-restamp-01.json` | `5948dd508726a2c91fde85e1a5d8bf324d5f03573cf4002c55ea317133317979` |

The script lists retained source file names and hashes. Point
`PINWHEEL_GEOMETRY_PYTHON` at the retained KLayout Python interpreter,
make NumPy 1.26.4 and SciPy 1.17.1 available on its `PYTHONPATH`, and
choose fresh ignored outputs.

```sh
ATTACH=build/tt-parent-attachment-20261115
POWER=build/8x4-hold-cap-20261107/trial-02/power-dc
"$PINWHEEL_GEOMETRY_PYTHON" -B scripts/streaming_8x4_hold_cap_parent_attachment.py \
  --out "$ATTACH/parent-attachment-replay.json"
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  "$PINWHEEL_GEOMETRY_PYTHON" -B scripts/streaming_8x4_hold_cap_parent_restamp.py \
  --parent-contacts "$POWER/parent-tt0004-projection-resolved-01/resolved.json" \
  --out "$POWER/tt0004-parent-restamp-replay.json"
```

The `tt_um_urish_sic1` phase is used in the illustrative solver input.
It records 1.20 V nominal and 1 Ω independently per resolved source
node. Those values match the earlier sparse diagnostic. The host solve
completed in 6.625 seconds at 745 MiB peak resident memory without
using the native CAD lease. Fabrication remains NO-GO.
[Existing parent intake and static power scope](streaming-8x4-hold-cap-workload-power-20261114.md)
