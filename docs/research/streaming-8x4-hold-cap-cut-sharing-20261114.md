# Frozen 8×4 via and decap current sharing

This follows the [Metal1, via and terminal audit](streaming-8x4-hold-cap-metal1-via-terminal-20261114.md)
on the frozen `dc654986…` ODB and `d4cd48f0…` GDS. The earlier analysis
established array and terminal branch currents and identified which physical
cuts they could involve. This audit uses the drawn geometry and signed feed
currents to test how much redistribution the local electrical assumptions
permit. Local rehearsal remains GO. Fabrication remains NO-GO.

## Via feed and resistance controls

The heated-sheet I²C case provides signed feeds for the 48 arrays flagged
in every sparse-source case. The reader reconstructs current from the
full solver voltages and conductances, verifies the rounded current CSV,
and checks conservation at all 96 endpoints. The largest endpoint
imbalance was 6.36 fA. The feeds include 168 same-layer branches, 29 adjacent
via branches and eight external 1 Ω branches. Currents can enter and leave
the same metal sheet, so their net transfer through the array alone does
not specify the local boundary.

Six of the modeled 1 × 1 µm sources overlap the central four cuts of
their Via3 array in projection. The two low-edge VPWR sources sit
1.780 µm to the south. The squares are above Metal4 and current spreads
through that layer before reaching the cut footprints. The greatest
Via3 transfer was 2.898 mA at VPWR (16.400, 663.780) µm. Its 4.957 mA
source feeds that array plus 2.059 mA south along Metal4. The greatest
Via2 transfer was 1.504 mA at VGND (1717.400, 669.400) µm, with feed
from both directions on Metal2 and an adjacent Via1 array.

The IHP reference gives 5/9/20 Ω for Via1–3 chain min/target/max and
0.4 mA per cut at the published lifetime and temperature reference. With
equipotential sheets, peak current through one selected cut is
`Iarray × r / (r + N - 1)`, where `r` is the resistance of the other cuts
divided by that of the selected cut. The comparison below keeps the
rounded-upper array total fixed. It deliberately mixes one 5 Ω cut with
all other cuts at 20 Ω. IHP supplies no local mismatch distribution for
that combination in these tables.
[IHP CMOS5L process specification, §§3.4–3.5](https://github.com/IHP-GmbH/IHP-Open-PDK/blob/2bbec755dc67ca3db0261c3d6163e15735d66710/ihp-sg13cmos5l/libs.doc/doc/SG13CMOS5L_os_process_spec.pdf#page=18)

| Sparse case | Peak Via2, mA/cut | Peak Via3, mA/cut | Arrays above 0.4 mA in this control |
| --- | ---: | ---: | ---: |
| Vectorless, ideal contacts | 0.489 | 0.596 | 14 |
| Vectorless, 1 Ω/source | 0.486 | 0.591 | 14 |
| I²C, 1 Ω/source | 0.480 | 0.582 | 14 |
| I²C, 1 Ω/source, 105 °C sheet | 0.547 | 0.610 | 16 |

The heated-sheet Via3 hotspot reaches the reference at an equipotential
resistance ratio of 2.401, and the Via2 hotspot reaches it at 2.535.
These are model sensitivities. The observed array totals cannot settle
whether the actual cuts differ in resistance by either ratio.

## Spatial via model

The finite-volume model uses the frozen GDS Metal2–4 rail stripes and
via enclosures. Each array has its own two-sheet domain with 0.190 × 0.190
µm cut footprints. Same-layer branches enter at stripe cross sections.
Adjacent-via and explicit source currents enter at their drawn cut
projections and 1 µm source squares, respectively. The model keeps
the signed heated-sheet I²C feeds fixed when changing resistance. It
uses the retained 0.132028 Ω/□ sheet value, based on the LEF maximum
anchored at the prior run's 25 °C baseline. Two lower sheet sensitivities
use the process table's minimum and target at 300 K scaled to 105 °C.
The contact and via values stay fixed with temperature in each solve.

| Resistance on every cut in each array | Peak over all 48, uniform feed density | Peak over all 48, varied feed placement |
| --- | ---: | ---: |
| 5 Ω | 0.204746 mA | 0.236518 mA |
| 9 Ω | 0.192869 mA | 0.212414 mA |
| 20 Ω | 0.190224 mA | 0.195042 mA |

The second column uses uniform density within each stripe or footprint.
The third varies the weight of each mesh cell independently over the
given footprint, preserving the branch total and direction. The adjoint
extrema bound this particular discretized feed family. All 48 arrays stay
below 0.4 mA in the uniform-resistance cases, including the lower sheet
values. No cut reverses direction in these solves.

Each array ran at pitches up to 120, 80, 45 and 25 nm with a 2.300 µm
window half-width. A 2.380 µm window tested the boundary location at
45 nm. From 45 to 25 nm, the largest change in a peak was 0.015 µA
with uniform feed density and 1.125 µA under varied placement. The
larger window changed those peaks by at most 0.010 and 0.521 µA.

Spatially moving a single 5 Ω cut among 20 Ω neighbors at the two
highest-total arrays made every tested placement exceed the reference.
The 8 Via2 placements gave **0.536–0.546 mA** peaks with uniform feeds
and the 16 Via3 placements gave **0.589–0.612 mA**. The largest
discretized feed-placement peaks were **0.548** and **0.644 mA**,
respectively. The fixed-total, two-sheet model leaves local cut mismatch,
three-dimensional current crowding, and actual parent feed geometry open.

## Decap contacts and the ground row

The two selected `decap_8` instances have 12 ground and 18 supply
contacts. The frozen GDS and pinned LVS layer derivations separate
their tap, diffusion and gate polygons. A contact joins only to its
associated lower conductor. The model keeps disconnected lower polygons
separate and imposes the retained net leakage magnitude of about
0.659 nA. It varies the allocation of that load, lower sheet resistance
and the published active and gate-poly contact resistances. The warmed
Metal1 sheet value is 0.17195244 Ω/□, using the original 25 °C anchor
with only the sheet term scaled.
[IHP extraction resistance settings](https://github.com/IHP-GmbH/IHP-Open-PDK/blob/2bbec755dc67ca3db0261c3d6163e15735d66710/ihp-sg13cmos5l/libs.tech/magic/ihp-sg13cmos5l-extract.tech#L62-L119)

Holding the original signed branch currents fixed gave typical peak
individual contacts of **4.019 µA** on ground and **2.502 µA** on supply.
The more conductive, equipotential within-component control reached
**25.386 µA** and **11.400 µA**, respectively. All tested static contact
currents are below the published **300 µA/contact** reference. The
allocated leakage and finite lower sheets are diagnostic assumptions.
The model covers lateral DC redistribution and omits transistor,
well and substrate coupling and transient decap charging.

The ground Metal1 result depends on how the local model is connected to
the rest of the rail. The current-imposed model gave **689.426 µA** on
the 0.440 µm row. Clamping the original native voltages gave **1.760 µA**
there. Those voltages came from a solve with a nearly shorted decap
terminal. Removing that idealized terminal star increased voltage
spread across its attachment points from 1.043 µV to 2.104 mV. The
same control increased the supply hotspot spread from 0.534 µV to
0.677 mV.

The coupled diagnostic removes one idealized decap terminal from each
frozen rail model, then connects the local multiport mesh to the
retained external rail response. The external impedance was positive
definite and reciprocal, and the local conductance was passive and
reciprocal. Existing lumped grid paths remain in parallel with the
new local model. A geometry-resolved replacement of the full local
grid is still needed to qualify the result.

| Coupled static result | Ground hotspot | Supply hotspot |
| --- | ---: | ---: |
| Peak contact current | 3.218 µA | 1.812 µA |
| Peak modeled current through 0.440 µm Metal1 | 597.116 µA | 232.069 µA |
| Ratio to the 440 µA Metal1 reference | 135.7% | 52.7% |

The ground slice is at X = 1565.935 µm, Y = 18.680–19.120 µm near
`FILLER_3_3251/VSS`. It spans the sole connected Metal1 slice there
even with the 5 µm crop halo. The solver integrates both the patch
sources and transfer into the lower components on one side to check
the section current independently. The coupled result changes by
less than 0.005 µA when the halo grows from 0.5 to 5 µm. That is a
local ground-row finding for the retained feed assumptions. Changing
patch radii from 40 to 160 nm gave 134.1–138.5% of the reference on
ground and 51.6–54.7% on supply. Refining the typical mesh from 20 to
10 nm gave 135.9% and 52.9%, respectively. Qualification requires the
actual parent supply boundary and a geometry-resolved grid that
replaces the local paths.

## Evidence

Raw results are kept locally under
`build/8x4-hold-cap-20261107/trial-02/power-dc/`.

| Artifact | SHA-256 |
| --- | --- |
| `via-feeds-01.json` | `4cad8af2c8271f58277efc49202ae20e8b710c5058796fb5eeba768b07a7045b` |
| `cut-parallel-01.json` | `b2e83f983d976237e12da45a818a99cfe2186d48fedd7dd3cf7b16bd08292ec9` |
| `via-cut-mesh-02.json` | `1de60440a87a355f77898c5634b10d5358adcbb2b4316aa4add4a21d5a0874f2` |
| `decap-feedback-02.json` | `d3a92260fc2f9e2f78a0bb994db8d29d44dff137456e3eb2bdaaf4a55e108d78` |
| `terminal-contact-model-03.json` | `9cc5d56517baba208693dbe84670422f2eddcaf4b114d479b2a3e15ce688e7e2` |

Use the retained Python 3.12 precheck interpreter with NumPy 1.26.4,
gdstk 0.9.52 and KLayout 0.28.17-1 as `PINWHEEL_GEOMETRY_PYTHON`.
Make the locally cached SciPy 1.17.1 importable with `PYTHONPATH`.
Point `PINWHEEL_CMOS5L` to the pinned CMOS5L PDK checkout. From the
worktree root, each command writes a fresh ignored receipt.

```sh
POWER=build/8x4-hold-cap-20261107/trial-02/power-dc
python3 -B scripts/streaming_8x4_hold_cap_via_feeds.py --out "$POWER/via-feeds-verify-02.json"
python3 -B scripts/streaming_8x4_hold_cap_cut_parallel.py --out "$POWER/cut-parallel-verify-02.json"
"$PINWHEEL_GEOMETRY_PYTHON" -B scripts/streaming_8x4_hold_cap_cut_mesh.py \
  --out "$POWER/via-cut-mesh-verify-02.json"
"$PINWHEEL_GEOMETRY_PYTHON" -B scripts/streaming_8x4_hold_cap_decap_feedback.py \
  --out "$POWER/decap-feedback-verify-02.json"
"$PINWHEEL_GEOMETRY_PYTHON" -B scripts/streaming_8x4_hold_cap_contact_model.py \
  --pdk "$PINWHEEL_CMOS5L" --out "$POWER/terminal-contact-model-verify-02.json"
```

The analyses bind the frozen input hashes and use the already retained
signed feeds and whole-rail response files at the paths in the table.
The reproduction commands leave the original artifacts and rehearsal
bundle in place.
