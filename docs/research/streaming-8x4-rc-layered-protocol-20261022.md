# Actual ITF M1 layered self and coupling experiment

This is a separate, predeclared experiment. It cannot promote the uniform
development pilot, a full five-metal model or final extracted timing. The
experiment uses exact merged MIN/TYP/MAX ITF fields from the retained primary
source intake at dev `7c783c7c56086511be93bb2097bee656a26148bd`.

The finite-volume reference and finite 3D FasterCap geometry are independently
constructed. They share the declared physical dimensions and materials, not a
mesher, panel list, electrostatic kernel or matrix parser. The FVM extends the
earlier independent one-conductor operator with labelled terminals and separate
unit excitations for the complete two-wire Maxwell matrix. It checks the true
linear residual, maximum principle, energy/terminal flux, cross-energy, matrix
signs, row sums, reciprocity and positive energy. The FasterCap path retains all
native warning, exact names/dimensions, matrix physics and complete-footer gates.

The six physical cases are:

| Corner | Width (µm) | Lateral spacing (µm) | Role |
| --- | --- | --- | --- |
| TYP | 0.16 | single wire | Development self C |
| TYP | 0.32 | single wire | Untuned held-out width |
| TYP | 0.16 | 0.18 | Development coupling |
| TYP | 0.16 | 0.36 | Untuned held-out spacing |
| MIN | 0.16 | 0.18 | Untuned ITF ER corner |
| MAX | 0.16 | 0.18 | Untuned ITF ER corner |

All use M1 bottom 1.04 µm and thickness 0.42 µm. The stack keeps fox, nitride,
dummy oxide, ox1–4, top-metal oxide, nitride passivation and external air. The
reference uses grounded outer boxes at 16/32 µm with 0.04/0.02 µm local steps.
Material interfaces are explicit grid anchors. A separate uniform-limit control
checks the new one-wire construction against the already executed uniform
reference. A planar series-capacitor equation control independently checks
harmonic dielectric integration and the one-time µm-to-m conversion.

The BEM geometry includes a finite substrate ground slab, finite layered prism
and air exterior. All conductor surfaces have an exact closed-volume witness;
every material adjacency tile is emitted once, dielectric reference points are
checked on the declared material side. Physical coordinates are quantized to
binary32 SI metres once, then exactly scaled by 2^20 for the solver. The finite below-substrate
medium uses ER 4.1 as an explicit truncation assumption. These are geometry and
interface witnesses, not bounds on finite-domain error.

Each case declares lengths 10/20/30 µm at ground extension 20 µm, plus lengths
20/30 µm at extension 30 µm. Five manual mesh values are used without auto mode:
0.000383703, 0.000248446, 0.000172698, 0.000086349, 0.0000431745; Galerkin,
GMRES 0.0005, interaction ratio 1. The full native set therefore has 150 calls.
A separately admitted first diagnostic uses only the TYP 0.18 µm two-wire,
10 µm length / 20 µm extension at the first mesh. That single result cannot
satisfy mesh, length, boundary or independent-reference acceptance.

Acceptance requires two consecutive complete matrix changes ≤2%, two length
slopes agreeing within 5%, ground-extension slope changes ≤2%, independent FVM
mesh/domain changes ≤2%, and every ground/self/coupling slope comparison within
10% of its independent fine reference. Coupling error is compared explicitly;
matching diagonal capacitance cannot hide wrong coupling. Held-out cases are
not used to tune geometry, solver settings or thresholds. All six expected
cases and their complete declared meshes/lengths/domains are mandatory for a
limited pilot pass. A partial prefix stays incomplete.

Root owns every numerical execution and the one shared heavy-job lock. The
reference requests 1 CPU / 2 GiB including 128 MiB scratch, at most 25 calls,
120 seconds per call, 1800 seconds work and 1860 seconds outer time. The native
path requests 1 CPU / 6 GiB including 512 MiB scratch, 120 seconds per call,
3600 seconds full work and 3660 seconds outer time. Each uses the pinned offline
CAD image, read-only source/input/runtime mounts, fresh owned output directories,
no extra swap and explicit process cleanup. No measurement occurs during HOST
preparation. Root reviews the exact fresh plan and proposal hashes before GO.

Initial reference preparation 01 and native preparations 01/02 are retained
unexecuted. A HOST negative control found mirrored floating-point endpoints could
make sliver cells at exact material anchors; these plans are superseded before
measurement. The regression reproduces a 4.44e-16 µm interval. The replacement
must retain exact declared anchors without emitting reflected copies of the
same endpoints, and must pass a minimum-interval geometry check before freezing.
The replacement constructs each original endpoint and midpoint once, reflects
only strict interior knots, and rejects every interval ≤1e-8 µm. All 24 HOST
grids now retain exact interface anchors, with minimum interval 0.0166667 µm
and maximum 37,647 nodes. No field equation has been solved during that check.

The replacement reference plan is `rc-layered-preparation-04/plan.json`, SHA256
`185bac5e2f4346aeb03ebda83b827e7fb0336ffbc51c8a0a46f24b4b72aa910c`.
The final finite geometry owner is `rc-layered-geometry-preparation-05`, and the
replacement native plan is `rc-layered-native-preparation-06/plan.json`, SHA256
`6ea3613a03b2c29b8706da76d02e5a4f67ae2f5dc6ff55ddfe5cc1e27b418cc4`.
These paths are relative to `build/campaigns/8x4-20261022-01/`. The three fresh
reference proposal ends `rc-layered-reference-command-proposal-04.json`, while
the native proposals end `rc-layered-{first,full}-command-proposal-05.json`.
The first diagnostic remains required before admitting all 150 native calls.

## Fixed numerical coordinate policy

The pinned FasterCap 3D path does not normalize input coordinates. Its
[refinement criteria](https://github.com/ediloren/FasterCap/blob/b42179a8fdd25ab42fe45527282b4a738d7e7f87/Solver/Autorefine.cpp#L2928-L3002)
compare a potential/field estimate multiplied by normalized panel area to the
manual `m` threshold. Under an exact coordinate dilation by s, conductor
criteria scale as 1/s and dielectric criteria as 1/s². This follows from the
[unit-charge numerical kernels](https://github.com/ediloren/FasterCap/blob/b42179a8fdd25ab42fe45527282b4a738d7e7f87/Solver/Potential.cpp#L2062-L2250).
The area normalization alone does not make manual mesh values independent of
numerical length units; the explicit coordinate scaling branch in
`BuildSuperHierarchy` is limited to the 2D solver.

The initial unexecuted SI-coordinate native plans are therefore superseded.
All thirty cases now use the same declared coordinate unit 2^-20 m, exactly
0.00000095367431640625 m. Every binary32 SI vertex and dielectric reference
point is multiplied by 2^20 and checked for exact binary32 serialization and
exact reversal. Physical capacitance equals raw capacitance divided by 2^20,
once. The geometry owner retains 2,220 coordinate/reference witness rows and
an independent HOST identity readback showing all underlying physical SI input
bytes, conductor bounds and material-boundary witnesses match preparation 02.
The fixed normalization applies to every corner and held-out case before any
measurement. It changes neither physical geometry nor tolerances.

The retained coated-sphere control used this same S20 coordinate policy and
checked `C_physical = C_raw / 1048576` against its analytic enclosure. That
supports the unit/interface seam; it does not establish M1 wire accuracy. The
new ladder values remain an untuned numerical policy and do not assert mesh
equivalence to the historical U. Full matrix refinement, independent references,
length and boundary gates still decide the limited pilot.

The independent HOST analyzer additionally reparses both retained physical SI
files and current emitted S20 files, checks every noncoordinate/material/name
field, and proves exact reversal for every vertex and dielectric reference
point. `rc-layered-S20-independent-readback-02.json` records all thirty cases and
2,220 witness rows passing. Missing witness rows are a negative control. A
separate review repaired two admission seams before measurement: Native leaf
mesh must equal its batch job's declared mesh, and each FVM result must contain
exactly one ordered residual/energy excitation record per declared conductor.
Empty, missing or reordered excitations cannot satisfy an aggregate vacuously.
The uniform-limit control also binds its actual case bounds, uniform material,
fine mesh/domain, plan hash, one ordered excitation, residual/energy/node gates
and positive finite scalar matrix before its capacitance is compared. Wrong
material, omitted excitation, wrong plan/domain or held-out width reject.

Exact primary source bytes and Git blob identities are retained under
`rc-fastercap-scale-source-intake-03/`. Its Autorefine.cpp SHA256 is
`50dd78c1589a244a49bc3a4aca33e8bde696e14ab5853f00648c5a572065b1a8`,
and Potential.cpp SHA256 is
`a9295b2cbc294318b833e4b38af5b7663ece01b123c3a0c8ac4b093d62292858`;
both match the archived runtime build-source identities. Earlier partial source
intakes are retained with an explicit unsupported non-UTF8 AutoPanel.cpp
roundtrip mismatch and are not used to establish these claims. The FVM cases and
tolerances remain unchanged; plan04 adds only exact excitation and uniform-control
payload guards, while native plan06 retains the fixed S20 policy. All earlier unexecuted
plans and committed checkpoints remain preserved and superseded.

Even a full pass covers only the declared M1 self and lateral coupling cases.
It leaves upper metals, every vertical gap, diagonal/shielding/power-wire ranges,
the draft's empirical linewidth/corner construction, generated vias and complete
final consumer annotation open. The
[eight-field coverage ledger](streaming-8x4-rc-coverage-20261022.md) governs the
full extraction-model claim.
