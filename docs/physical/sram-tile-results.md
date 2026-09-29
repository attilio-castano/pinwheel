# SRAM tile width discrepancy isolated

The September 27 experiment identifies a specific obstacle in the supplied
32-bit SRAM tile: **96 physical resistor markers are 0.200 µm wide, while the
reference schematic says 0.260 µm**. Their lengths agree at 0.600 µm. The strict
adapter refuses the source. A separate diagnostic copy changes only those
widths and, after checked model and hierarchy preparation, matches every device,
net and port in both extraction modes. Restoring the original widths fails.

**The supplied tile remains unqualified.** This is evidence about the
layout/reference comparison contract; it does not establish which supplied
view should change or whether a documented model convention explains the gap.
The chip, macro inputs and installed PDK remain unchanged.

The [reviewable bundle](../../physical/fixtures/sram-tile/README.md),
[manifest](../../physical/experiments/sram-tile-results.json) and
[frozen protocol](sram-tile-experiment.md) retain the original inputs, exact
diagnostic recipe and results. [Status](../research/status.md) owns the next gate.

## Physical context and comparison contract

The fixture exports the complete existing `BITKIT_16x2_SRAM` hierarchy: 32 bit
cells and four tap instances. Polygon XOR and text equality pass on all 27
source layers. The source CDL retains both reachable definitions, with only
the fixture boundary type renamed. No transistor geometry is cropped or added.

Deep extraction places the tile's MOS devices at different hierarchy levels
from the schematic. Flattening the two bounded **tile netlists** reconciles
that ownership while preserving the expanded model counts and individual
resistor dimensions. The full SRAM array is not flattened. Each side contains
128 NMOS, 64 PMOS, 64 metal2 resistors and 32 metal3 resistors.

The three source resistor definitions repeat in every bit cell:

| Definition / endpoints | Physical marker | Native class | Source W × L | Physical W × L |
| --- | --- | --- | --- | --- |
| R0: BLT_BOT–BLT_TOP | 10/29 inside metal2 | `res_metal2` | 0.260 × 0.600 µm | 0.200 × 0.600 µm |
| R1: BLC_BOT–BLC_TOP | 10/29 inside metal2 | `res_metal2` | 0.260 × 0.600 µm | 0.200 × 0.600 µm |
| R2: RWL–LWL | 30/29 inside metal3 | `res_metal3` | 0.260 × 0.600 µm | 0.200 × 0.600 µm |

Every marker is rectangular and wholly inside its conductor. Independent
native extraction reports the same dimensions and corresponding endpoints.
The dimensional adapter requires agreement before translating `lvsres` to the
two native classes. It refuses the original source with
`SOURCE_GEOMETRY_DIMENSION_MISMATCH: R1`.

The diagnostic changes exactly three width tokens, then applies the checked
model translation. It retains every MOS parameter, node and resistor length.
Width and length remain compared; resistance value and analog characterization
are outside this contract. Resistors cannot combine or disappear. Forty-two
original top-owned conductor labels bind the declared ports: eight on metal2
and 34 on metal3. The source connections justify `VDD!` → `VDD_CORE` and
`VSS!` → `VSS`; no wire is reconnected.

The pinned extraction deck derives metal resistor bodies from conductor/marker
intersections. General IHP [LVS resistor documentation](https://ihp-open-pdk-docs.readthedocs.io/en/latest/verification/lvs/04_05_res.html#lvsres)
also describes dimensional comparison. That SG13G2 documentation is not a
version-specific interpretation of this SG13CMOS5L SRAM. The inspected material
does not establish a justified 0.260-to-0.200 µm normalization for this tile.

## Measured results and fault sensitivity

The initial causal comparison and packaged control run agree:

| Comparison | Deep extraction | Flat extraction |
| --- | --- | --- |
| Width-corrected diagnostic | Native pass; database match | Native pass; database match |
| Same model preparation, original widths restored | Native failure; database mismatch | Native failure; database mismatch |
| Geometrically unchanged mutation carrier | Native pass; database match | Native pass; database match |

Each positive matches **288 device pairs, 182 net pairs and 42 pin pairs**,
with no ambiguous matches. The packaged run has four positive comparisons and
**42 fault rejections: 30 native mismatches and 12 explicit policy refusals**.
Crashes and unexplained failures do not count as fault detection.

Faults cover single-bit opens/shorts, missing MOS/resistors, wrong or unknown
metal models, width/length changes, equal-resistance-ratio dimension changes,
word-line swaps, missing declared ports, physical metal opens/bridges, missing
gate geometry, and missing/swapped/off-metal physical labels. Single-bit source
faults clone one leaf and leave the other 31 cells unchanged. Physical geometry
edits affect the shared bit-cell definition's 32 placements; independent
whole-tile XOR confines each edit to its intended layer. Label faults leave
polygons unchanged. Seven incomplete-evidence cases and 13 malformed or
unsupported adapter inputs also refuse.

One auxiliary fault-area field in the frozen runner was computed from a live
geometry view after mutation and incorrectly reports zero. It never controls
acceptance. The separately reloaded GDS confirms the original whole-tile XOR
and records the correct local/whole-tile areas: metal open 0.008/0.256 µm²,
metal bridge 0.012/0.384 µm², missing gate 0.039/1.248 µm². The original receipt
and explicit readback correction are both retained.

## Budget, reproducibility and next gate

Four bounded offline invocations cost **86.455 CAD seconds**, including cleanup:
inventory, causal width comparison, packaged controls and independent audit.
They contain 52 native LVS comparisons. All source hashes remain unchanged and
all receipted containers are absent. Campaign total is **8,390.384 seconds /
139.84 minutes**, within eight hours; three A routes remain used and two B
routes reserved. Raw logs, databases and audits live under
`build/validation/sram-tile-01/`; the manifest pins them, but those ignored
artifacts are not supplied by a fresh checkout. The tracked bundle reproduces
the diagnostic with the pinned tool and PDK inputs.

**Next settle the exact width contract.** Establish whether these supplied
GDS/CDL/deck versions intentionally use different width conventions or contain
an inconsistent reference. Any accepted correction or interpretation needs
source provenance and must retain the demonstrated wiring, dimension and
physical-fault sensitivity. The passing counterfactual is a concrete test of
a proposed interpretation, not permission to waive the discrepancy.

Then qualify the recorded array-edge and control contexts and repeat the
hierarchical macro comparison. Macro connection-fault sensitivity still needs
a passing macro positive control. Full SRAM/GDS signoff, the prior Magic
diagnostics, compatible fast views, complete timed Lean refinement, accepted
A/B and clean-source replay remain open. This experiment advances the complete
design iteration by turning an opaque comparison failure into a small,
reproducible source-contract question.
