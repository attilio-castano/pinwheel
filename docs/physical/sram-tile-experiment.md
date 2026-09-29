# Bounded 32-bit SRAM tile qualification

The user authorized the next gate after the hierarchical macro diagnostic.
Qualify the complete supplied `BITKIT_16x2_SRAM` tile: 32 cells with their four
tap instances, original neighboring geometry, labels and transforms. Start
from campaign **8,303.929 CAD seconds**. Preserve the chip, installed PDK,
supplied macro, previous fixtures, recipes and receipts.

Export the whole existing tile hierarchy, not a clipped transistor drawing.
Verify every source/export polygon layer and text, retain the source CDL's
reachable definitions, and change only the fixture boundary type name where
needed. Inventory resistor markers, conductor layers and extracted terminals
before proposing the three bit-cell resistor model correspondences. Require
the source nodes and length/width to agree with those physical witnesses.
Translate only the demonstrated metal2/metal3 instances; reject unknown models,
extra/missing parameters and unsupported geometry. This is dimensional LVS,
not resistance-value or analog characterization.

Apply the qualified physical-port and device-preserving preparation principles
to this bounded fixture. Reconcile hierarchy ownership inside the tile only,
preserve all expanded devices and individual resistor dimensions, and bind all
42 declared ports to original top-owned physical labels. Account explicitly
for the tile's `VDD!` to `VDD_CORE` and `VSS!` to `VSS` boundary spellings after
checking their source instance connections. Do not delete inconvenient ports,
join wires implicitly, discard devices, waive errors or invent GDS labels.

Require positive comparisons in both deep and flat extraction. Then test
schematic wiring, missing devices, resistor models/dimensions, physical metal
opens/bridges and port identity/binding faults. A native final pass, matching
database, complete policy audit and physical/source identity checks must all
agree. A crash, process exit zero or mismatch without a passing positive
control is not qualification. Preserve ablations needed to identify the cause.

Use at most two implementation/repair cycles per failed hypothesis and at most
**1,800 CAD seconds**, within the existing 28,800-second campaign. Each offline
pinned container invocation is capped at 600 seconds, four CPUs and 6 GiB;
one container at a time. Freeze inputs/recipes before running, count failures
and cleanup, and never overwrite an executed output directory. Raw evidence
lives under `build/validation/sram-tile-01/`.

No full SRAM/chip flat extraction, other control-block qualification, new A
route, chip/installed-PDK edit or publication is allocated. This local result
cannot by itself close macro wiring, prior Magic diagnostics, fast-library
compatibility, timed Lean refinement, accepted A/B or clean-source replay.
