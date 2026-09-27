# SRAM GDS extraction qualification

The September 27 continuation investigates the SRAM boundary exposed by
[final layout checks](chip-finalization-results.md). The user authorized local
continuation. Preserve the filled chip, supplied macro, pinned PDK, container,
all failed results and earlier receipts. No new full-routing A/B attempt,
physical chip edit, changed electrical rule or timing constraint is allocated.

First discriminate hierarchical import from actual geometry failure. Compare
the unchanged SRAM and actual exported chip with only the SRAM's internal GDS
hierarchy flattened during import. Retain the macro boundary, all geometry,
all declared pins, native overlap feedback and extracted circuits. Account for
the extra ground terminal; never delete or alias it solely to obtain a pass.
Inspect the pinned import/extraction rules and raw connectivity evidence.

If supported, qualify a bijective interface spelling adapter for angle/square
bus names and the three power names. Require all 351 declared pins and fail on
unknown, missing or colliding names. Keep the raw extraction. Exercise changed
signal and power connectivity controls before using an adapted whole-chip LVS.
Name any remaining macro internal blackbox boundary. Attempt isolated internal
LVS only with its supplied schematic and explicit device/model conventions;
an interface pass is not an internal transistor proof.

Run at most two repair/control cycles for the same failure. A failed or timed
out comparison remains rejected. Preserve both native reports and wrapper
errors. Stop expanding tool repair if the bound is exhausted; record the
smallest remaining reproducer and required next evidence.

Allocate 1,800 CAD seconds within the 28,800-second campaign, starting at
6,711.725 seconds. Each invocation is at most 900 seconds, four CPUs and 6 GiB;
one pinned, offline container at a time. Count failures and cleanup. Freeze
source identities and recipes before execution; retain artifacts under
`build/validation/sram-extraction-01/`. Final GDS LVS, SRAM internal LVS, fast
characterization compatibility, timed Lean refinement, accepted A/B, clean
replay and submission remain distinct gates.
