# SRAM comparison policy qualification

The September 27 continuation qualifies a consistent comparison policy on the
[complete context fixtures](sram-context-results.md). The user authorized the
next gate. Preserve the chip, supplied macro, installed PDK, prior fixtures,
executed recipes and receipts. No new full-chip routing or full-flat SRAM/chip
run is allocated.

Use a private copy of the pinned KLayout LVS deck to make comparison preparation
explicit. Keep extraction geometry and device-recognition rules unchanged.
Reconcile device ownership by flattening the two small extracted/schematic
netlists after extraction, with expanded device counts checked before and after.
Give both sides the same dimensional metal-resistor policy: compare length and
width, retain each resistor separately, and preserve the existing limited
dummy-cell model translation. Do not discard devices or waive a mismatch.

Bind the declared schematic interface before simplification. Reject a missing,
extra, renamed or disconnected declared port and verify the interface again
after preparation. Retain named layout-port checks; explicitly account for the
fixtures' anonymous supply nets rather than inventing GDS labels. Preserve
native comparison results and independently require a completed policy audit.
Neither a zero exit code nor a matching database alone establishes acceptance.

Require the same policy to qualify both deep and flat extraction of all four
fixtures. Retain known open, short, missing-device, physical geometry and
resistor-dimension controls. Include the native discarded-output counterexample
and port-name/connection controls. Unknown active device models, unsupported
inputs and absent audit evidence must fail closed. Test policy ablations where
needed to establish which preparation change resolves each failure.

Keep the qualification local. A passing policy on these cells does not qualify
the full SRAM, supplied analog characterization, final GDS, fast-corner pairing,
timed Lean refinement or complete design iteration. Record a concrete next
larger-block gate only after this fixture policy is qualified.

Use at most two implementation/repair cycles for a failed hypothesis. Allocate
at most 1,800 CAD seconds within the existing 28,800-second campaign, starting
at 8,067.658 seconds. Each invocation is capped at 600 seconds, four CPUs and
6 GiB, with one pinned offline container at a time. Count failures and cleanup.
Freeze inputs and recipes before each launch; retain evidence under
`build/validation/sram-comparison-01/`.
