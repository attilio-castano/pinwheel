# SRAM extraction context fixtures

The September 27 continuation isolates the internal extraction failures in the
[retained SRAM comparison](sram-extraction-results.md). The user authorized
small fixtures that preserve neighboring physical geometry. Keep the supplied
macro, filled chip, PDK and prior results unchanged. No chip edit or additional
A/B routing attempt is allocated.

Start with `RSC_IHPSG13_WLDRVX8` and `RSC_IHPSG13_CDLYX1_DUMMY`. Locate actual
instances and their ancestor cells, well regions, contacts and resistor markers
in the supplied GDS. Compare isolated cells with bounded neighborhoods or the
smallest useful complete ancestor. Preserve source transforms, polygon coverage
and declared schematic connectivity. A clipped patch with cut devices is a
device-recognition diagnostic, not a complete LVS fixture. Record that boundary.

Separate three questions:

1. Does preserved context change which physical devices are recognized?
2. Do the extracted devices, dimensions and terminal connections agree with the
   supplied schematic under the pinned rules?
3. If a model convention differs, is there a narrow, explicit correspondence
   supported by source geometry and schematic intent, with rejecting controls?

Retain strict native comparison results before any experimental adapter. Do not
waive missing devices, ignore unmatched cells or ports, or discard geometry to
obtain a pass. A resistor-model adapter must preserve connectivity and the
dimensions actually specified in the source; unknown models and missing fields
must reject. Keep open, short, device-removal and resistor-dimension controls
where applicable. Report device recognition separately from complete fixture LVS
and from qualification of the entire SRAM.

Use at most two implementation/repair cycles for a given failed hypothesis.
Stop at a reduced, attributable failure if those controls cannot qualify it.
Do not resume the full-flat chip or SRAM runs that exhausted their earlier caps.

Allocate at most 1,800 CAD seconds within the existing 28,800-second campaign,
starting at 8,028.479 seconds. Each invocation is capped at 600 seconds, four
CPUs and 6 GiB; use one pinned offline container at a time. Count failed probes,
controls and cleanup. Freeze every executed recipe and input before launch and
retain evidence under `build/validation/sram-context-01/`. Prior recipes and
receipts remain immutable. Full SRAM qualification, GDS signoff, compatible
fast characterization, timed Lean refinement and clean physical replay remain
separate gates.
