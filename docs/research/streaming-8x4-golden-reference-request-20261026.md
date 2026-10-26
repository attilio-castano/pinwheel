# Proposed golden-reference and corner oracle contract

This is a local data request and admission contract, not an accepted reference
package. No external contact, experiment or model-generation run is authorized
by it. **G2 is not admitted; all eight coverage rows and qualified timing remain
open.** Preserve f516 and its existing G4/G5 evidence.

The fixed ODB is
`f516ffbca3cd86e5cd214c515ca0be457a91a517dbe715caa47336aec907eee0`.
The completed nominal reference component is independently reopened at
`rc-reference-composite32-independent-audit-01.json`, SHA256
`4d75e83da017dcd6b810f3e0062ea8b19bed62fca53f9e1d0ddcbc04f2936c32`.
It binds the canonical composite authority
`00e7efa944330f70a9a9b321ab6334c811ba1e38118541e3922d75fe2e6eac99`:
32 grids, eight nominal TYP 2D cases, complete one/two-conductor matrices,
maximum mesh change0.983710% and domain change0.853374%, both below2%.
Old27 and fresh5 remain separately identified; original timed-out027 is still
failed. This supplies empirical nominal comparisons, not physical material,
finite-wire, foundry-corner or actual-route qualification.

## Requested immutable package

Supply one manifest with regular-file path, SHA256, byte count, provenance and
units for every item below. Retain native raw results and command/configuration
records, not just a summary spreadsheet. Identify the trusted reference tool,
version/binary and deck, or measurement/metrology procedure and calibration.
State which independent evidence validates its physical assumptions and error
bounds. Independence from the candidate OpenRCX tables/importer and their
training data must be explicit; a second run of the same model is not an oracle.

1. **Physical stack and contacts.** Exact CMOS5L conductor elevations,
   widths/thicknesses, dielectric boundaries/permittivities, substrate and outer
   boundary conditions, contact planes and via/cut geometry/resistance. Identify
   included cell/pin/internal conductor material and justified exclusions.
   Nominal ITF transcription alone does not establish physical accuracy.
2. **Corner authority.** Source-defined physical parameter variations and their
   correlations for every declared RC corner; exact corresponding process,
   technology LEF and reference deck. Supply an explicit, justified RC-to-cell
   Liberty corner pairing table. Names such as MIN/TYP/MAX are identifiers,
   not proof of foundry correlation. Do not invent missing tolerances or map
   one nominal deck to three cell corners by name.
3. **Frozen query universe.** Before calibration or revealing held-out values,
   bind the exact final ODB/views, consumer binary/options and complete
   route-relevant geometry/context requests. Include regular and SPECIALNETS
   wires/vias, widths/NDRs, end extensions, bends/branches/patches, layer pairs,
   offsets/overlaps, same-net/other-net/PG roles, shielding and cell/port context.
   The abstract census alone does not yet establish all these contexts. Every
   exclusion or interpolation region needs a physical error/applicability bound;
   no arbitrary neighbor radius or unobserved far-field assumption is accepted.
4. **Training and untouched tests.** Commit geometry/material/terminal recipes,
   membership, split and numerical protocol before calibration. Record all
   previously measured development cases. New heldouts must be disjoint from
   fitting/tuning and must cover applicable range boundaries and contexts.
   Existing value-free recipes may be used only after their freshness and
   disjointness are checked; old failures are never renamed fresh heldouts.
5. **Golden values.** Per case/corner, retain absolute R/via values and complete
   signed Maxwell C matrices, conductor names/order, grounded/floating terminal
   conventions, reference planes, units and precision/error information. Keep
   diagonal, ground-row sums and every coupling entry. For finite-length slopes,
   provide all declared lengths and end/boundary variants, not a fitted slope
   alone. For consumer checks, supply complete golden SPEF/net/R/C/via topology,
   units, node naming and passive-load conventions.

## Eight coverage obligations

| Row | Required oracle and actual-consumer check |
| --- | --- |
| Resistance | Full physical width/contact/end-face model and applicable bends, junctions and segments; compare complete actual net graphs. Existing90 ideal end-face controls are a software/reference component. Preserve earlier absolute failures; no fitted endpoint subtraction. |
| Ground capacitance | Complete finite-stack terminal matrices and ground convention, finite ends and applicable surrounding conductors/materials. Compare ground-row sums and length slopes, not only diagonals. |
| Coupling capacitance | Nonzero/zero values justified for applicable same-layer/vertical/offset/multiconductor contexts. Validate actual importer slot, distance/width dispatch and callback summation on every used branch. Synthetic projection controls do not supply physical coefficients. |
| Via resistance | Actual named and generated cut/enclosure structures, contacts/spreading and parallel-cut assumptions, including applicable SPECIALNETS behavior. Source-aligned LEF arithmetic is distinct from physical reference accuracy. |
| Dielectric interfaces | Full applicable material/boundary stack and its variation; explicitly resolve substrate, excluded process/cell material, finite ground and air assumptions. The 2D component checks only its declared nominal stack. |
| Layer coverage | Every applicable layer/pair/via plus cell/port/field context. Absent TopMetal1/TopVia1 routed footprint does not alone prove absence of their electrical influence. |
| Width/spacing range | Complete declared actual-query membership, offsets/overlap/end/context dimensions and independent interpolation/error witnesses. Out-of-envelope queries fail; no extrapolation or point-pilot promotion. |
| Consumer units/semantics | Complete golden R/C/via graph, units applied exactly once, named matrices/ground versus coupling conventions, full annotations and exact per-corner rules/LEF/process/consumer policy identity. |

## Existing numerical gates remain exact

Complete ordered case/excitation/matrix membership; positive diagonal,
nonnegative full row sums, nonpositive off-diagonals and positive-definite symmetric part; BEM
reciprocity≤1%. Reject warnings/errors, timeouts, missing rows and fallback.
Require two successive BEM mesh comparisons≤2%, length-slope consistency≤5%,
ground-extension≤2%, independent-FVM mesh/domain changes≤2%, and independent
physical C comparisons≤10%. Retain FVM true residual≤1e-9, energy/flux≤1e-7
and reciprocity≤1e-7. R/via relative limits remain0.1%, including the original
via residual bound max(0.001ohm,0.001×reference) where applicable. These are empirical admission
criteria, not newly claimed rigorous continuum error enclosures.

The exact case membership, protocols and original per-case gate definitions
remain authoritative. This request neither relaxes those definitions nor adds
unmeasured results. All declared corner/case/heldout observations must be
complete and independently reopened. Budget the exact workload before launch;
the generic27,900-solve regeneration is not admitted by this document.

## Admission and bounded fallback

First validate package provenance, independent accuracy authority, corner
relationships and the complete frozen applicability universe. Only then may
Root admit one bounded transport/consumer validation sequence: close exact
unit/import/context dispatch; compare all declared consumer R/C/via outputs
with untouched references; verify final-route applicability; then construct
the immutable bundle and actual typed
`streaming_8x4_closure48_model_authority.closed_authority` endpoint. The endpoint
must reopen all raw evidence and original eight-row gates. File presence,
synthetic controls, nominal references and manually asserted flags cannot
substitute for that authority. Qualified timing/ECO remains blocked until then.

At the four-hour decision, missing physical/corner/reference authority means
**no full model regeneration or conditioning**. The measurable fallback is the
closed nominal2D component, complete available abstract/query inventory with
unsupported contexts listed, source-bound consumer semantic controls, and an
exact missing-data ledger/request. Preserve G2/G3 as open. This is component
progress, not full or predefined partial tapeout closure. Any later physical
variant requires fresh affected G4/G5 and model applicability on that target.
