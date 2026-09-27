# SRAM interface checking and the remaining internal LVS gate

The September 27 continuation establishes a passing **351-pin SRAM boundary
comparison on the actual exported chip GDS**, with native rejection of signal
and power wiring faults. **Full GDS signoff remains rejected.** The comparison
uses the existing schematic SRAM blackbox; internal extraction still has errors,
and the independent PDK SRAM layout/schematic check does not pass.

Retain the filled chip and the checked spelling adapter. The remaining task is
SRAM/PDK extraction qualification using small context fixtures, before another
chip layout change. No chip geometry, netlist, routing, PDK rule, timing
constraint or area changed in this continuation.

The [manifest](../../physical/experiments/sram-extraction-results.json) binds
the recipes, exact sources, native reports, negative controls and failed runs.
The [protocol](sram-extraction-experiment.md) was frozen before execution;
[status](../research/status.md) owns the active decision. The prior
[finalization failure](chip-finalization-results.md) remains a historical result.

## What was qualified

The original extraction exposed a 352nd SRAM terminal with an internal ground
name. An audit of the raw `.ext` merge records places it in the same **169,408-node
equivalence class** as chip `VGND`, the SRAM's declared `VSS!`, and substrate.
It is outside the `VPWR` class. The record retains explicit merge-line witnesses;
this observation does not justify deleting a terminal.

Flattening only SRAM control descendants during GDS import removes that extra
terminal naturally. The macro now has exactly the 351 declared LEF pins. The
adapter changes **338 bus-pin spellings** from angle to square brackets, preserves
their order and references, and validates a bijection against the LEF interface.
It keeps the existing native power-name convention. No terminal or connection is
dropped, and no ground alias is inserted.

| Boundary check | Result |
| --- | --- |
| Adapted exported-GDS circuit versus filled powered netlist | Native **`Circuits match uniquely.`**; all seven LVS difference/error counts zero |
| Devices / nets in each compared top circuit | **12,337 / 12,313**; eight unused package inputs remain disconnected |
| SRAM address bit 0 deliberately tied to ground | Native top-level pin matching fails |
| SRAM ground deliberately tied to power | Native top-level pin matching fails |
| Missing, duplicate, unknown or colliding interface pin | Adapter rejects all four cases |

Netgen's malformed JSON bug recurs on both deliberate failures. Their native
text reports already reject the wiring, so the rejection does not depend on
JSON parsing. The positive report parses normally. The SRAM's schematic is
still a blackbox: this pass establishes its integration boundary, not the
correctness of its internal transistors.

## What hierarchy changes explain, and what they do not

All comparisons use the original supplied macro, actual exported GDS, pinned
container and unchanged PDK. The altered Magic recipe adds `gds flatglob` entries
before import; the macro boundary remains present.

| Import/control | Illegal overlaps | Conversion diagnostics | Disposition |
| --- | ---: | ---: | --- |
| Original standalone SRAM | 24 | 522 | Rejected historical control |
| Original chip | 24 | 522 | Rejected historical control |
| All 139 SRAM descendants flattened, standalone | **0** | **0** | Removes overlap/conversion errors; 1,024 edge-device warnings remain |
| All SRAM descendants flattened, chip | No final result | No final result | Stopped at the 600-second limit; no accepted output |
| 120 control descendants flattened, 19 array cells retained, standalone | **2** | **438** | Rejected extraction |
| Same control import, chip | **2** | **438** | Boundary LVS passes after spelling adaptation; extraction remains rejected |

The conversion diagnostic is `Number of subscripts doesn't match`. It was
already present in the original reports and is an additional reason not to
infer macro correctness from a zero LVS count. The remaining two overlap boxes
are metal2/resistor-metal2 conflicts in the SRAM. No extraction error is waived.

The pinned import rules derive p-well geometry using neighboring well shapes
and distinguish metal from resistor-marked metal using Boolean layer operations.
The measured sensitivity to import hierarchy supports an extraction problem;
it does not by itself prove that every physical SRAM connection is correct.
[Magic's GDS documentation](https://opencircuitdesign.com/magic/commandref/gds.html)
describes this import operation and its interpretation of layout through the
technology rules.

An independent geometry audit compares the supplied macro with the macro inside
the exported chip: polygon XOR is empty on **all 32 layers**, and all **754,685
text labels** retain their names and transforms. Thus this is the same physical
macro in both checks. This is a macro-only audit, not a whole-chip streamout XOR.

All **1,024** full-flat missing-terminal warnings locate uniquely on actual
poly/diffusion gate intersections in **512** supplied edge cells, exactly two
per instance. The CDL also instantiates 512 such cells and defines both devices
with source, drain and bulk on `VSS`. This accounts for the warning locations and
intended terminal ties; it is not an internal LVS pass. The first audit attempt
used an unavailable API method; the second exposed overlapping cell bounding
boxes. Both failures are retained. The final audit uses actual gate geometry.

## Independent SRAM check

The pinned PDK's KLayout LVS deck compares the **unchanged standalone SRAM GDS
against its supplied CDL schematic**, using strict port matching and default
device checking. No unmatched-port, implicit-connection, tap-removal or cell-ignore
option is added. Its hierarchical comparison completes and reports that the
netlists do not match. The matched flat-mode control stops at its **400-second
limit before a comparison verdict**; it is incomplete, not a second measured
electrical mismatch.

The native hierarchical report identifies `RSC_IHPSG13_CDLYX1_DUMMY` and
`RSC_IHPSG13_WLDRVX8` among the failing cell comparisons. For the word-line driver,
the extracted subcircuit contains two PMOS devices while the supplied schematic
has those two PMOS plus two NMOS devices. This is a concrete reduced diagnostic;
context-dependent device recognition remains to be established before calling
it a physical defect. The full native cross-reference is retained separately
from the chip boundary comparison.

Native database readback gives **23 matching cell pairs, two nonmatching pairs,
five schematic-only mismatches and a skipped top-level comparison**. The delay
dummy has matching NMOS/PMOS classes but different resistor models: extracted
`res_metal1` versus schematic `LVSRES`. The other mismatch is the word-line
driver above. The five schematic-only cells are `CBUFX8`, `CINVX2`, `CINVX8`,
`FILLCAP4` and `FILLCAP8` under the `RSC_IHPSG13_` prefix. These inventories
describe the saved comparison, not a count of defective physical cells.

IHP's [historical SRAM LVS issue](https://github.com/IHP-GmbH/IHP-Open-PDK/issues/239)
also names the delay dummy cell, but covers other macros and an older PDK commit.
It is supporting context, not evidence that this candidate is correct or that
our complete failure has the same cause.

## Next gate and retained boundaries

Build a small SRAM context fixture around the failing word-line driver and
delay cell. Preserve the actual neighboring well, contact and resistor-marker
geometry, and compare it with the supplied schematic under a qualified device
recognition and resistor-model contract. Keep open/short/device-removal and
resistor-dimension controls. A tiny cell
without the well geometry provided by its neighbors is not a sufficient control.
Require a complete strict SRAM result, or explicitly justified supplied-IP
qualification evidence, before accepting the blackbox boundary for signoff.

The two Magic repair/control cycles and two independent SRAM comparison modes
are retained; broad flattening is not extended indefinitely. No fourth A route
or B attempt is allocated. Positive timing/electrical, full-rule chip GDS DRC,
antenna, power continuity and package replay remain bound to the unchanged
[filled chip](chip-finalization-results.md). Fast characterization compatibility,
timed Lean controller/loading/package refinement, accepted A/B, clean-source
replay and competition admission remain open. The evidence is local under
`build/validation/sram-extraction-01/`; it is not a clean-checkout replay bundle.

## Resource use and verification

| Invocation | Outcome | CAD seconds |
| --- | --- | ---: |
| flat-01 | All-descendant import; standalone completes, chip times out | 604.162 |
| flat-02 | Control-descendant import; both complete with residual extraction errors | 168.214 |
| geometry-01 | Geometry audit; instance API mismatch | 25.204 |
| geometry-02 | Geometry audit; cell bounding boxes prove ambiguous | 24.921 |
| geometry-03 | Geometry and actual gate-location audit passes | 25.628 |
| interface-01 | Positive boundary LVS and signal/power negative controls pass | 7.930 |
| internal-01 | Strict hierarchical SRAM comparison returns mismatch | 37.059 |
| internal-02 | Strict flat SRAM extraction times out before comparison | 404.238 |
| lvs-readback-01 | Saved native report readback; accessor API mismatch | 9.444 |
| lvs-readback-02 | Native comparison inventory readback passes | 9.954 |
| **Total** | **All failures, timeouts and readbacks included** | **1,316.754** |

This uses **21.95 CAD minutes** of the 30-minute continuation allocation. The
campaign total is **8,028.479 seconds / 133.81 minutes** of eight hours. Three A
full-routing attempts remain used and two B attempts reserved. All receipted
containers are absent; the source and PDK identities remain unchanged.

The record audit checks every bound recipe/report, reconciles the full cost
ledger and validates documentation links. The executed controls are the relevant
checks for this experiment; no Lean source or chip implementation was changed.
