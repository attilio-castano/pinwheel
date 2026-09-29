# Final layout checks and the SRAM extraction boundary

The September 27 continuation finishes the repaired chip and verifies that its
electrical and functional improvements survive. **Final GDS signoff is rejected:**
the exported-layout extraction reports 24 illegal overlaps and its LVS does not
match. The same failures occur on the preceding layout, and all 24 overlap
markers reproduce on the unchanged supplied SRAM by itself. This localizes the
next investigation to SRAM extraction and interface qualification.

The [manifest](../../physical/experiments/chip-finalization-results.json) binds
the exact artifacts, failed runs, controls and costs under the
[frozen protocol](chip-finalization-experiment.md). [Status](../research/status.md)
owns the next decision. Neither A nor the complete design iteration is accepted.

## What survived finishing

The input is the exact [five-buffer/one-diode repair](chip-closure-results.md).
The standard flow resumes at fill insertion with empty initial metrics. No new
routing, placement optimization, clock change or constraint relaxation occurs.

| Check | Result |
| --- | --- |
| Original instances and all their terminals | All **12,335** retained exactly, including placement and power binding |
| Original detailed wires | Every raw wire encoding retained; **340 clock nets** included |
| Connected signal/clock wire coverage | **12,191** nets, all wired |
| Original antenna bindings | All **98** retained, including the repair's added diode |
| Added cells | **45,901** signal-free filler/decap cells; **58,236** final instances |
| Saved routing resources | Unchanged, zero overflow |
| Full-rule Magic DRC on exported GDS | **0** violations; full flat import, no macro exclusion |
| Antenna / critical disconnected pins | **0 / 0**; eight unused package inputs remain classified separately |
| Power | Every terminal correctly bound; native analysis reports both power grids connected |
| Independent circuit and package check | Exact pre-fill signal circuit retained; **331,401 edges / 1,517 frames** pass |
| Database/LEF-based LVS control | All seven reported difference/error counts **0** |
| Exported-GDS extraction/LVS | **Rejected**: 24 illegal overlaps and failed top-level pin matching |

Filler/decap adds 491,334.0768 µm², for 867,216.7872 µm² total instance area.
The signal/SRAM/antenna area remains **375,882.7104 µm²**, 4.5942% above the
historical comparison allowance. These are different accounting quantities;
filling existing empty space does not enlarge the 1,289.28 × 710.64 µm outline.
The original six-cell repair still costs 78.0192 µm².

Fresh extraction and an independent STA process bind the filled database,
netlist, constraints and newly produced SPEF. They reproduce the pre-fill
timing results exactly. All setup/hold/capacitance/slew/fanout counts are zero.
Every consumed net has complete parasitic annotation; all 128 unannotated drivers
are independently reconciled to unused signals. All 64 SRAM write holds pass
at each recorded corner.

| Recorded corner | Setup margin | Hold margin | Minimum SRAM write hold |
| --- | ---: | ---: | ---: |
| Fast screen | +10.304851 ns | +0.026979 ns | +0.112677 ns |
| Typical | +7.309177 ns | +0.119130 ns | +0.251519 ns |
| Slow | +1.242753 ns | +0.302933 ns | +0.457890 ns |

The functional check uses the existing standard-cell and SRAM behavioral models.
It rejects inserted hidden state, changed flip-flop clocks and changed antenna
bindings. It is finite pin replay, not SDF simulation or a new Lean theorem.

## What the stronger check exposed

The preceding flow used `MAGIC_EXT_USE_GDS=False`: LVS reconstructed top-level
connections from DEF/LEF. This continuation also tests `True`, so the layout
circuit comes from the actual exported KLayout GDS. It preserves the original
PDK rules, libraries, layout and checking thresholds.

| Control | Extraction overlaps | LVS outcome |
| --- | ---: | --- |
| Repaired chip, exported GDS | **24** | Native report: `Top level cell failed pin matching` |
| Pre-repair third A chip, exported GDS | **24**, exact same boxes | Same native failure |
| Repaired chip, DEF/LEF | **0** | Pass; zero differences/errors |
| Unchanged supplied SRAM GDS alone | **24**, exact boxes after placement translation | Isolated extraction control; no standalone LVS claim |

All overlap markers lie within `memory.storage`, and the old and repaired chip
produce byte-identical extracted SRAM subcircuits. Translating the standalone
markers by the SRAM placement offset, (252, 144) µm, reproduces every whole-chip
marker exactly. This is direct evidence that the overlap reports do not depend
on the six-cell electrical repair.

There are two concrete interface findings:

- The GDS-extracted SRAM uses angle-bracket bus indices and `VDD`, `VDDARRAY`,
  `VSS`; the LEF/logical interface uses square brackets and `!` power names.
  The standalone extraction has all **351** declared pins after spelling
  normalization. This comparison diagnoses naming; no renaming is applied to
  obtain an LVS pass.
- Whole-chip extraction exposes **352** SRAM terminals. Its additional terminal
  is `RM_IHPSG13_1P_COLDRV13_FILL4C2_1[2]/RSC_IHPSG13_FILLCAP4_1/VSS`.
  That extra internal ground terminal is absent from the standalone top-level
  interface. Its origin and treatment must be established before accepting a
  hierarchy or interface adapter.

The overlap types are 20 well-type conflicts and four resistor/metal-type
conflicts. These are extraction feedback, despite passing full-rule DRC.
The controls do not yet distinguish a physical macro defect from an import,
hierarchy or technology-extraction issue. No overlap or extra terminal is waived.

Netgen additionally writes invalid JSON containing an unescaped power-pin name;
LibreLane stops while parsing it. The native text report already rejects LVS,
so repairing the report parser alone cannot make this candidate pass. The raw
JSON and text failures remain unchanged. The configured LVS also treats the SRAM
as a black box on its schematic side; it does not establish SRAM internal LVS.

## Resource use and retained failures

| Invocation | Disposition | CAD seconds |
| --- | --- | ---: |
| Pinned-flow preflight | Configuration and scripts captured | 1.639 |
| Finalization | DRC/timing/power pass; GDS extraction/LVS fail; malformed JSON stops flow | 215.186 |
| Matched old-GDS/current-DEF controls | Reproduce old GDS failure and current DEF pass | 79.479 |
| First independent inspection | Stops on absent output from the failed checker | 2.166 |
| Corrected independent inspection | Uses retained extraction-stage state; geometry, wires, timing, antenna and power bindings pass | 26.280 |
| Standalone SRAM extraction | Reproduces all 24 overlap markers | 20.954 |
| Circuit readback and pin replay | Pass | 41.498 |
| **Total** | **All attempted work included** | **387.202** |

Campaign charge becomes **6,711.725 seconds / 111.86 minutes** of eight hours.
This continuation uses **6.45 CAD minutes** of its 30-minute limit. All receipted
containers are absent. Three A full-routing attempts remain used and two B
attempts reserved; this finishing continuation consumes no additional A slot.

The failed flow never writes a successful `final/` snapshot. The manifest names
the actual completed stage artifacts instead: filled ODB/netlists/DEF, extracted
SPEF and exported GDS. No generated success directory is substituted for the
failed flow. All outputs remain under `build/validation/chip-finalization-01/`;
they are retained local evidence, not a clean-checkout replay bundle.

## Next decision and limits

Retain this filled repair. Qualify the SRAM interface and GDS extraction using
the isolated macro and matched chip controls before further physical edits.
A proposed adapter must account for every declared signal/power pin and the
extra ground terminal, retain connectivity-changing negative controls, and
explain the overlap feedback. If macro internals remain outside the check,
identify the separate evidence that justifies that boundary. Then rerun the
actual exported-layout LVS; do not return to DEF-based LVS and call the gap closed.

Fast logic/SRAM temperatures remain −40°C/−55°C with no qualified joint view.
Complete timed Lean controller/loading/package refinement remains open.
The power-grid result establishes connectivity under the configured analysis;
IR-drop magnitudes use default voltage-source placement and modeled activity,
so they do not qualify package-level power delivery. KLayout DRC, streamout XOR
and whole-flow EQY remain disabled, not passed. Competition admission, accepted
A/B, clean-source physical replay and silicon evidence remain separate.
