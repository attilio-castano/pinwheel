# Fixed actual-via-family arithmetic diagnostic

This is a new unexecuted six-call diagnostic. Root alone may commit its new
sources, issue a GO and dispatch Native after independent review. It contains
no FasterCap/FVM work, physical fit, new foundry-corner correlation or timing
promotion. The numerical-conditioning stop remains binding. Full M/private
work has priority; preparation may remain unexecuted at the model cutoff,
25 October 2026 02:38:15 UTC.

The exact final-route census `f4e9a6b4…ca8dd5` identifies four actual named
technology vias (Via1_XY, Via1_YY, Via2_YX, Via3_XY) and three generated block
vias with 2/8/16 cuts. The historical five-fixture experiment did not measure
these names. This packet retains the passing R90 authority
`83feadf5…3d87eb`, its exact original technology, merged ITFs and fixed TYP
rules. Every old producer, result, failure and shared PDK byte is preserved.

## Source mechanism and fixed intervention

At pinned OpenROAD `dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`,
`netRC.cpp:getShapeRC` selects a named tech-via VIARES entry when present,
including with `-lef_res`. Generated `dbVia` objects take
`getViaResistance_b`: mean CUT-layer LEF resistance divided by the actual cut
count. Adding generated names to VIARES would not change this v1 path.

Frozen R90 retains a TYP VIARES table, whose four actual named coefficients
are 9 ohms, and CUT-layer LEF resistance 20 ohms for Via1/2/3. That policy is
retained as the baseline. The source-aligned branch changes only the four
actual named VIARES coefficient tokens and three CUT-layer LEF resistance
tokens to the same existing ITF label's RPV. All other rule/LEF bytes remain
fixed relative to the existing R90 sheet-only local LEF policy. The nested
`sheet_policy` witness describes that unchanged intermediate sheet-only step;
the separately enumerated CUT/VIARES edits describe the final diagnostic input.
Unused table coefficients and unqualified C tables are inert retained context,
not a complete corner model. No cell-corner mapping is introduced.

| Declared policy | Four one-cut named vias | Generated 2 / 8 / 16-cut arrays, ohms |
| --- | --- | --- |
| Baseline, all three sheet labels | 9 | 10 / 2.5 / 1.25 |
| Source-aligned ITF_MIN | 5 | 2.5 / .625 / .3125 |
| Source-aligned ITF_TYP | 9 | 4.5 / 1.125 / .5625 |
| Source-aligned ITF_MAX | 20 | 10 / 2.5 / 1.25 |

These are premeasurement software predictions. Baseline is predicted to fail
42 of 63 ITF via-alignment comparisons; those remain explicit mismatches even
if its separate source-policy prediction check passes. No result is available.

## Exact matrix, geometry and references

Six fixed calls are baseline then source-aligned, each ITF_MIN/TYP/MAX in order.
Every call has 45 nets/90 ports: seven families times 50/100/150um wire-leg
lengths (21 one-via chains) plus eight actual layer/width pairs times three
lengths (24 wire controls). Default named-via widths are .16/.20um as applicable;
PG widths are Metal1 .44, Metal2 1.0, Metal3/4 2.1um. All orientations are N.
The generated families remain `dbVia` definitions and are placed as regular
SIGNAL chains for RCX extraction; this does not test SPECIALNETS extraction.

The independent declarative reference is ideal `Rsheet*L/W` per leg plus
`RPV/cuts`. Full chain totals and analytically identified via residuals are
checked, never fitted endpoint offsets. Wire totals retain 0.1%; via values
retain the earlier `max(.001 ohm, .001*abs(target))` bound. The complete frozen
SPEF parser checks units, exact port membership and every series-graph edge.
The source-aligned branch must pass all applicable comparisons; a partial
prefix, missing family or successful subset cannot pass.

`dbWirePathItr` resets prior extension state after VIA/TECH_VIA. The geometry
therefore explicitly repeats the via coordinate with POINT_EXT0 immediately
after the via, restoring a zero-extension next leg. Every point, layer, NDR,
VIA versus TECH_VIA, cut/enclosure rectangle and endpoint association is
mandatory in the complete public decoder inventory. Foreign opcodes are fatal.
Pre/post DEF bytes must match; post-extraction BTERM annotations must be exactly
the two named/directed/net-bound physical endpoints. Line buffering preserves
failure snapshots. Internal RC-property operands and raw wire byte identity
are not claimed. Declared opcode/annotation sequences remain predictions until
actual Native observation.

Generated cut/enclosure boxes use the integer `dbVia.cpp:create_via_boxes`
algorithm, including array centering. The new source-data intake binds exact
netRC/decoder/shape/parser sources and `dbVia.cpp`, SHA256
`fd37a3dd3f8416852bdf01f309da278652e022728f4946abd6396ce228474a1d`.
Its computed Git blob `9a2002ad7562a0196edcf9cd60f730187601773a` matches the
read-only primary file API observation at the pinned commit. Source data is
neither imported nor executed. Intake02 manifest SHA256 is
`5370e196b42ccf9904996dcedc32740eb46c40d3f7f81ff2ce3c7fcee1d92f00`.

## Resource and evidence boundary

Native is bounded to six calls, 30 seconds each; actual whole work including
terminal input verification is at most 210 seconds, outer guard 240 seconds.
Use one CPU, 2GiB including 128MiB tmpfs, zero extra swap and 95% memory
preemption. Resource/geometry/custody failure stops the suffix. Closed numerical
failures remain in the fixed packet; no retry, fitting or retuning is allowed.
The pinned image/interpreter/executable, full actual revision, copied inputs,
complete raw inventory, all source files and exact Root resource/GO/cleanup
joins remain mandatory. The reader performs no Native work.

Thirteen portable controls pass normally and under Python optimization. They
cover array boxes, complete geometry/decoder/contact membership, candidate and
baseline arithmetic, failure/prefix/work clocks, token-only deltas, complete
SPEF graph rejection, actual writer cgroup schema and an end-to-end synthetic
HOST leaf readback. They do not establish Native availability or correctness.

Preparation03 plan SHA256:
`488bf60e795c82d1c45fd4a05867fe023cbc77b95fdd31b9e4f66e23ba59667a`.
Inert proposal03 SHA256:
`827cd2d4ca7f10841a48b6370c3631c972193bd4d1339c6f8b8c3c87b013f37b`.
There are 52 producer files and 30 prepared input files. Preparations01/02 and
source intake01 are preserved unexecuted/superseded after primary Git-blob
observation, terminal-work/membership tightening and making the reader's
baseline-mismatch flag depend on actual complete measurement. Preparation02's
52 source bytes are retained in a separate HOST source snapshot. No Root GO
exists here.

A pass would close bounded source-policy arithmetic/units transport for these
seven families. It would not qualify contact/spreading resistance, independent
parallel-cut physics, physical process/corner correlation, arbitrary routed
R, capacitance, full via coverage, a full extraction model or qualified timing.
