# HOST route-material census preparation, October 24

The new adapter can identify design-relevant extraction obligations from a
closed final-view authority. It has not consumed a selected final target. Its
current complete-DEF exercises are development observations, and every model,
corner, qualified-timing and tapeout flag remains false.

`scripts/streaming_8x4_model24_route_applicability.py` accepts only the new
`closed_views` authority. It reopens the certified 8×4 preparation, exact final
ODB, fresh same-ODB `design.def`, complete canonical view inventory, signal/pin
inventory, resolved configuration and certified technology LEF. The latter is
the exact asset
`ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lef/sg13cmos5l_tech.lef`, SHA256
`3edd5a1ad31e8307be537d0d1b85c3258fefeb21aac04aaa476e4f72de4cffd5`.
The configured default-corner selector must resolve to this asset. All inputs
and the complete 63-file HOST source closure are rechecked after parsing. The
new result must be written outside the immutable final-view directory.

The separate pure parser, `streaming_8x4_model24_route_def.py`, consumes every
token in `NETS`, `SPECIALNETS`, `VIAS` and `NONDEFAULTRULES`. It records all net
endpoints and attributes, ordinary and special routed paths, orthogonal
centerline lengths, explicit/default/NDR widths, wildcards, explicit endpoint
extensions, relative and absolute RECT patches, masks, named and generated via
placements, orientation and exact cut counts. A via contributes its two metal
layers to the material footprint even when neither has a wire segment in that
scope. Generated arrays retain their source parameters and ROWCOL cut counts;
the parser does not expand or qualify their individual positions/enclosures.

The grammar is grounded in the retained pinned
[OpenDB DEF writer](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/odb/src/defout/defout_impl.cpp):
generated/explicit vias at lines 389–460, signal wires at 1452–1650 and special
wires at 1653–1840. The retained source has SHA256
`a81f028054a03466ff67755b8bc203adb0ea97b89136efebb92f690ace7eae7d`
and Git blob `277a7a3475e45679382a147b72d4161d89fd9bdf`. The parser rejects
unknown physical tokens, unresolved layer/via/NDR identities, polygonal via
geometry, generated sparse PATTERNNAME occupancy, nonorthogonal routes,
unbound wildcards, malformed records and nonempty conducting FILLS/SLOTS. A
multi-endpoint net with no routed material blocks the final census; a legal
abutment exception would need a separate explicit witness.

Fourteen portable controls pass normally and under `python3 -O`. They exercise
the actual parsing and authority paths using literal LEF/DEF and temporary
files, including repeated cut-layer blocks, generated arrays, NDR/TAPER layer
switching, escaped names and quoted semicolons, wildcard/extension/RECT forms,
unknown physical grammar, exact membership, unit scaling, changed certified
assets/target and missing route material. Indented sections are consumed and
malformed section candidates reject. They read no ignored campaign inputs. An
independent grammar/scope review found no remaining material blocker after
these controls and the exact source were reopened.

## Development-only full01 stage11 observation

The completed stage11 DEF, while the full CAD tail remains unclosed, parsed in
21.5270 HOST seconds with the reviewed parser. Its 43,828,610 bytes have SHA256
`7a55a065eda994064e24eed5349a792ce3059e2db17bbae57eac6b3d9df24565`.
The unadmitted development observation is
`build/campaigns/8x4-20261024-01/model24-route-parser-development-02/observation.json`,
SHA256 `650cedf98e3d08064394018a29e7e5c58e499e2a8f998c797dcc31dc601c43de`.
It retains a source snapshot with SHA256
`79856c1d2c8a285793409ba257db494e931a8a527a704dd8f2f0be915fd3dd72`
and rechecks source/DEF/technology bytes after reading. The earlier development
observation is preserved. Neither observation is a final-view or
model-applicability receipt.

| Parsed routed material | Development observation |
| --- | --- |
| Signal nets / endpoints | 44,604 / 124,109 |
| Signal via placements | Via1_XY 56,282; Via1_YY 68,942; Via2_YX 129,031; Via3_XY 19,216 |
| Generated PG via placements / cuts | via1 array 6,545 / 13,090; via2 array 980 / 7,840; via3 array 980 / 15,680 |
| Signal straight-segment widths | Metal2–4: 200 DBU, with actual DEF scale 1,000 DBU/µm |
| Special straight-segment widths | Metal1 440; Metal2 1,000; Metal3–4 2,100 DBU |
| Routed metal footprint, including via enclosures | Metal1–4 |
| Used NDRs / multi-endpoint nets with no material | None / none |

This exposes why the earlier five named-via fixture names cannot establish
actual-used via coverage: all four observed signal-via names differ from those
five controls, and PG uses generated multi-cut arrays. It also shows the
importance of retaining Metal1 signal via enclosures even though ordinary
signal segments use Metal2–4. No observed TopMetal1/TopVia1 routed material is
an observation about these routed sections, not proof of absence from port or
cell-internal geometry or from electrostatic field context.

The coarse inventory does not compute conductor unions, connectivity validity,
contact/end effects, true path resistance, neighbor spacing, overlap, shielding,
same-net context, dielectric validity, process corners or interpolation ranges.
RECT patch dimensions are not inferred wire linewidths, and centerline lengths
exclude endpoint-extension and patch-area geometry. It therefore leaves all
eight original model-coverage fields unqualified and does not define a complete
precalibration model envelope.

After Root selects a closed target and produces fresh views, the intended HOST
commands are:

```sh
python3 scripts/streaming_8x4_model24_route_applicability.py read \
  --views-report <closed-final-views-directory>/report.json \
  --output build/campaigns/8x4-20261024-01/model24-final-route-census-01.json
python3 scripts/streaming_8x4_model24_route_applicability.py verify \
  --report build/campaigns/8x4-20261024-01/model24-final-route-census-01.json
```

These commands launch no CAD, solver, container or exporter and change no
historical receipt. A successful final census would close only this separately
typed routing-inventory task; the full model and timing gates would remain
subject to their existing independent numeric/source/applicability requirements.
