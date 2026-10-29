# Proposed separate R length/width study

Status: proposal only. No new producer, preparation, measurement or Native
authorization is implied. The completed original six-call result remains
failed:72 absolute wire failures and30 passing named-via differences.

The useful next question is whether the slope is width independent while an
endpoint term changes the absolute resistance. Existing default-width50/100um
observations support that mechanism; the single wide100um point cannot
measure a wide slope or test linearity. A third length also provides a heldout
prediction rather than a two-point fit that is automatically linear.

Use a new controlled26-net fixture: seven wire families (all five default
widths plus M1.32um/M2.40um) at50/100/150um, plus the same five named-via
chains and matched50um wire controls. Exact1000DBU,52 ports, no cells,
no generated vias. The two proven block-local NDRs declare all five layer
widths and active spacing. Keep the original process tables, version1.0,
via names, corner identities and warning policy. A new limited census must
bind every actual segment/width/port/via/NDR fact and admit only the already
source-proven redundant via-exit NEW clauses; the frozen17-net checker is not
silently widened.

Run a fixed six calls: MIN/TYP/MAX × two separately declared policies:

| Policy | Purpose | Exact delta |
|---|---|---|
| Baseline rules |Measure three actual wide lengths and replicate default slopes |Original retained rules, original LEF, `_lef_res` disabled |
| Width-aware candidate |Test explicit actual-width scaling while keeping the shared PDK immutable |Add `-lef_res`; generate a local per-corner LEF changing only the five ROUTING `RESISTANCE RPERSQ` values to exact pinned ITF sheet R |

The candidate's LEF adapter must reparse all five original routing fields,
bind each generated value to the selected corner's pinned ITF conductor RPSQ,
and prove every other byte identical, including all widths, shapes, cut-layer
fields and explicit named-via resistances. The shared PDK is untouched. The
new policies and local LEF identities belong to new schemas and resource seals.

Predeclare the observations before execution:

- Record every original-style absolute `RPSQ*L/width` residual, retaining any failure. The old0.1% absolute gate is never promoted by this study.
- For every wire family, compute both50→100 and100→150 slopes, each against the selected ITF `RPSQ/actual_width` with a separate0.1% slope threshold; require their mutual relative difference at most0.1%. For the heldout150um check, require its raw R rounding interval to overlap `2*I100-I50`. At `extSpef.cpp:1111`, resistance is printed with `%g`: for each nonzero raw resistor value `v`, use the explicit rounding half-width `0.5*10^(floor(log10(abs(v)))-5)` and sum edge intervals. This is only a serialization rounding allowance, not a physics/error enclosure. Report all intercepts; do not fit away them before the absolute audit.
- Compare actual baseline/candidate wide-to-default slope ratios. Source predicts a baseline ratio near1 and candidate ratio near0.5 at doubled width. Treat these as hypotheses to measure, not evidence already obtained.
- Recompute all five named-via differences in every call from matched wire controls. Source in `netRC.cpp:305–350` handles explicit via resistance/model overrides separately from wire `_lef_res`; therefore candidate named-via behavior must be measured. Preserve retained LEF targets20/20/20/20/4ohm as explicit controls, and refuse unexpected fallback or VIARES behavior.
- Require complete ordered six-call execution, full raw SPEF graphs, exact geometry/source/runtime custody and exact Root process cleanup. No retry, subset, corner waiver or successful-prefix authority.

Retain the tested bounds: one CPU,2GiB, no extra swap,128MiB scratch,
30s per call,210s work,300s outer. Actual runtime is unknown for the new
fixture; the earlier17-net six-call batch took4.331s, which is only a sizing
observation. Any launch needs a reviewed new producer, focused controls,
fresh preparation/proposal and Root GO.

Success would establish only a small version1 R-consumer length/width seam
and measured behavior of five named technology vias. It would not qualify
the draft capacitance tables, all widths/spacings/vias, process corners,
full CMOS5L model, physical closure or extracted design timing.
