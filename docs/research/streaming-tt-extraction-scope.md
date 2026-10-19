# CMOS5L extraction model scope

Observed on 2026-10-18 during the twelve-hour streaming TT campaign. This is
an open qualification obligation, not a waiver or a replacement model.

The selected PDK commit is `2bbec755dc67ca3db0261c3d6163e15735d66710`.
Its CMOS5L LibreLane `RCX_RULES` points through `IHP_rcx_patterns.rules` to
the SG13G2 seven-layer model. The resolved file has SHA-256
`ffda02d57a6ecb39b02268be9511d89ef072911f17bd2dcd095f3f3cbeb5a905`.
The CMOS5L tech LEF declares Metal1–Metal4 and TopMetal1; this candidate
restricts signal/clock routing to Metal4 and uses no TopMetal1 PDN drawing.
Neither that routing restriction nor a successful extraction alone proves
the model's vertical-context accuracy.

[IHP Open PDK draft PR #1237](https://github.com/IHP-GmbH/IHP-Open-PDK/pull/1237)
proposes CMOS5L-specific typical, minimum and maximum OpenRCX models. Its
`ffdafdb` change description identifies the inherited SG13G2 symlink as
incorrect for CMOS5L, including the TopMetal1 height. The PR remained a draft
when inspected; the discussion also identifies unresolved process-stack
review. This is evidence of a model qualification concern, rather than
independent validation of the proposed replacement. The draft models have
not been substituted into this campaign's pinned PDK.

OpenROAD's [OpenRCX documentation](https://openroad.readthedocs.io/en/latest/main/src/rcx/README.html)
describes extraction as interpolation from process/corner calibration tables,
including lateral and vertical conductor context. Its
[calibration workflow](https://openroad.readthedocs.io/en/latest/main/src/rcx/doc/calibration.html)
requires comparison with reference extracted patterns. Consequently, the
campaign must keep these claims separate:

- Fresh three-Liberty-corner timing with explicit nominal LEF RC is a global
  routing estimate. Those inputs are recorded and verified natively.
- Actual routed SPEF timing is an extracted measurement only after binding
  the final ODB, model, extractor invocation, annotation and propagated clock.
- Physical timing qualification additionally needs a justified CMOS5L model
  and declared RC corner scope. Nominal RC cannot stand for minimum/maximum RC.

Continue routing, native layout checks and actual-netlist correspondence.
Keep `extraction_model_qualified` false until this obligation has evidence;
do not label the candidate tapeout-ready while it remains open. A later model
selection needs a separately pinned, immutable attempt, with its own rationale,
native extraction/STA and replay, preserving all prior measurements.
