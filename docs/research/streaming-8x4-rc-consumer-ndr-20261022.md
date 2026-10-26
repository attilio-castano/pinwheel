# Separate block-local NDR consumer correction

The unit-correct consumer failed before extraction: its first MIN/retained
process reported undefined `WIDE_Metal1` and `WIDE_Metal2` nondefault rules, then
the DEF parser failed. No resistance result exists for that attempt. Its original
plan `ae63e1068aa9cb1e0430d18487c727be3154a7e8773a6ffa45813718cd0dd8b6`,
receipts, geometry and frozen producer files remain unchanged.

The exact OpenROAD source intake is
`build/campaigns/8x4-20261022-01/rc-ndr-source-intake-01/manifest.json`, SHA-256
`2731ee9198d7ce32a9033fd3dc35a765bc3244f7fc076962d1788d4ebf2779b6`.
Five original Tcl/C++ files are checked by byte count, SHA-256 and Git blob hash
at `dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`. Public source reads and HOST
preparation ran; no downloaded source or Native tool executed.

`src/OpenRoad.tcl:20–25` explains the failure: an unflagged second `read_lef`
imports only a library once a technology exists. The first `tech.lef` creates
technology; the second `widths.lef` therefore did not install its technology NDRs.
`definNet.cpp:148–157` resolves a block-local rule before a technology rule.
`definNonDefaultRule.cpp:16–19` creates DEF NDRs on the actual block, and its
width/spacing handlers convert DEF integers through `dbdist`. At1000DEF and
1000LEF DBU, widths320/400 and spacing210 represent exactly .32/.40/.21um.

A source detail prevents repeating another parser-only failure:
`definNonDefaultRule.cpp:193–207` requires rules on the routing layers. Each of
the two declarations therefore contains all five actual technology-layer
WIDTH entries. Unused layers retain their exact technology default widths;
only the intended active layer receives the old LEF NDR width and .21um spacing.
No unused-layer spacing override, hard-spacing flag, via policy or physical
shape is introduced.

`scripts/streaming_8x4_rc_consumer_ndr.py` prepares a separately typed owner.
It copies the complete old unit preparation and failed evidence byte-for-byte,
then adds one `NONDEFAULTRULES 2` section before COMPONENTS in a fresh DEF. Removing
that section must recover the original DEF exactly. All148 coordinate pairs,
all17 nets and route references, the unchanged Tcl, technology/widths LEF, model
copies, six corner/policy calls and numerical tolerances remain identical.
Complete file membership, original unit authority, source evidence and old/new
producer hashes reopen before and after execution.

The Native body remains the unchanged six-call `streaming_8x4_rc_consumer.run`:
30seconds/call,210seconds work and300seconds outer,1CPU,2GiB,128MiB scratch.
Root must separately admit the new committed producer under the campaign guard.
No Native execution or numeric pass is claimed by this preparation.

The new HOST reopener first uses the original complete raw SPEF/R arithmetic
reader, preserving every wire/via numerical failure. For all six calls it also
reparses actual `before.def`/`after.def`: units1000, exactly two block-local rules,
all five layer widths, exact active spacings and all17 NDR-to-net assignments.
Missing definitions, wrong widths/spacings, missing layers, altered references,
partial calls, warnings and failed cleanup cannot establish a pass. The separate
Root resource receipt remains mandatory. All qualification flags remain false.

Eight HOST controls pass normally and under `-O`, including real source/fixture
bytes, missing-layer/width/spacing/reference negatives, exact148-pair preservation
and incomplete-prefix rejection. Actual Native parsing and all six numerical
results remain unmeasured.
