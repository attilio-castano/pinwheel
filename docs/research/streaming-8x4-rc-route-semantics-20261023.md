# Narrow R-consumer route serialization gate

The original `rc-consumer-ndr-01` remains failed: its frozen worker stopped at
the first corner/policy because `before.def` and `after.def` were not byte equal.
Its six-call numerical experiment did not complete. The new HOST checker does
not change that receipt or its acceptance result.

The exact captured files differ by five redundant `NEW` path headers, one at
each named via. At pinned OpenROAD `dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`,
`definNet.cpp:452–498` inserts the named via and changes the current routing
layer to the opposite end of that via. `defout_impl.cpp:1452–1609` serializes
path/junction opcodes as `NEW` and serializes a named technology via followed by
the next point. The exit layer is therefore already selected when that point
follows the via directly. This explains why an otherwise unchanged path can
lose a repeated same-layer/same-junction header.

`streaming_8x4_rc_route_semantics.py` accepts only the controlled17-net fixture.
It independently rederives all22 positive horizontal segments and their actual
default/NDR widths, five named via identities and exact entry/exit layers and
junctions, two complete block-local NDR definitions, and all34 port positions,
layers and connections. The exact technology LEF is hash pinned. A `NEW` clause
may be removed only immediately after one selected named via, at its exact
exit layer and explicitly repeated integer junction, with a following segment.
Unsupported masks, orientations, taper/width attributes, extensions, branches,
generated vias, duplicate/missing routes and alternate physical facts reject.
After removing only those proven spans, the complete DEF bytes must match.
Thus every other byte, including all nonroute sections, must remain identical.

The two small captured DEF fixtures have individual exact size/SHA256 entries
in `tools/artifact-policy.json`; no category of raw CAD payload is exempted.
The checker tests include actual successful normalization and negative controls
for junction/layer/via/width/NDR/ports/nonroute/unsupported syntax/source changes.
They run on the HOST and execute no CAD or numerical solver.

Source authority is separate and immutable: reader intake manifest
`2731ee9198d7ce32a9033fd3dc35a765bc3244f7fc076962d1788d4ebf2779b6`,
writer intake manifest
`b83762c171b157c8c0de868e9b171e9fc7247ba8873c6b0afd77484a8d042be3`,
writer Git blob `277a7a3475e45679382a147b72d4161d89fd9bdf` and SHA256
`a81f028054a03466ff67755b8bc203adb0ea97b89136efebb92f690ace7eae7d`.
Downloaded source was not executed.

After independent checker review, `streaming_8x4_rc_consumer_semantic.py` and its
independent reader implement a separately typed new six-call experiment. The
initial Native DEF must also equal the exact captured import SHA256
`9d50fc55eff69c38f634f78b7b8b2ce692f068f9592c594a6d670a91c768245b`
in every call. Copied-body tests establish that geometry, policies, resources,
warnings, scheduling and original0.1% R equations/tolerances remain unchanged.
All six actual measurements and raw HOST readback are still required.

HOST preparation01 plan
`b38f0ff0b3ace618a2cd854aaf06b4b18b9eec771de9e7ea7db9e01257e7f65e`
binds57 files and11 producers, including the immutable original failure and both
source intakes. The separate command proposal01 is
`5135b2c03c3906a465310f75654f8880959f49a3ad5c729aa168a88593a3162d`;
launch/reopen proposal01 is
`d53b742d8fc8cbc52e21513c71be53fd2a60a4d81576372123cfc76a7fabd1e2`.
These are HOST preparation, with no Native execution. The exact five command
identity substitutions retain1CPU/2GiB/no extra swap/128MiB scratch,
30s per call/210s work/300s outer limits. The typed HOST closeout reopens exact
Root argv/input seals/exit/cleanup independently of the numerical outcome.
Eight checker, six worker/reader and three closeout HOST controls pass normal
Python and `-O`; independent review found no material blocker.

A possible future length-slope experiment that
cancels a wire-end constant is a separate proposal, never a reinterpretation
of the original0.1% failures. This gate makes no DRC, whole-design, capacitance
accuracy or process-model qualification claim.
