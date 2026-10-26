# Complete six-call R consumer result

The new `rc-consumer-semantic-01` completed all six declared corner/policy
measurements, but **failed the unchanged numerical gate** (outer exit2,
4.331s). Exact Root command/input/process cleanup and independent HOST raw
readback closed. The original unit/NDR byte-gate failures remain unchanged.
No HOST readback launched Native.

| Gate | Observed result |
|---|---|
| Exact imported DEF and complete physical invariance |6/6 pass:17 nets,22 segments,5 named vias,34 ports and actual NDR widths/bindings per call |
| Original0.1% absolute wire-R controls |72/72 fail |
| Original named-via difference controls |30/30 pass; maximum absolute error0.00008ohm |
| Composite via consumer gate requiring default wires |Failed, because its mandatory default-wire controls fail |
| Whole consumer / process model / extracted timing |Failed / unqualified / unqualified |

All five default-width layers have an additive offset in total resistance.
The two measured lengths permit a posthoc slope and intercept diagnostic:

| Layers | Intercept, MIN/TYP/MAX (ohm) | Largest default50→100um slope error versus ITF |
|---|---|---|
| Metal1 |0.085 /0.110 /0.135 |0% |
| Metal2–Metal4 |0.073 /0.088 /0.103 |0.046364% |
| TopMetal1 |0.015 /0.018 /0.021 |0.000172% |

For example, MIN Metal1 gives26.6475ohm at50um and53.21ohm at100um,
versus the original targets26.5625/53.125ohm. Both absolute gates fail;
their difference has the ITF slope0.53125ohm/um and a0.085ohm intercept.
These posthoc observations do not introduce a new pass gate.

Wide Metal1(.32um) and Metal2(.40um) were measured only at100um. Their total
R remains about twice the width-aware ITF target: relative errors100.64% for
M1 and100.7068–100.8% for M2. Actual DEF census verifies the wide widths, so
this is not a missing NDR import. One wide length cannot independently
separate its slope from its intercept.

The pinned source supports a more precise mechanism than a generic
width-table clamp. In `extmain.cpp:242–306`, `getResCapTable()` uses the
technology layer's default width and caches one resistance-per-length value
per layer/model. `getLefResistance()` at357–376 multiplies that cache by length
and divides by actual width only if `_lef_res` is enabled. This experiment
does not enable it. In `netRC.cpp:355–390`, the normal wire path uses the
rectangle's maximum extent as length. These code paths are consistent with
the default-width endpoint offset and the width-independent wide-wire slope
hypothesis. Merely adding another width row is not established as a repair
for this cached per-layer dispatch. Primary files are exact OpenROAD
`dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`: `extmain.cpp` blob
`cb40a868ff513c4bf9c7f99b9cff32dd02dd6327`, `netRC.cpp` blob
`330f54abf140b7c1283947d58adc151c6740e25b`.

For the five measured named technology vias, retained rules reproduce the
explicit LEF resistances; owned VIARES rules reproduce the declared per-cut
ITF arithmetic across all three corners. This is not independent parallel-cut
physics, generated-via coverage, all-via coverage or process qualification.

Immutable campaign evidence, under `build/campaigns/8x4-20261022-01`:

- Preparation: `rc-consumer-semantic-preparation-01/plan.json`, SHA256 `b38f0ff0b3ace618a2cd854aaf06b4b18b9eec771de9e7ea7db9e01257e7f65e`.
- Exact Root resource join: `rc-consumer-semantic-resource-join-01.json`, SHA256 `05cedf7ae89887f0268a51a5e61a6b499c1f16c00e8c585038dc3e5ea7ec2807`.
- Independent six-call raw readback: `rc-consumer-semantic-independent-raw-readback-01.json`, SHA256 `abce0d09344562621fd6df1b4e10b25d4c62af7a2cc478c40fe66ce87fe4d2d3`.
- Separate posthoc HOST calculations/source rehash: `rc-consumer-semantic-results-HOST-analysis-01.json`, SHA256 `3fac11c865e787cf2c5d54323b5b6efe582c6a393de6317cd814b5089703765c`.

The separately declared length/width experiment has since executed; its
[R26 results](streaming-8x4-rc-R-length-width-results-20261023.md) preserve
all original 0.1% absolute failures and distinguish the new slope/length
observations from still-failing absolute resistance.
