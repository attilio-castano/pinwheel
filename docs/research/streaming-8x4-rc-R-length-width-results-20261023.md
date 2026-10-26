# Fixed26-net R length/width result

`rc-r-length-width-01` completed all six calls and passed its **separate
length/width diagnostic controls**. The independent frozen HOST closeout
recomputed complete geometry, raw SPEF, per-edge rounding intervals, absolute
audits and slope/via results, and joined exact Root input/command/cleanup.
Worker time was1.029s; Root outer time4.317s, exit0, no process/container
residue. No HOST reader launched Native.

This is not an absolute-R or process-model pass. The new126 absolute wire
audits contain123 failures. The earlier17-net experiment remains failed with
its original72 wire failures and30 passing via differences; its receipts and
0.1% thresholds are unchanged.

| Measured control | Baseline rules | Local per-corner LEF plus `-lef_res` |
|---|---|---|
| Seven width families × three corners, both adjacent slopes |Source-policy slope error at most0.046364% |ITF actual-width slope error at most0.001186% |
| Wide/default M1 and M2 slope ratio at doubled width |0.999976–1 |0.499993–0.5 |
| Independent150um rounding check from50/100um |21/21 pass |21/21 pass |
| Original-style absolute wire audits |60/63 fail |63/63 fail |
| Five named-via differences × three corners |15/15 pass |15/15 pass |

The candidate uses the pinned ITF sheet resistance for each selected corner
and divides by the actual wire width. Only the five local routing LEF RPSQ
tokens and the explicit `-lef_res` option differ; all other LEF bytes,
including named-via geometry/resistance, restore exactly to the immutable
original. The shared PDK is untouched. The actual Native census checks all
26 nets,31 segments,5 named vias,52 ports and both complete NDRs per call.

The TYP example separates width scaling and endpoint behavior:

| Family | Baseline slope (ohm/um) | Candidate slope (ohm/um) | Baseline / candidate intercept (ohm) |
|---|---|---|---|
| M1.16um |0.6875 |0.6875 |0.110 /0.110 |
| M1.32um |0.6875 |0.34375 |0.220 /0.110 |
| M2.20um |0.439796 |0.440 |0.088 /0.088 |
| M2.40um |0.439796 |0.220 |0.1759 /0.088 |

Both measured adjacent slopes agree within the fixed0.1% gate. All42 heldout
checks pass the preregistered interval overlap `I150 ∩ (2*I100-I50)`, using
only the six-significant-digit `%g` rounding of every raw resistor. These are
serialization allowances, not physical error enclosures. The positive
intercepts persist, so correct width scaling does not repair the unchanged
centerline-length absolute audit.

This supports the source-grounded dispatch diagnosis: normal version1 caches
a per-layer coefficient at the default width; the explicit LEF-resistance
branch uses actual-width scaling. The measured endpoint term is consistent
with the wire rectangle extent used by `netRC.cpp:355–390`. Relevant exact
OpenROAD `dcf36133a369abc8f3c5e5738cd4d82e4903c0e0` sources are
`extmain.cpp:242–306,357–376`, `netRC.cpp:305–390` and
`extSpef.cpp:1111`. The source and all physical/numerical producers are
hash-bound by the preparation.

The measured named technology vias retain20/20/20/20/4ohm targets in both
policies, with maximum difference error0.00008ohm. This establishes behavior
of these five explicit names under this consumer policy; it does not qualify
generated vias, parallel-cut physics, the draft capacitance table, other
widths/spacings, a full CMOS5L process model or extracted design timing.

Evidence under `build/campaigns/8x4-20261022-01`:

- Preparation01: `be67ddd26954fbc615462a2fcbb01e63ac9bb52c277a8d9e950ce8da170e8825`.
- Command proposal01: `42f20f753fed284bfab29b7d99c96d3e28cb1e5a938879283ce4e0096da05c9c`.
- `rc-r-length-width-closeout-01.json`: `9e4394463fb1a1ac7f12e53410826968a5cac35248bc59c4e3ccd165db57c7b4`.
- Exact Root resource report: `6ec2f24370c72b112e6f2f92352e6147bdf1de180b16d104f6c8e85b55d9681c`.
