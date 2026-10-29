# Synthetic far-row consumer development study

Root executed all four declared calls after commit `c2de534` and independent
review. Measurement controls pass; the candidate development gate fails its
predeclared larger-gap coupling comparison. Full accuracy remains unmeasured.
This one source-grounded lookup experiment cannot qualify the CMOS5L model,
the PDK, any process corner, or timing.

The executed C1 measurement exposed a substantial ground/self-capacitance gap
against the empirical layered FVM reference. The C2 version-only experiment
confirmed the predicted isolated value but failed both mandatory pair coupling
checks. Those failures and all original sources/receipts remain intact. See
[the executed results](streaming-8x4-rc-consumer-cap-results-20261023.md).

## Causal mechanism and frozen change

At OpenROAD `dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`, the v1 no-neighbor
lookup uses the last row of the regular `Metal 1 OVER 0` distance table:
`extMeasure::getOverRC` in `extRCmodel.cpp:2012`, `getFringeRC` at line 1698,
and its default index in `extRCap.h:326`. This is a finite sampled distance,
not an independently established isolated limit. The existing last row is
.9um. Its fringe .0000225122 fF/nm predicts the measured C1 self slope
45.0244pF/m. Loading separate `OVER0` data does not cause this dispatch to use it.

The prepared candidate changes only that regular M1 table's distance count
from 5 to 6 and appends exactly:

```
9 0 0.000042527523152569435 0
```

All five original rows and all other bytes remain unchanged. The retained TYP
table hash is `bf2af2235b102d7bb58fe782d8d8b41a64cb3efde46593562314a499e9c4a612`;
the candidate hash is
`28418aef896dbb35c404723cd23d6f00157a29a7527c9df55fe2b327261c051f`.
A separate HOST reverse transformation recovers the original bytes exactly.

Only isolated .16um TYP reference04 case003 supplies the coefficient:
`8.505504630513887e-11 F/m / (2e-6)`. No pair or wider reference enters this
fit. A fitted training match provides no independent validation.

The 9 um endpoint is a synthetic development policy, chosen before measurement
as 10 times the previous largest spacing. Zero endpoint coupling is an explicit
assumption, not measured physics. Interpolation from .9 to 9 um remains unvalidated;
contexts above .9 um receive no accuracy claim. The reserved 99/100 um lookup path
has different assumptions and is deliberately unused. No blanket coefficient
scaling, shared-PDK edit, or near-spacing adjustment is performed.

The exact four-file causal source intake is
`build/campaigns/8x4-20261022-01/rc-cap-causal-source-intake-01/manifest.json`,
SHA `ef1c7ae013237229066e66c7032bdd161c1702f9b1b0ecee4843a8067d03c5f8`.
Every copied source byte, SHA256 and Git blob is checked; none is executed.

## Fixed measurements and claim boundary

Four fresh OpenROAD calls are declared: retained/candidate table crossed with
512/1024 um fixture-group separation. Every call contains all four cases at
50/100/150 um lengths, totaling 18 nets and 36 ports. There are zero cells, ITerms,
and routed vias. DBU is 1000/um. Exact actual DEF readback checks every port,
straight M1 route, endpoint, effective width, outline and local NDR. The .32um
stress wire uses a separately declared 320 DBU M1 rule; all unused layer widths
remain the LEF defaults. No general DEF equivalence or via normalization is used.

| Case | Role fixed before measurement |
| --- | --- |
| .16um isolated M1 | Training only; never independent validation |
| .16um M1 pair, .18um gap | Previously observed C1 development control |
| .16um M1 pair, .36um gap | Untuned held-out consumer measurement; its FVM/table prediction is already known |
| .32um isolated M1 | Wider clamp stress; no width-range qualification |

The held-out label refers to withholding its coefficient from fitting; it does
not imply blind statistical validation. Reference rectangles, vertical heights,
full TYP dielectric stack and exact SI-to-DEF cross-section witnesses bind all
four cases separately to unchanged reference04.

Source arithmetic predicts the candidate's .18um pair coupling/ground/diagonal
as 121.501/55.299723152569435/176.800723152569435pF/m. For the .36um pair it
predicts 59.5316/59.390923152569435/118.922523152569435pF/m. Its coupling is
already predicted to differ from FVM by 18.8572%, exceeding the fixed 10% gate.
That expected failure must remain a failure; the coefficient and tolerances may
not be retuned after this measurement.

The unchanged parser reconstructs complete Maxwell matrices in F, including
ground, off-diagonal coupling and every D_NET total. Mirrored coupling must
appear exactly once in each owning net and counts once globally. Actual C_UNIT,
writer rounding, physical resistor-graph connectivity and intended pair coupling
remain mandatory. All Native warnings/errors are fatal even with exit 0.

Every complete matrix cell and ground row participates in both 50 um length
slopes. Consecutive slopes must agree within 5%; the512/1024 um spacing-isolation
control must agree within 2%. This is a fixture-isolation control, not a physical
ground-boundary test. Numerical reference differences use the unchanged 10%
gate. All four calls and all failures are retained, with no prefix pass,
adaptive retry, or hidden fallback.

Measurement-control completion and candidate-development gates are separate
booleans. Even if every candidate comparison passed, full physical accuracy
would remain **unmeasured**: original BEM native 06 failed its first mandatory
case. The original 2% reference mesh/domain, 2% BEM mesh/ground-boundary,
5% BEM length, and 10% independent-comparison prerequisites remain unchanged.
A future successful BEM policy requires a distinct typed join naming its actual
new plan/hash. Empirical FVM convergence is not a rigorous continuum bound.

## Prepared identities and reopening

Under `build/campaigns/8x4-20261022-01/`:

- `rc-cap-far-row-development-proposal-01.json`: approved premeasurement scope,
  SHA `621baa705264eff5e68ecdc575a44e61893bf89a5ed57daf302d92869c787a65`.
- `rc-cap-far-preparation-03/plan.json`: SHA
  `c68adbaf9c7ce2374383db08e423b706a2c88f88abd5e062ed16b986a0033de5`.
- `rc-cap-far-command-proposal-03.json`: SHA
  `4c441162be5c864f69943465c1d42450ef5fbd1bc5bfd622b63219f4d6f4290e`.
- `rc-cap-far-host-readiness-03.json`: SHA
  `c9ec56fd2423197e4cb29ff538c08112ec7d7e119654c4b9d58a14125b7e69ab`.

Preparations 01 and 02 and their proposals are preserved unexecuted/superseded. Before any
measurement, inspection of actual retained writer DEFs showed the canonical
`+ USE SIGNAL` net header. Preparation 02 admitted exactly this header and wildcard
repeated coordinates, while rejecting extra/foreign attributes. Physical cases,
coefficients and tolerances did not change. Preparation 03 adds the exact campaign root, RC experiment kind, shared heavy lock/sentinel and wrapper/inherited-supervisor hash join, with negative controls; it does not change numerical policy.

The new producer family is `scripts/streaming_8x4_rc_cap_far*.py` and the focused
HOST controls are `test/test_streaming_8x4_rc_cap_far.py`. Ten controls pass in
normal and optimized Python, including exact append-only transformation,
training-authority rejection, NDR/effective width, physical reference joins,
complete call membership, off-diagonal held-out failure preservation,
length/isolation failures byte-identified baseline worker control flow, and campaign/shared-lock/wrapper/supervisor rejection.
Original C1/C2 preparation verifiers still reopen unchanged.

```sh
python3 -B scripts/streaming_8x4_rc_cap_far.py verify \
  --inputs build/campaigns/8x4-20261022-01/rc-cap-far-preparation-03 \
  --plan-sha256 c68adbaf9c7ce2374383db08e423b706a2c88f88abd5e062ed16b986a0033de5
```

The fixed Native bound is four 30 s leaves, 150 s work and 180 s outer, one CPU,
2GiB memory including 128 MiB bounded scratch, no extra swap, offline pinned
CAD image, read-only input/source mounts and an owned fresh output. Root's
resource receipt must bind the exact proposal argv, plan and every transitive
producer seal, and prove terminal cleanup with no remaining container/process.
The separate HOST reader reparses every retained leaf and joins that receipt;
it never executes Native. Its command, after actual terminal state only, is:

```sh
python3 -B scripts/streaming_8x4_rc_cap_far_readback.py \
  --inputs build/campaigns/8x4-20261022-01/rc-cap-far-preparation-03 \
  --plan-sha256 c68adbaf9c7ce2374383db08e423b706a2c88f88abd5e062ed16b986a0033de5 \
  --directory build/campaigns/8x4-20261022-01/rc-native-outputs/rc-cap-far-01 \
  --resource-report build/streaming-tt-resources/8x4-rc-cap-far-01/report.json \
  --command-proposal build/campaigns/8x4-20261022-01/rc-cap-far-command-proposal-03.json \
  --output build/campaigns/8x4-20261022-01/rc-cap-far-independent-readback-01.json
```


## Executed result and independent closeout

All four fresh leaves completed and passed the strict raw measurement controls.
The candidate gate remains false, as predicted, because both .36um pair
fixtures fail the unchanged 10% coupling comparison. The resource terminal is
failed/exit 2 with confirmed cleanup and unchanged inputs; it is not a partial
packet or an infrastructure failure. Worker time was .70945s and the outer
supervisor elapsed 4.373 s.

First 50→100 um slopes are shown in pF/m; both length slopes, every matrix cell,
every ground row and both spacing fixtures remain in the raw readback.

| Table/case | Diagonal | Coupling magnitude | Ground |
| --- | ---: | ---: | ---: |
| Retained .16 self | 45.0244 | — | 45.0244 |
| Retained .18 pair | 156.78448 | 121.5002 | 35.28428 |
| Retained .36 pair | 98.9074 | 59.5318 | 39.3756 |
| Retained .32 self | 45.0244 | — | 45.0244 |
| Candidate .16 self | 85.0552 | — | 85.0552 |
| Candidate .18 pair | 176.7998 | 121.5002 | 55.2996 |
| Candidate .36 pair | 118.923 | 59.5318 | 59.3912 |
| Candidate .32 self | 85.0552 | — | 85.0552 |

The candidate .18 pair's largest complete-cell/ground difference is 7.49003%.
The .36 pair coupling is 18.8569–18.8572% low against FVM, while its ground is
about 7.71% high. Its unchanged near coefficient correctly remains a failure;
no retuning followed. The .16 self result reproduces the fitted target within
printing precision and supplies no validation. The .32 result is 9.70892% low;
it is the same clamped-width consumer result as .16, so its numerical 10%
pass does not establish width interpolation or physical width dependence.

Maximum consecutive-slope change is .00148146%; spacing-isolation change is 0.
A conservative source-backed writer bound is .0176pF/m per complete slope cell,
far below the held-out coupling discrepancy. It is a printing bound, not a
physical/reference uncertainty bound.

The frozen independent reader reparsed all four raw leaves and every input,
DEF and SPEF hash. It joined the actual 1 CPU/2GiB/no-swap cgroup report, exact
proposal argv, campaign/shared lease, wrapper/inherited guard and empty
process/container cleanup. A supplementary HOST closeout independently
recomputed all 24 actual resource seals, Root GO and the complete numeric packet.
Root's Homebrew Python launcher appears as its Framework executable in
`sys.orig_argv[0]`; all remaining wrapper arguments are byte-identical and a
separate HOST identity query confirms this interpreter re-exec behavior.

- `rc-cap-far-independent-readback-01.json`: SHA256
  `bfc10aaacb56a4f6ae89aa6b5367b4faf51678c3928a4b89a05ab7bec8042051`.
- `rc-cap-far-independent-closeout-01/report.json`: SHA256
  `de78c620cb9838c48e4b1b0664e208e849c609ef0f72bed1d7c665684c8ede05`.
- Resource `build/streaming-tt-resources/8x4-rc-cap-far-01/report.json`: SHA256
  `aa966ec09acbc64a503a996869aa5b0d629d4ab5a159f19230e419d517480183`.
- `rc-cap-far-root-go-01.json`: SHA256
  `579e5fc8da242e53acd3aba0b4a764ff2e6fa4b0fd40ca6edb0240ea0f0bceac`.

Full accuracy is still unmeasured and original BEM prerequisites remain false.
The experiment confirms a consumer table-selection mechanism and exposes an
untuned remaining coupling error; it does not validate the synthetic 9 um endpoint
or the broader model envelope. No producer or table was changed after execution.
