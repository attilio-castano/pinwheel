# Streaming Tiny Tapeout renewal: outcome and remaining gates

**Outcome as of 2026-10-19 02:06 UTC.** This is an evidence summary,
not an acceptance receipt. The [approved reactivation
plan](streaming-tt-closure-reactivation-20261018.md) runs from 15:26:07 UTC
on October 18 to **03:26:07 UTC on October 19**; admission of new candidate experiments
closes at **00:26:07 UTC**. The [execution journal](streaming-tt-renewal-journal-20261018.md)
retains the chronology, failed attempts and detailed identities. The maximum
window does not require spending time after prerequisite failures prevent the
remaining checks; no new candidate or RC retry is admitted during closeout.

We have closed the renewed source and optimized digital proof work and have
measured the actual physical failure modes. We have **not** closed a fully
routed or tapeout-ready candidate. The immediate bottleneck is completing
detailed routing while retaining the now-clean nominal timing and electrical
counts, followed by antenna and final physical checks. The one-hour routing
validation timed out without a completed database. A separate RC-model
qualification gap would remain even if detailed routing succeeded.

## What has closed

| Scope | Actual result | Limit |
| --- | --- | --- |
| Fresh committed source foundation | **649 modules, 44,383 declarations, 25,323 theorems; 65 executable and eight kernel suites.** Both custom-axiom and unused-private-axiom controls rejected. | Source/library evidence, not implemented-netlist or physical qualification. |
| Balanced source and actual raw lowering | The 64-leaf serial guard became a kernel-equivalent balanced conjunction. Fresh frontend and depth-two/depth-four raw component gates passed all-state/output proofs, wrapper checks and **19 expected rejections: 16 semantic mutations and three private-axiom controls**, with **4,682 actual Native commands**. | The raw component gate is an input stage, not a full physical acceptance gate. |
| Optimized depth-two whole device | Whole-device kernel join and **25 API names** passed; independent actual-SV reimport matched every cell/pin, FF D root and public output. All **6,039 semantic state bits** remain. | Certifies the optimized digital candidate before placement/CTS/repair. |
| Independent proof replay | **395 positive modules**—161 frontend, 228 core, six device—freshly compiled, followed by the **same two private-control commands**; all **397** commands and journals closed. | Final post-repair/post-route correspondence remains a separate proof. |

The balanced optimized map reduces the longest unweighted combinational path
from **114 to 64 gates** (core 82 to 49), at a mapped Liberty-area increase
from **606,637.1178 to 612,878.6538 µm²**, about 1.03%. These are structural
measurements, not routed delay or die-area signoff. The 64×64 program bank,
two-word TX/RX queues, 20 ns clock and protocol capabilities are unchanged:
4 KiB duplex SPI, 4,097-bit JTAG, 64-byte reactive I²C and autonomous
single-frame UART. No capacity or behavior was removed to obtain these results.

## What the physical runs taught us

The implementation has progressed through placement, CTS, global routing,
antenna insertion and ordinary timing-repair attempts. This is useful Native
measurement, but none of the current candidates has completed detailed routing
and final signoff.

1. **Global-route overflow responds to repairs and reserve settings.** The ten-buffer clock/
   enable fanout repair retained every original placement and all 6,039
   positive, depth-four FF clock paths. Global routing subsequently reached
   zero overflow. Later, the 32-branch data-fanout candidate left one Metal4
   overflow at 20% capacity reserve; a separately reviewed 16% reserve variant
   reached zero. Physical tracks, rules, footprint and the clock stayed fixed.
2. **Nominal timing is sensitive to physical continuation.** Fresh propagated-
   clock, global-route estimates first exposed 16 fast-corner hold failures
   at **−0.0663482 ns**. Ordinary repair reduced the independently read-back
   result to **seven failures at −0.0231356 ns**. At that cut, all setup, slew
   and capacitance violation counts were zero, but antenna-diode loads caused
   **13 fanout violations**. These are rejected nominal-RC estimates, not
   qualified extracted timing.
3. **Adding delay consumes placement room.** Raised internal hold targets of
   +0.10 ns and +0.06 ns reported +11.8% and +7.3% area respectively, then
   failed detailed placement on 918 and 349 instances. Neither produced a
   completed timing-step ODB or fresh accepted timing. The resizer's rollback
   log counter is not a reliable added-cell census; actual database inventory
   is required.

The measured **+0.05 ns internal hold-target trial04** passed detailed
placement and mirroring after marking 67 endpoints for repair. Its subsequent
global route failed with 43 overflow units: Metal2 12, Metal3 27, Metal4 4.
Its frozen plan is
`build/streaming-physical-development/streaming-tt-balanced-postgrt-data-hold050-04/plan.json`,
SHA-256 `9a2d791c26e39be9049db094f96185082c5d1ddca3f9d11904773831a0430312`.
The resource guard closed failed in 242.817 seconds with unchanged inputs and
complete owned cleanup; resource SHA-256 is
`281078a4333781102dd041d6fd55d578a85cc4a71d863f4dffe56e03da6cbd7e`.
No repaired timing-step ODB survives this failure, so fresh accepted timing
is unavailable. Trial05 changes only router reserve 16% to 12%, retaining the
measured 0.05 ns target and every acceptance condition. It completes all ordinary
prefix stages and fresh three-corner STA. Setup, hold, slew and capacitance
violation counts are zero at all three nominal corners; fast hold slack is
positive at **0.0155542 ns**, slow setup slack is **2.21072 ns**. Six actual
fanout failures remain, with maximum load count 20, so every acceptance flag
remains false. The original 42,390-instance contract and all 6,039 clock paths
are preserved in the 42,540-instance repaired database.

Its original HOST closeout additionally rejects a tuple/list JSON format
mismatch in route-summary rows. A separate HOST-only reopening runs the
unchanged complete validator with only that serialization boundary normalized,
all subprocesses forbidden and all original input/artifact hashes unchanged.
It closes the diagnostic at SHA-256
`2ada096b5cd3b96f3ca6ca6746ffe45c21899a991b67e38ef1663f22c9d2c3a1`;
the failed original receipts and all six real fanout failures remain unchanged.
A targeted eight-buffer proposal now moves diode loads first while retaining
most functional paths and fixing all prior cell placements. Its first Native
attempt06 fails placement on one new buffer. A separately reviewed attempt07
widens only the search for new cells; it passes placement, complete source/pin/
clock checks, database round-trip and global routing while preserving every
original placement. The fresh antenna check then reports **70 violating nets
and 72 pins**. There is no final readback or fresh timing for this attempt,
and its failed receipt remains unpromoted. The separately reviewed route-only
jumper repair08 then inserts **48 jumpers for 38 nets**, reducing antenna
failures from 70 to **32 nets** without adding diodes or changing any of the
42,548 cells, pins, placements or statuses. Source/clock contraction, legal
placement, logical PG and database round-trip checks pass. All routing guide
and via endpoints stay within Metal1–4, with unchanged Metal1 pin access.

This actual08 target now has **zero setup, hold, slew, capacitance and fanout
violations at all three nominal corners**. Fast setup/hold slack is
9.73128/0.0117854 ns; slow is 2.1238/0.318759 ns; typical is
8.44321/0.145805 ns. The six earlier fanout failures are closed at this target.
These remain global-route nominal estimates, not qualified extracted timing.

Review finds that the jumper command prints no fresh routing table and its
saved congestion counters use narrowing integers. The saved-grid comparison
passes with identical capacities, but cannot independently establish full
fresh global zero overflow. This uncertainty and the 32 real antenna failures
keep strict structure, fresh timing and overall acceptance false. Native/HOST
exit two is preserved; the resource guard closes failed with cleanup and all
1,963 inputs unchanged in 167.849 seconds. A separately labelled diagnostic
permission was independently reviewed and installed for the complete ordinary
detailed-routing and signoff tail. It preserves the failed parent and every
final check; permission to measure does not accept the failed parent.
Raising an internal repair target does not relax the required zero setup,
hold or electrical violations at every declared corner.

The first full-tail attempt started actual CAD at **00:23:43 UTC**, before
the candidate cutoff, and exhausted its **900-second Native allowance** in
DetailedRouting. The first routing pass reported **41,449 violations** before
repair iterations. These intermediate counts are not a terminal DRC result.
No completed routing state or final ODB was produced. The controller reports
`timed_out`, typed exit 124; Docker exited 137 after owned termination. The
outer resource receipt closed in **1,367.230 seconds**, with all 2,232 guarded
inputs unchanged, no remaining owned process/container and cleanup confirmed.
Complete source replay before and after the attempt has the same digest.

A separately named validation of the **same frozen candidate** used
a 3,600-second Native allowance and 4,320-second outer guard.
The routing recipe, all 34 ordinary tail stages, rules, layers, constraints,
tools and PDK remain identical. Only ownership, budget and parent provenance
may change. This uses the approved plan's existing-parent `cad-validation`
provision after the new-candidate cutoff; it does not authorize a new physical
variant or substitution of a partial routing database. Author, independent
and Root packet reviews passed. All 92 staged inputs are read-only and all
2,346 guard anchors were checked. The guard launched at about 00:58:13;
complete source-authority revalidation passed and actual CAD started at
**01:01:53 UTC**. Complete iteration counts were **41,449 → 29,969 → 30,815 →
8,535 → 5,992 → 5,282 → 4,910 → 4,698 → 4,367 → 4,124**. The last complete
iteration is about 90% below the initial count, with 3,195 shorts and 929
spacing violations. The next iteration reached a provisional 3,777 at 90%
before the Native allowance expired. These are intermediate router counts,
not terminal DRC or physical signoff; they neither prove eventual clean
routability nor establish that the design cannot route.

The actual result is **`timed_out`, typed exit 124**, with **no completed
`state_out.json` or authoritative routed ODB**. Docker exited 137 after owned
termination. The outer resource receipt closed at **02:05:42 UTC**, in
**4,044.868 seconds**, with all **2,346 inputs unchanged**, cleanup confirmed,
no remaining owned processes/containers and no cleanup errors. Complete
pre/post source replay digests are identical:
`74b7fcface5707cebcd0eb805bb26a65eb630ae318ad771c51f98beb9978ecb9`.
The final physical report is
`build/physical/streaming-tt-balanced-final-02/report.json`, SHA-256
`c589f650ee276e967ae8835571f67a83eca8c46320438fa8620e29c608de5902`;
its resource receipt is
`build/streaming-tt-resources/streaming-tt-balanced-final-02/report.json`, SHA-256
`e9ae8fcf06b4e96023a78f04bf7baab96f931166b9580dc425c6749b63d5b2bd`.
No partial routing state is substituted for the missing completed target.

## Final proof and RC gates remain open

The fixed source replay has been revalidated, and the final-state handoff
requires the actual completed detailed-route target, latest authoritative
ODB, fresh native export and a complete semantic FF map. A diagnostic witness
covering all 6,039 FF names, pins and sequential functions is not a transition
proof. The final actual-netlist proof family, **M**, has not been admitted or
run against a completed final target.

The reviewed GEN04 layout removes repeated whole-authority regeneration
between proof families. On retained diagnostic inputs, all **3,966 modules
and 220,262,451 source bytes** match GEN03 exactly in the same dependency
order, with 15 diagnostic families coalesced into one Native stage. Chunk
size remains one; individual Lean processes, memory limits, proof bodies and
private controls are unchanged. This HOST-only comparison neither fixes the
eventual final-M count nor proves the final device or promises deadline fit.

The offline private FasterCap build and five analytic sphere controls passed.
Both normalized and finer-mesh wire pilots were **rejected** on early numerical
diagonal-dominance warnings, despite exit zero and terminal reported Frobenius
changes below 1%. The predeclared warning refusal was retained. This is not
proof of nonconvergence or of wrong process data. No wire training case,
layered-wire comparison, held-out calibration or manufacturing-corner
qualification was admitted.

A fresh independent provenance audit binds the actual Final02 configuration:
`RCX_RULESETS` selects one nominal **seven-layer SG13G2 rules file** through
the CMOS5L alias, while the actual technology LEF has **five routing metals**.
All three timing corners vary cell PVT while sharing nominal RC; they are
not three independently qualified RC corners. Signal routing restricted to
Metal2–4 does not establish extraction-model applicability. Matching basic
five-metal process data is already local: three merged official ITFs plus
18 retained draft/common/rule objects, all 21 checked by SHA-256 and Git blob.
The draft five-layer rules need generation provenance, consumer/coverage
validation and justified corner calibration; their corner construction differs
from the merged ITFs. The audit is
`build/streaming-tt-recovery/renewal-RC-provenance-audit-01/report.json`, SHA-256
`25e130546cf2c0114a9f72a344c8742d6737ca3ad7d8a739b65728aa632f69a4`.
Root also rehashed all 44 reviewed objects. Historical setup/no-pilot statements
in the [RC review](streaming-tt-rc-model-review-20261018.md) are superseded by
these later build and pilot receipts; its unqualified-model conclusion and
the [extraction scope](streaming-tt-extraction-scope.md) remain applicable.

The remaining mandatory gates are: completed detailed routing; actual final
ODB-to-source all-state/output/clock/packing proof and public/private audit;
final-netlist public-wire regressions; justified extracted setup/hold and
electrical checks; actual power connectivity; DRC, LVS and antenna closure;
and the applicable unchanged full official TT precheck. Isolated pin/PDN
fixtures, HOST controls and nominal timing do not close these gates. No
tapeout-readiness or fabrication-submission claim is made.

## What is needed next

There is no immediate user decision, installation or missing basic process
document blocking the work. The next focused campaign needs to establish
whether the exact candidate can reach completed, clean detailed routing under
an adequate declared budget, then address measured route/antenna failures.
The present timeout gives no route-violation geometry with which to justify
a specific new floorplan or repair. A qualified five-layer extraction model
and independent R/C/via calibration form a separate engineering track.
Once a real completed target exists, the prepared full M proof, separate
private controls, public-wire regressions and final physical/precheck gates
must run against that exact target. Prepared tools and HOST controls do not
count as those executions.

If already available, an IHP/organizer-qualified CMOS5L extraction deck with
exact process/corner/tech-LEF/tool bindings and validation records, or independent
geometry-specific R/C/via reference data, would shorten RC qualification.
Additional generic stack parameters or a generic approval would not close it.

## Retained evidence and recovery pointers

The following immutable receipts were rehashed for this report. Paths are
relative to the repository root; their recorded scopes remain authoritative.

| Receipt | SHA-256 |
| --- | --- |
| `build/validation/renewal-foundation-649-03/report.json` | `81fd894827acd13248bc2f1f12851c35fa87ff342176a796781dd9128f288379` |
| `build/validation/streaming-tt-balanced-raw-02/report.json` | `5bd0d0889787f9022b00fc97bb11eb6a0f685fe5fc72cb9b0fdebfc4fa4752d3` |
| `build/streaming-tt-optimization/parent-intake-balanced-02/report.json` | `f49053aab54c09c171357d090336dfca0d3c1a28892df4cd3c4808ccc9481656` |
| `build/streaming-tt-optimization/replay-intake-balanced-e2-01/report.json` | `2bdf6da15598ea03362a788fa918e0df50b3aaf1613672bfe2f6136f582224fa` |
| `build/streaming-physical-development/streaming-tt-balanced-postgrt-passive-readback-02/native/sta/report.json`—rejected timing | `9393be7e28b50f00251f285c742c7f05db9cdcbe054ff1a945f53e21100585b0` |
| `build/streaming-physical-development/streaming-tt-balanced-postgrt-data-hold100-02/report.json`—failed placement | `5515e6a50284b1194ac0f216b3e88a828afb2c49fb064c97b73ae8b1042a83cf` |
| `build/streaming-tt-rc-research/typ-tessellated-root-closeout-unqualified-01/report.json`—rejected RC pilot | `112621b5020bae9e1aa6eb1775cb8e8774d12288fa17c741556c4e14651fa339` |
| `build/streaming-physical-development/formal-actual-M-generator-unqualified-04/host-preparation-01.json`—HOST preparation only | `b57c90296b8735eb57a3b30dcdffe1f1d5f7b7aca6844dbad1949094967e6af8` |
| `build/streaming-physical-development/formal-independent-M-handoff-review-unqualified-01/report.json`—HOST review only | `610e9f66285418eab1d681785697cb8f9805b5770e204272ee0f1f25a16e029b` |
| `build/streaming-physical-development/streaming-tt-balanced-postgrt-jumper-08/report.json`—closed diagnostic, rejected physical parent | `ed3c4e5795184d55256b3746038d52546732b6af91e98fdff98cda8727dc40dd` |
| `build/streaming-tt-resources/streaming-tt-balanced-postgrt-jumper-08/report.json`—failed typed-two child, cleanup complete | `ce2367d37d6addfa3353bfc4f480b54e537150e6e2bf06b9c3a8a1f7b50a9da4` |
| `build/physical/streaming-tt-balanced-final-01/report.json`—timed out, no completed routing state | `4861310538889c6b02db00a8a9b81be9adc18a13dea1eb53de0ebb594e9de170` |
| `build/streaming-tt-resources/streaming-tt-balanced-final-01/report.json`—typed 124, cleanup complete | `f55d975f26b901330c2b647e3b219e39a077ce32cedc49ae62f12596cb718438` |
| `build/physical/streaming-tt-balanced-final-02/inputs.json`—frozen inputs for closed timed-out validation | `1b6f464bb4a9802061b6ba0fec47593ecb2df00826a789ea34b2f2fcf6454714` |
| `build/physical/streaming-tt-balanced-final-02/guard-plan.json`—reviewed same-candidate validation guard | `b1f7fc5bd064652cd4faeafc70c570a6f4ac8cdf8e0bec8d82af6ee9089b9a08` |

For continuation on Final02, the actual fixed replay admission is
`build/streaming-physical-development/balanced-postgrt-final-replay-admission-unqualified-02/admission.py`
(SHA-256 `2f9cea85a303f03c9e511b1c1ae661a0097665c8fa769477f319ff34dd86246b`)
and handoff is
`build/streaming-physical-development/balanced-postgrt-final-M-handoff-unqualified-03/m_handoff.py`
(SHA-256 `220dac90546b8095932348050051e0905cb3d9aca09fe6e7afe28317e6f51eee`).
They preserve the fixed N395/same-two-private authority and unchanged full
GEN04 proof producer, with a fresh A02-owned snapshot in Final02 metadata.
The concrete data-only command protocol is
`build/streaming-physical-development/balanced-final02-M-handoff-protocol-unqualified-02/plan.json`
(SHA-256 `d35a8c8dbdac8c39de6aad3e6d12068e0f110860dcb46b9f17f118b7077613c9`).
Its target/count fields remain pending and command arrays are templates.
The ordinary canonical exporter uses `python -B` without `-I`; fixed owned
helpers and proof entrypoints retain `-I`. Root verified that the earlier
isolated canonical invocation failed imports before any Native execution;
the corrected command passes read-only help and import checks.
The original handoff02 plan remains a historical protocol reference; its
Final01/A01 owner pins cannot authenticate Final02. Actual M has no admitted
target or Native lease yet. The failed08 diagnostic admission was bound and
independently reviewed before the first full-tail attempt. Final02 binds that
authenticated terminal first attempt and retains its timeout. A later M
handoff must authenticate terminal Final02 and select a completed routing
checkpoint. Do not rewrite old receipts, reuse populated
attempt directories or infer acceptance from a successful prefix. The actual
Final02 has no such checkpoint, so this protocol cannot advance against it.
A future actual attempt needs its own exact authority and target bindings.

The [closed controller snapshots](local-evidence/README.md#artifact-4c248989ba0a)
preserve reviewed source bytes and original-path manifests. They were not
executed from the documentation tree and are not standalone reproduction
bundles. Full frozen inputs, runtime/PDK identities, generated objects and
Native outputs remain under `build/`. Recovery starts with the journal and
those hash-bound original owners, not execution of a relocated archive copy.
