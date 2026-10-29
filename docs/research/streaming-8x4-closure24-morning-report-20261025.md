# 8×4 closure campaign — morning report

**Engineering and cleanup closeout: 25 October 2026, 05:10:25 UTC.** The companion adoption manifest records the final local report commit, exact snapshot and postcommit audit. The approved maximum was 24 hours; engineering and cleanup ended after 14 hours 32 minutes.

**Closure objective not met; two mandatory parent gates closed; neither full nor predefined partial closure achieved.** We now have complete final-target Boolean correspondence, the finite public-wire corpus, and passing physical/official checks. OpenROAD antenna 1, all eight extraction-model rows and qualified timing remain open. The predefined partial result requires routing/antenna closure as well as proof and physical checks, so G4/G5 alone do not satisfy it.

| Mandatory parent gate | Baseline `e800b424…` | Terminal engineering result |
| --- | --- | --- |
| **G1: whole route/antenna** | No admitted completed final route. | **OPEN**. Whole ordinary DRT completed, route DRC 0; OpenROAD antenna 1 persists. |
| **G2: applicable extraction** | Eight obligations incomplete. | **OPEN**. Scoped software/arithmetic controls pass; all eight qualification rows remain open. |
| **G3: qualified timing** | No qualified same-target result. | **OPEN / NOT ADMITTED**, because G2 did not close. |
| **G4: correspondence/wires** | No final-target acceptance authority. | **PASS**. Fresh complete 3,966-module proof, whole-owner audit, real private negative controls and complete finite public-wire corpus independently joined. |
| **G5: physical/official** | No fresh complete packet. | **PASS**. Full GDS DRC/antenna, transistor top LVS/used references, required PG connectivity, consistent views and all applicable official checks. |

## One unchanged implementation target

The accepted target is variant-B ODB `f516…eee0`, GDS `5c1d…6261d`, logical Verilog `b8b0…c971`. All nine payload members and the complete SDC remain fixed: 6,039 semantic state bits, 64×64 bank, depth-two queues, 20 ns/full I/O contract, 85% density, Metal 2–4 signal routing, and full SPI/JTAG/I²C/UART capacities. The 8×4 die/core, 43 public signals including clock, two PG BTerms (45 total) and 70 admitted full-height power stripes are preserved.

The physical repair added bounded PG-aware diode access and placement at the canonical initial and subsequent insertion paths, using the pinned blocked-layer and legal-site rules. The admitted post-seed path completed ordinary routing; the fresh initial path still failed as recorded below. The executed shared PDK was preserved.

Exactly two physical policies, A/B, were consumed. Completed ordinary routing/canonical tail used the authenticated post-diode 39 seed. The separate fresh initial 94-diode path failed strict guide refresh (`GRT0116`); it remains failed. Seeded completion does not prove reproduction of that path. A further physical policy would need new authorization and fresh affected target/proof/timing/signoff evidence.

## Complete proof now passes

Source checkpoint 42 is `f87de820…`: six new production/test/document files, with old producer bytes preserved. Fresh source generation and a separate, fully reaped independent rederivation preceded every new Lean object. The positive run compiled **all 3,966 actual modules**, with **7,932 intent/result events**, 395 N modules and 4,361 positive owners. No earlier prefix, diagnostic object or synthetic root entered acceptance.

The whole-owner audit covered 1,373,773 declarations and 1,027,725 theorems with only the approved standard axioms. The 14,923-file runtime, imports, source/object/log identities, 6,039-state/24-output mapping and 1,016 CTS nodes were checked. Positive execution took 4,925.871 s; its guard exited 0 in 4,926.912 s. Sampled peak aggregate RSS 4,006,048 KiB stayed below the unchanged 4,194,304 KiB cap.

**Real separate private controls also pass.** The original unused private axiom compiles (exit 0), while the complete private auditor rejects that exact axiom (expected exit 1/no audit object). It imports all 4,361 real positive owners plus BAD: 4,362 ordered owners. This packet took 87.561 s; its guard exited 0 in 140.394 s with current inputs and confirmed cleanup. Its independent review closed, with sampled peak aggregate RSS 4,051,152 KiB below 4,194,304 KiB and the actual positive FinalRequired object bound instead of a stub. The explicit synthetic stub used in earlier software controls was not substituted. Canonical Gate 4 reader 05 then closed PASS against the same target, resource/RootGO/source seals, full rederivation and wire authority.

The finite public-wire corpus passes 35 positive cases plus one actual sampler mutation, 14 processes/28 events, four protocols and 513,297 connectivity edges. This finite corpus complements the universal two-state Boolean state/step/output/run/packing/clock-reset proof. Neither supplies delay, electrical, analog or silicon qualification.

The failed checkpoints remain separate evidence:

| Preserved failure | Resolution and scope |
| --- | --- |
| Observer/context and API harness failures | Repaired in new typed families; old receipts/source bytes preserved. They were not mathematical counterexamples. |
| Opaque-state full proof: CanonicalDevice type error after 3,463 successes | 547 finite transport proof sites/seven modules repaired; the failed prefix was never accepted. |
| Next full proof: Codec aggregate-memory stop after 3,466 successes | 48 private chunks cover all 6,039 indices; 829 public declarations/statements and other Codec bytes stay fixed. No original Codec verdict was inferred from the stop. |
| TypedJoin/ActualTypedJoin elaboration and FinalAudit codegen failures | Two full-function headers, five congruence proof spans, one parenthesized equality composition and bounded owner data were validated diagnostically, then compiled afresh in the successful full run. |

The final composition changes 11 modules and leaves 3,955 unchanged. The finite 7/3,959 and Codec 8/3,958 certificates describe earlier stages only. TypedJoin header text and proof/audit representation changed: `mathematical_statements_domains_unchanged=false` and `original_TypedJoin_public_header_text_unchanged=false` are explicit. Full 6,039-state/18-input domains, full function-width polymorphism and every other public statement are preserved. The positive audit explicitly imports 4,360 generated owners; the remaining positive module is the auditor itself. The private audit imports all 4,361 positive owners plus BAD. Its 4,362-name array and the positive array each use 69 bounded noinline chunks; the original audit predicate, whitelist and rejection body stay exact.

## Physical/official checks and the open antenna gate

Fresh GDS DRC passes 332 categories/zero items; foundry antenna passes 23 categories/zero items. Every applicable unchanged official check passes: nine checks through three Native calls/six events. Real transistor LVS matches 37 circuit pairs including top, with complete references for 38 used masters and recomposed CDL for 98,957 instances/322,058 positional terminals. Its 244 device definitions are hierarchical, not the flat-chip transistor count; two device-empty fillers simplify normally.

Required PG connectivity combines same-rail geometric paths for every 98,957 ITerm per rail/zero skips with real strict-power-port `NET_ONLY=false` GDS-versus-complete-CDL LVS. PSM's short checker is a stub and was not executed. Fresh same-target views and all 43 public signal-pin rectangles/labels pass. G5 is closed within the approved pinned-deck contract. The flow's EQY, KLayout XOR and linter steps remained disabled and are not counted as executed. Package, IR-drop and EM qualification are unclaimed; no new acceptance gate was added.

G1 remains open: net `engine.core._0083_.Y` has Metal 3 cumulative ratio 213.80 against 200, with protection joining through Metal 4. The source comparison distinguishes OpenROAD's layer-prefix/LEF/PWL model from the foundry deck's full-stack diffusion-based diode branch. It explains a possible discrepancy, but zero-item XML does not prove the actual net's selected branch. There is no false-positive verdict, waiver or change to the criterion.

## Extraction and timing remain the main uncertainty

The actual-via packet passes 270 controls: 126 via-chain/144 wire, two policies, three owned ITF labels, four named actual vias and three generated 2/8/16-cut arrays. Public decoder/terminal/cut/enclosure geometry and complete SPEF graphs are checked. Baseline 42 ITF mismatches remain preserved; exactly four VIARES/three CUT-resistance token changes produce source-aligned 0. This establishes software arithmetic/units transport, not independent contact/cut/corner physics or SPECIALNETS electrical qualification.

| All eight model rows remain OPEN | Principal missing evidence |
| --- | --- |
| Resistance / via R | General physical current paths, contact/spreading/cut behavior and justified corners beyond the bounded arithmetic controls. |
| Ground C / coupling C | Independently justified physical coefficients; isolated/context errors, zero vertical coupling and the 18.86% heldout failure remain. |
| Dielectric interfaces / layer coverage | Complete applicable independent references and consumer coverage; expanded-domain reference work is incomplete. |
| Width/spacing / consumer semantics | Complete neighbor/shield/overlap/pin contexts, interpolation, genuinely untouched heldouts and a qualified rules/LEF/process/caller bundle. |

The fixed eight-call full-stack study had no profile passing both geometries: near reciprocity 0.926316%, far 1.010310% exceeded the 1% gate. Further numerical conditioning/tuning is bindingly stopped. Historical 1 pF/m prediction versus 2 pF/m remains a failed prediction. Source-aligned transport and owned MIN/TYP/MAX labels cannot qualify physical corners; previously observed cases cannot become untouched heldouts.

A bounded official-source check earlier in the campaign found no qualified replacement package addressing all eight rows. Official dev `cb743f75…` selected legacy seven-layer rules; PR 1237 was draft/unmerged at `ffdafdbb…`. Merged ITF PR 1251 retained missing tolerances/copied TopVia 1 limits. Issue 1282 discusses a mismatch but warns that its fitted values use the wrong deck. These are scoped external source observations, separate from the unchanged executed PDK.

Qualified STA was **NOT ADMITTED**. Closing G3 requires a qualified model/SPEF and justified cell/RC corners on the exact final views, complete relevant annotation and propagated clocks, nonnegative setup/hold and zero slew/capacitance/fanout violations under unchanged 20 ns/full I/O constraints. Historical draft-RC hold negatives remain diagnostic. The antenna residual is concrete local engineering; complete reference/envelope/corner qualification has unresolved physical-data dependencies and no demonstrated bounded completion time. STA/ECO effort cannot be predicted before that model exists. A separately authorized follow-on can resolve the antenna and qualified reference/corner bundle, run qualified STA/any ECO, then rerun affected G4/G5 on the exact resulting target. Existing G4 Boolean and G5 pinned-deck evidence remains valid for current `f516…eee0`.

## Boundaries, delivery and remaining work

The campaign began 24 Oct 14:38:15 UTC. The hour 12 observation at 25 Oct 02:38:54 recorded all nine model jobs terminal/cleanup confirmed, all eight rows open and no further model dispatch. The physical-freeze observation at 03:38:53 was explicitly **after** its 03:38:15 deadline: it confirms candidate bytes already fixed long before, not a retroactive observation. At 04:37:21, before the 04:38:15 decision deadline, qualified timing was explicitly NOT_ADMITTED.

The approved heavy-work cutoff was 13:38:15 UTC and the hard stop was 14:38:15 UTC, both on 25 October. This attempt ended early: both physical policies are consumed, model numerical STOP applies, timing lacks its admission prerequisite, and no additional physical/model/timing work is authorized. The final ledger and manifest record the actual adoption time before the unchanged hard stop. The successful proof did not widen the serial 4 GiB/four-hour policy. No push, publication, external contact or fabrication submission occurred; local commits do not back up all runtime evidence.

Delivery/adoption is controlled by a companion final ledger binding the exact committed report/hash, postcommit artifact audit and cleanup receipt. The report cannot embed its own commit/hash or create an audit-hash cycle. The final artifact audit retains 1 MiB/blob/25 MiB aggregate limits, the sole exact DEF-fixture exception, protected guards/contracts and separate known LEF line 113 blank-EOF lint failure. A budget pass is not a clean-lint claim.

Cleanup passed at **05:10:25 UTC** under reviewed helper 03: all **68** resource records were terminal with confirmed cleanup (32 completed, eight stopped, 28 failed). Failed engineering outcomes remain failed. The scoped process and named-container postflight lists were empty, the cleanup sentinel was absent, and the existing shared lock was acquired nonblocking and released. Only the lifetime-verified campaign `caffeinate` group (PID/PGID 10431) received SIGTERM and was confirmed absent. No other process/container was killed, no system setting changed, and historical records were preserved. This is a momentary campaign-ownership observation, not a global process-absence certificate.

The source checkpoint contains **42 local commits** after the baseline; this report is the sole 43rd commit. Delivery evidence is in [gate-ledger-16.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/gate-ledger-16.json) and [final24-ledger-closeout-manifest-01.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/final24-ledger-closeout-manifest-01.json): exact final commit/report bytes, completed postcommit [final24-commit-artifact-audit-06.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/final24-commit-artifact-audit-06.json), cleanup, and the matching append-only journal event. [final24-report-snapshot-01.md](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/final24-report-snapshot-01.md) is an exact byte snapshot. These records are written after this report's commit, avoiding a self-hash cycle. Raw evidence and all failed originals remain in the local campaign directory. The snapshot and manifest are local custody records, not a remote backup or a complete portable runtime archive. Nothing was pushed or submitted.

## Immutable evidence index

Local authority links below point into the retained campaign and resource directories. The Gate 4/Gate 5 aggregates carry their complete underlying evidence joins.

| Authority | SHA256 |
| --- | --- |
| [final24-canonical-gate4-independent-readback-01.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/final24-canonical-gate4-independent-readback-01.json) | `21249d9175afbf0729e62f03b9fa4370bc248fe48929e10fe5b66286d9fc3558` |
| [canonical-gate5-closeout-01.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/canonical-gate5-closeout-01.json) | `7a3bb16aacc815e474cf2fcbb8ea20650ef89e027b47b3d22d81bbb0d2ff12c4` |
| [final24-M-typed-join-positive-01/report.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/final24-M-typed-join-positive-01/report.json) | `62e185ebb7b975a66e4953b053fcbc9b3e3d93d22f77e5ee4ce71bec7a3d471b` |
| [final24-M-typed-join-positive-independent-readback-01.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/final24-M-typed-join-positive-independent-readback-01.json) | `a48f66fbb2c0683f149203641b2696e8cb92aec93c3b903955acfe326290394f` |
| [final24-M-typed-join-private-01/report.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/final24-M-typed-join-private-01/report.json) | `aae0d24fa618f6c4bb185b61c02d39a01b94172925735bc4ca599a70027a0453` |
| [final24-M-typed-join-private-independent-readback-01.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/final24-M-typed-join-private-independent-readback-01.json) | `a0df779d1145498d8da818a93f859421dac92b3ae46c75dd23f738b637ae64e9` |
| [resources/8x4-24-final-M-typed-join-positive-01/report.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/streaming-tt-resources/8x4-24-final-M-typed-join-positive-01/report.json) | `611bbb732570b4e98cb4614c38f6f5960b7fa912370aa221251c1d0fe714afdc` |
| [resources/8x4-24-final-M-typed-join-private-01/report.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/streaming-tt-resources/8x4-24-final-M-typed-join-private-01/report.json) | `fa26bafd1693acdca29c34c985522151f9e28924a7c4e431b0a210fdcce00fdd` |
| [prepared.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/final24-M-typed-join-01/prepared.json) | `7844f0b2424342c14c76fa060d4904ca96cfad040fd228748a8519048b0ba8f5` |
| [generation-manifest.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/final24-M-typed-join-01/generation-manifest.json) | `6cbc1eac0292e5b701f3cd0e2066b72c1c78e0cdca86ff3d3b51f4d2e3d2cef1` |
| [model24-final-eight-row-audit-02.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/model24-final-eight-row-audit-02.json) | `f4b7f039280c4b1afaa91278124ebbf79dc785c7154b461e95be583169def6ae` |
| [model24-via-independent-readback-01.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/model24-via-independent-readback-01.json) | `4ab1ee98a7987eeafbc5b73ebca898a2c7dc79d5c8c6ef64eeab00e4f543ba29` |
| [antenna-model-comparison-HOST-01/report.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/antenna-model-comparison-HOST-01/report.json) | `f3ecf963b09975f5b5ab75f336f0465e38c3fcf4a6be479c89ca235d3a00e3d2` |
| [model24-hour12-stop-observation-01.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/model24-hour12-stop-observation-01.json) | `e8f62e83b9883f8cdd825551b518b1cb6e2c983388dcff93aa3c8e6da8d8be24` |
| [final24-hour13-physical-freeze-observation-01.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/final24-hour13-physical-freeze-observation-01.json) | `3729691cae82e1d6d203cb1e2eb451bc9e9f6c74621f5dc9c01f2c979cd81f79` |
| [final24-hour14-qualified-timing-decision-01.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/final24-hour14-qualified-timing-decision-01.json) | `2ed426159471fad3669950b41014eb1421b6ebb3efed591dbc1285f1b98aa767` |
| [final24-cleanup-01.json](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/final24-cleanup-01.json) | `91ed15ed9fd2d4c9b47ff54108185341616f1a5ed827ea90c33c3a71920eb15f` |
| [streaming-8x4-closure-campaign-20261024.md](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/docs/research/streaming-8x4-closure-campaign-20261024.md) | `78409c501ec6d16e4952d0c0fd66e19693505adbdfaa822fc3409c041acf19dc` |


Full target ODB `f516ffbca3cd86e5cd214c515ca0be457a91a517dbe715caa47336aec907eee0`; GDS `5c1d5635b47023591a0e4f8d76b61b84a4d7ae9bdfa4183700bc955a4cd6261d`; logical Verilog `b8b0a29851369f2b181b67db77778979703a30adc92051e2992a2e8fb98dc971`.

Source checkpoint `f87de820de6be2786fd37d025ffa85553ffef053`; CAD image `sha256:5825633bea1f9cbc705ece2de2bc31de6e4ec83d233739205a0f265ef9d92f92`; OpenROAD `dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`; support `d66cf179e7bc4d296362ab7e2e3b344dc3c4f665`; Lean 4.33.1/full 14,923-file runtime as bound by Gate 4. Prior working reports and failed receipts remain preserved.

Historical primary-source availability references: [draft PR1237](https://github.com/IHP-GmbH/IHP-Open-PDK/pull/1237), checked head `ffdafdbb4abb17316fa0ffd221ea99c0475c4734`; [merged ITF PR1251](https://github.com/IHP-GmbH/IHP-Open-PDK/pull/1251), merge `9182b4ff461d90948ade30b1614d5000128cb9f7`; [issue1151](https://github.com/IHP-GmbH/IHP-Open-PDK/issues/1151); [issue1282](https://github.com/IHP-GmbH/IHP-Open-PDK/issues/1282); [checked dev configuration](https://github.com/IHP-GmbH/IHP-Open-PDK/blob/cb743f75aabc96e30450e9e53afc8d3c4867e5e2/ihp-sg13cmos5l/libs.tech/librelane/config.tcl#L97). These are not executed-model qualification authorities.
