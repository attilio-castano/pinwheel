# Routing and CMOS5L RC campaign — 19 October 2026

**Campaign outcome: the full tapeout-readiness goal remains unachieved.**

The full tapeout-readiness goal has not been achieved. The ordinary final-flow attempt exhausted a six-hour routing allowance without producing a completed final target. A separate bounded measurement produced an unclean diagnostic database and usable location reports. The campaign also recovered source-replay continuity and tested the capacitance solver under strict numerical checks. It has not established final implementation correspondence, qualified extracted timing, or physical signoff.

The approved window began at 08:59:42 UTC, with a maximum end of 20:59:42 UTC. New candidate experiments closed before 17:59:42 UTC; later work was fixed-target validation, review and reporting. Compute cleanup completed at 19:01:45 UTC. The [frozen plan](streaming-tt-routing-rc-campaign-20261019.md) and [execution journal](streaming-tt-routing-rc-journal-20261019.md) retain the contract and individual decisions.

## What the measurements establish

| Layer | Evidence and result | Limit |
|---|---|---|
| [Digital design][prior] | The retained source and optimized prephysical proof work covers the declared initialized, two-state digital model, all 6,039 semantic state bits and the established protocol capacities. | This predates placement, clock repair and routing. It cannot certify a later physical netlist. |
| [Six-hour routing measurement][final03] | Final03 timed out with exit 124. Its [107-artifact inventory][final03-inventory] contains no completed routing state or produced ODB. Across 56 completed internal optimization records, the best count was 1,623 and the last was 1,777 violations. | Internal counts are nonmonotonic diagnostic observations. They neither establish a clean route nor prove that routing is impossible. |
| [Bounded coordinate measurement][coordinate] | The router completed its declared call with a diagnostic state and 5,992 violations. Source/runtime postchecks and resource cleanup closed. The unchanged original closeout validator independently reproduced the results. | The HOST result remains failure 2 for incomplete earlier reports. The unclean diagnostic database is not a final implementation-proof target. |
| [Fixed-target geometry API check][geometry] | One read-only validation of that exact diagnostic database stopped at its first API check: the installed Python module does not expose `odb.dbShape`. The declared ELF/ODB hashes, read-only mounts and resource caps matched. HOST and supervisor cleanup/input checks closed. | The database bytes were hashed, but OpenDB never loaded or scanned it. No geometry or intersection output exists. This establishes the selected Python interface gap; other interfaces and the C++ class remain unassessed. No retry occurred. |
| [Source continuity after timeout][recovery] | The external recovery completed the unchanged full A03 source API, one fresh isolated HOST regeneration and revalidation of retained 395-positive/same-two-private proof evidence. It checked 29,290 consumed inputs and preserved 151 caches. | It ran no new Lean, CAD or solver commands. It did not repair the original timed-out receipt or turn it into an accepted final target. |
| [Coated-sphere control][coat] | The actual solver workflow passed the predeclared faceted-capacitance enclosure, with unchanged warning, matrix-physics, convergence and unit checks. | This supports that particular dielectric-interface compatibility check. It does not quantify finite-wire or process-model accuracy. |
| [Original finite-wire pilot][u-original] | The workflow closed with strict failure 2: iteration 0 warned about diagonal dominance and had a negative SIGNAL row sum. Later iterations recovered the physical screen. | Later recovery does not erase an earlier warning under the unchanged all-warnings-fatal rule. The original six-case suite remains unadmitted. |
| [Link-accuracy follow-up][u-follow] | The sole solver change was `-d3.83703e-36`, with unchanged geometry and numerical gates. The solver reported 6.55 seconds internally (6.57 seconds observed process time) before file-error exit 74. Iteration 2 estimated 1,977 MiB of interaction-link storage, while its temporary filesystem was 32 MiB. This is a storage estimate, not measured RSS or an OOM result. The outer supervisor confirmed cleanup. | The numerical workflow is failed and unaccepted. The unchanged matrix parser refuses its incomplete log. No convergence, reference accuracy, original-U promotion or six-case admission follows. |
| [CMOS5L process model][rc-intake] | A fresh official upstream intake reproduced 25 selected raw requests covering 21 objects and checked the selected PR/dev status against the morning pins. Those bytes and statuses are unchanged. The five-layer model proposal remains draft; merged ITF files do not close model qualification. | This was not a global search for new datasets. Generation provenance, consumer applicability, coverage, independent references and RC corner definitions remain open. |

## Routing diagnosis

The bounded coordinate diagnostic uses the same starting database, seed 42, tools, PDK, routing layers Metal2–4 and physical rules. Its declared changes stop after iteration 4, save interval reports and disable antenna repair for that diagnostic. This is a measurement protocol, not a replacement final flow or a final-proof target. The five completed internal counts were 41,449 → 29,969 → 30,815 → 8,535 → 5,992. Interval 1 serialized 16,869 records against 29,969 violations; interval 2 serialized 16,584 against 30,815. Those earlier location sets remain incomplete. Intervals 3/4 match 8,535/5,992, and the final report matches 5,992. The iteration 4 and final-base files are byte-identical and do not represent independent samples. The unchanged original validator subsequently passed its independent HOST reopen in 42.8 seconds, reproducing those exact usable and incomplete scopes.

The starting block is 1289.28×710.64 µm. Its 42,548 instances include 6,039 flip-flops. A direct sum of instance bounding-box areas is approximately 80.2% of the placement-row bounding-box area, including every instance kind. This sum is context, not a new overlap, legality, congestion or causal proof. Existing antenna cells must be distinguished from any later stage's insertion count.

Any accepted coordinate analysis must bind closed actual execution, full raw reports, the independent uncapped post-check count and matching iteration fences. Clipped reports remain incomplete. Seed-name context is restricted to exact net, instance and port lookups. Pin names, anonymous obstructions and empty source lists must remain explicitly unresolved where their prerequisites are missing; none of these labels establishes the cause of a violation or logical-source correspondence.

The exact initial dictionary resolved all 16,444 named references in interval 3 and 11,579 in interval 4. All were literal net-name references: 2,404 distinct names in interval 3 and 1,632 in interval 4. These are reference/name counts, not counts of causal or failing nets. These particular reports contain no pin, obstruction or empty-source references. Every raw record, repeated reference and original order remains preserved; this initial-name context does not establish a causal net or logical-source behavior. Broader pin-name support remains unadmitted. The [reference summary][names] and [Root authentication][names-auth] preserve the exact scope.

The final diagnostic DRC report contains 4,523 shorts and 1,467 metal-spacing violations, plus one minimum-area and one cut-short violation. Metal2 accounts for 4,453 of the 5,992 total. The four highest-count 100 µm bins, selected **after** observing the results, are:

| X range (µm) | Y range (µm) | Violations |
|---|---|---:|
|1000–1100|600–700|1,305|
|1100–1200|600–700|1,103|
|200–300|500–600|996|
|100–200|500–600|841|

These bins contain 70.84% of violation bounding-box midpoints and 4.88% of summed initial cell-bbox area. Their summed bbox-area/row-area ratio is 88.31%, compared with 80.19% globally. The fixed grid preserves all 104 bins and exact areas. This is a descriptive association, not a cause, cell-overlap check or legal-placement-density result. However, 62 other bins have a bbox-area/row-area ratio of at least 84% and zero final violation midpoints. That bbox-area/row-area ratio alone is therefore insufficient to identify a cause. The next study should first authenticate guide, pin-access and route geometry in those regions, then compare a controlled placement/routing intervention. The [complete CSV][spatial] and [Root authentication][spatial-auth] retain the descriptive data.

The subsequent fixed-target check preserved the diagnostic database and used the existing `cad-validation` allowance. The frozen six-file source version had 18 synthetic controls passing in normal Python and 18 under optimization, followed by independent source and packet reviews. Actual execution then resolved one uncertainty: the first selected shape class is unavailable through this installed Python module. It stopped before the script's target-database creation/read, so the geometric mechanism remains open. A later campaign needs a reviewed, compatible readback implementation before choosing a repair. The [independent outcome review][geometry-review] and [Root receipt join][geometry] preserve that narrow result.

## What remains before tapeout readiness

1. Obtain a genuine completed, clean route and connectivity result. Use measured violation locations to justify any next routing or placement change; another longer timeout alone is not evidence of a solution.
2. Export that actual target freshly, regenerate the complete 6,039-state map, and run full implemented-netlist correspondence, the original private controls, whole-proof auditing and actual final-target public-wire checks. Coverage must account for all actual implemented state and public outputs; matching a semantic-state count alone is insufficient. A diagnostic database cannot substitute for it.
3. Qualify the applicable CMOS5L extraction model and declared corners using independent resistance, capacitance, via and dielectric references. Bind actual extraction, SPEF annotation and timing to the same final database. Three Liberty cell-PVT corners sharing nominal RC are not three qualified RC corners.
4. Complete foundry DRC, overlap/connectivity, antenna, actual power connectivity, transistor LVS, final GDS/LEF/powered-netlist consistency and the unchanged applicable official TT checks. The selected nine official prechecks omit timing, LVS, antenna and CMOS5L power-pin checking; those remain independent obligations.

No readiness percentage is assigned. The strong digital evidence and the open physical obligations describe different parts of the claim.

## Validation, custody and remaining decisions

The campaign preserves failed and superseded attempts, reviewed source changes, meaningful normal/optimized HOST controls, actual launch commands, resource receipts and independent reviews. Local checkpoint archives are exact copies of selected original files; original execution paths and referenced runtime inputs remain the authority. They are not standalone reproduction bundles. Checkpoint 14, committed as `b9a7fc46`, retains 326 selected source/closed-result files. Root verified every original/copy pair and all staged Git blobs before that local commit. The [technical report review][report-review] checked retained report version `850f72fa`; the [final report review][final-review] covers the later additions and closeout. Device-goal acceptance remains false.

The original incomplete Final03 remains incomplete. After the external source recovery, Root separately joined the actual source result, launch/resource/terminal receipts and fresh cleanup observations in lease receipt 994696da. That action released compute capacity only. The historical journal hash referenced by an earlier synthesis was recovered exactly from Git in a separate receipt; the current mutable journal is not claimed to have that historical hash. The two inherited dirty documents remain outside campaign changes.

An optional download-and-save of pinned OpenROAD method source was rejected by automatic approval review, citing missing explicit authorization for that action. No workaround was attempted. That provenance gap remains explicit and does not qualify pin-name mapping.

The [final cleanup receipt][cleanup] records 28 terminal resource receipts with confirmed cleanup, a free heavy-job lease, no Native processes or running containers, and unchanged preserved inputs. It sent SIGTERM only to the exact campaign-owned keep-awake PID 84655 after matching its birth, command and original ownership receipt; that PID was absent afterward. The [last checkpoint][checkpoint15] retains the final validation, review and cleanup evidence. No further candidate, solver or Native readback is admitted in this campaign. Remaining design, proof, RC and physical gates stay open.


[prior]: streaming-tt-renewal-report-20261018.md
[final03]: local-evidence/README.md#artifact-4bf01153abeb
[final03-inventory]: local-evidence/README.md#artifact-236624056770
[coordinate]: local-evidence/README.md#artifact-1d7403809fd7
[recovery]: local-evidence/README.md#artifact-e57ec46bf17e
[coat]: local-evidence/README.md#artifact-d1e9b826ad79
[u-original]: local-evidence/README.md#artifact-c69b39ad47ba
[u-follow]: local-evidence/README.md#artifact-899c736de97a
[rc-intake]: local-evidence/README.md#artifact-f420fd0a7dfc
[names]: local-evidence/README.md#artifact-8ba565c373a1
[names-auth]: local-evidence/README.md#artifact-4b7f348a2aa0
[spatial]: local-evidence/README.md#artifact-2cd18714c569
[spatial-auth]: local-evidence/README.md#artifact-ae6549fd90d8
[geometry]: local-evidence/README.md#artifact-01cfda951e90
[geometry-review]: local-evidence/README.md#artifact-4ee89f7fa1df
[report-review]: local-evidence/README.md#artifact-c6d70a1e2843
[final-review]: local-evidence/README.md#artifact-a1ef1dc413d4
[cleanup]: local-evidence/README.md#artifact-016e56c54ab7
[checkpoint15]: local-evidence/README.md#artifact-951f29d9bc6f
