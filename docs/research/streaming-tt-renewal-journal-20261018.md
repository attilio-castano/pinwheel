# TT closure renewal: execution journal

The approved window is **2026-10-18 15:26:07 UTC through 2026-10-19
03:26:07 UTC**. New candidate CAD admission stops at 00:26:07 UTC.
The [approved plan](streaming-tt-closure-reactivation-20261018.md) defines the
unchanged design and acceptance conditions. Entries below distinguish passed
scopes, failed attempts and pending work. This journal is not a qualification
receipt or a completed morning report.

## Source integration and bounded proof preparation

Commit `1bbfecc` replaces the left-folded 64-leaf guard with a balanced
conjunction. A generic Lean theorem connects the balanced evaluation to the
original fold. The host witness checks all 64 leaves and unchanged state and
interface declarations. The critical integration replay rebuilt 14 affected
modules against 30 exact unchanged ancestors after excluding all 48 affected
cached objects and sidecars. It passed in 48.668 seconds, including source
refinement, initialization, loader equivalence and both legacy integration
roots. Receipt:
`build/streaming-tt-recovery/renewal-balanced-critical-03/report.json`, SHA256
`e181ea3ad6d2605ca61765e695b1b5e59bf6c63168c48ea438a915c42e6f6f10`.
This bounded replay does not replace the complete fresh source gate or fresh
mapped and implemented-netlist correspondence.

Commits `9df6b9c` and `c50ce46` bound finite clock proofs and keep concrete
public-output evaluation behind generic opaque lemmas. The historical old07
implementation's 90-module clock scope, all 24 public outputs and signed
803-buffer inventory now have closed native receipts. These results remain
specific to the old implementation and old 648-module foundation. They do not
certify the changed source or a newly placed design. Commit `f959bb4` prepares
bounded all-D/all-output endpoint proofs and a typed-state extensionality
helper; its host controls passed, but the generated Lean changes have not yet
been run natively.

## Fresh source gate: failed attempt and measured restart

`renewal-foundation-649-01` rebuilt 185 of 649 source modules before the outer
supervisor stopped the process tree at **5,253,824 KiB RSS**, slightly above its
5,120 MiB bound. Host memory availability was 84 percent. The supervisor's
original receipt records `cleanup_unconfirmed` and remains unchanged:
`build/streaming-tt-resources/renewal-foundation-649-01/report.json`, SHA256
`d639551a16a93bf0420bae2d6586ae2d0382b413328c5384a47a743d4cab067f`.
An independent later process observation confirmed the remaining owned PID
absent and no Lean/Lake processes. The original poison sentinel was retained
under an audited, exclusive-lock retirement rather than deleted silently.
The later closeout and retirement records are in
`build/streaming-tt-foundation/renewal-foundation-649-01/`.

At **15:54:19 UTC**, `renewal-foundation-649-02` started from a new clean
committed archive with a 6,144 MiB outer RSS bound. Lean remains at **4,096 MiB,
one compiler job, asynchronous elaboration disabled**. The full 822-input
controller source projection was checked byte-identical to the preceding
selected source wave; unrelated committed recipe and documentation changes
are separately identified by the archive commit. No prefix cache from the
failed attempt is accepted. The gate also compares the complete 14,923-file
installed compiler/shim/runtime identity before and after execution. Its
receipt and runtime companion remain pending until both close successfully.

The second attempt also stopped at the I2C certificate, at **16:07:17 UTC**,
with **6,329,008 KiB** process-tree RSS. The 6 GiB guard was retained. Its
original failed receipt remains at
`build/streaming-tt-resources/renewal-foundation-649-02/report.json`, SHA256
`57f9ec44d8a068bb559e8bec97c3db0bf94b98ce1ee4b9f1f962f9cc16e7082b`.
Independent later observations under the exclusive lock confirmed both
original owned PIDs absent, no Lean/Lake processes, and safe sentinel retirement.

The repair changes proof decomposition, preserving both public statements and
the remaining certificate source exactly. It checks all 1,024 endpoint cases
in 16 groups of 64 and all 270 validator cases in groups of 16, including the
final 14. An isolated native probe against 41 exact transitive ancestors passed
in **15.271 seconds**, with **1,735,696 KiB** observed peak tree RSS and full
runtime/input closeout. Its receipt is
`build/streaming-physical-development/i2c-certificate-bounded-renewal-unqualified-01/report.json`.
The exact tested source was promoted in commit `9f10a56`. The isolated pass
does not certify the other source modules.

The cleanup supervisor previously checked for remaining processes immediately
after asynchronous SIGKILL delivery. Commit `4922556` waits up to five seconds
for observed absence while preserving exact PID birth identities and failing
closed on observation errors or persistent processes. Thirteen focused tests
passed normally and under `-O`. The live control
`build/streaming-tt-resources/renewal-settle-cleanup-01/report.json` stopped a
separate-group, SIGTERM-ignoring owned child in 4.112 seconds; cleanup confirmed
no remaining owned processes. This expected timeout is a passed control, not
a successful application job. Commit `0644f9d` also preserves native validation
of explicitly frozen parents during the final reserve without reopening new
candidate experiments or extending the hard deadline; 15 focused tests pass
in both Python modes.

`renewal-foundation-649-03` is a new clean replay of archive
`0644f9dc75fe5763dc8525435a1b5a0788febe39`, including the committed certificate
repair. It reuses no prefix proof objects from either failed full attempt.
Its complete runtime pre-scan passed and source compilation is running. The
canonical gate and runtime companion are pending at
`build/validation/renewal-foundation-649-03/report.json` and
`build/streaming-tt-foundation/renewal-foundation-649-03/report.json`.

## Physical and extraction preparation

The isolated corrected PDN fixture passed its native generation/readback and
the unchanged official pin checker. It retains all 43 public pins and exports
52 full-height Metal4 power stripes with at least 640 DBU measured clearance.
The closed receipt is
`build/streaming-physical-development/pdn-clearance-unqualified-02/report.json`,
SHA256 `3754a1f7bc2ff189d545b27de105fb5a8a4d0b42901ba2e09bad4c8a53057aeb`.
This fixture does not establish candidate power connectivity or full DRC/LVS.

Commit `9abfd35` requests and checks delivery of explicit eight-sink CTS
clustering. All 392 old overloaded clock nets are FF-driving leaves, while
the old upper branches already meet the limit. The old automatic run also
reported size eight, so the trial requires measured actual topology and
electrical results before attributing a benefit to the setting. See the
[controlled trial](streaming-tt-cts8-trial.md).

Read-only upstream research found merged CMOS5L ITF/process-stack work in
[IHP PR 1251](https://github.com/IHP-GmbH/IHP-Open-PDK/pull/1251), independently
of the still-draft extraction tables in
[IHP PR 1237](https://github.com/IHP-GmbH/IHP-Open-PDK/pull/1237). The intake
retains exact upstream commit and blob identities as data. No downloaded
generator or field solver has been executed and the shared PDK is unchanged.
Merged geometry inputs alone do not qualify draft extracted-RC models.

## Mandatory gates still open at this checkpoint

The complete fresh source gate, new raw components and controls, new semantic
state bijection, optimization replay, placement/CTS/routing, correspondence
to the actual new implementation, public/private axiom audit, qualified
extracted timing, electrical and power checks, DRC/LVS/antenna, and unchanged
official full precheck remain open. No tapeout-readiness claim is made.

## Fresh source gate closed at 17:12 UTC

`renewal-foundation-649-03` completed successfully from the clean committed
`0644f9d` archive. It checked **649 modules, 44,383 declarations and 25,323
theorems**, all **65 executable suites and eight kernel suites**. Both the
untrusted-axiom and unused-private-axiom controls were rejected. The source
gate took 3,424.669 seconds; the outer supervised job closed in 3,435.557
seconds with unchanged inputs and confirmed owned cleanup. The full 14,923-file
runtime identity remained unchanged. The sampled peak process-tree RSS was
3,875.6 MiB; this is a sampled observation, not an operating-system peak claim.

Closed receipts and SHA256 identities:

- `build/validation/renewal-foundation-649-03/report.json`:
  `81fd894827acd13248bc2f1f12851c35fa87ff342176a796781dd9128f288379`.
- `build/streaming-tt-foundation/renewal-foundation-649-03/report.json`:
  `e20245ec401769745a17a59beec4170ef058692262c711366bc5cdcea01fdb0e`.
- `build/streaming-tt-resources/renewal-foundation-649-03/report.json`:
  `e872c87264023a2d242a88bfadb5de8c9b52c71f75fffff5a6a4d989303ceb44`.

The actual fresh-foundation binding to frozen logical candidate `72ba31d`
passed its complete source-projection, log, runtime and object checks. It
contains 1,298 positive library artifacts, with the separate negative-control
module retained and excluded. The binding is recorded in
`build/streaming-tt-recovery/balanced-real-binding-01/report.json`.
This closes the fresh source gate listed as open above; it does not close the
new candidate's raw, optimized or actual physical correspondence gates.

## Lowering measurement and between-job supervision

The new raw run starts from candidate `72ba31d` and the closed source binding,
retaining all 19 original negative controls. A new host diagnostic attributes
the old raw guards by checking all 256 count/payload assignments for each of
64 leaves. The old frontend has an isolated tail-guard AND depth of 63; the
old core's complete guard context has depth 64, with seven additional context
leaves. Their global consecutive one-bit AND depths are 67 and 71. These are
raw structural observations, not mapped timing or whole-state proofs.
Frozen diagnostic source is commit `5ab1553`; baseline receipts are in
`build/streaming-tt-recovery/balanced-raw-depth-baseline-02/`.

The old CIRCT export flattened associative AND expressions. The new raw run
must therefore measure whether the source balance survives lowering before
optimization and CAD. If it does not, a separate bounded pilot will test a
lowering-only metadata copy and export settings, preserving the original MLIR
as the typed source authority. The existing raw bridge supports associative
regrouping; any successful production change still requires a new committed
candidate and a complete fresh raw gate. A partial or aborted attempt cannot
be promoted to a completed gate.

After the source job had closed, commit `a05da0e` repaired the supervisor's
same-name container replacement race. A failed observation of old container A
is accepted only after a new query proves A absent; a replacement B is recorded
and receives its resource checks on the next sample. Ambiguous ownership and
persistent-A observation failures still reject. Seventeen focused tests passed
normally and under `-O`, including a replacement violating memory, swap, CPU
or network limits. Independent review cleared the exact patch. Resource caps,
candidate cutoff and hard deadline are unchanged.

## RC preparation advanced; qualification remains open

A new source-only intake verified 8,338 Git blobs across complete pinned
FasterCap, Geometry, LinAlgebra and official wxWidgets source trees. The receipt
is `build/streaming-tt-rc-research/solver-source-intake-unqualified-02/report.json`,
SHA256 `648d2a06f6f86fc8c9c25d4e8e3376c29f7372b4092aac029897ca7a47bd0c59`.
The failed first intake is preserved: archive CRLF transformations differed
from Git blobs, and the second intake accepts normalization only when bytes
exactly recover each pinned blob. No downloaded source was executed, no solver
was built and no shared PDK was changed. Offline compiler/build-tool usability,
the reviewed Native geometry/runner, numerical convergence and independent
physical comparisons remain open. The 61-solve pilot plan is preparation only.

## Export balance recovered; frontend certificate still open at 17:53 UTC

The actual `72ba31d` raw frontend retained the old isolated tail-guard depth
of 63. That run was intentionally stopped after this measurement, with owned
cleanup and unchanged inputs confirmed. Its partial artifacts are preserved;
they are not a completed raw gate and did not complete the 19 controls.
The closeout is
`build/streaming-tt-resources/renewal-balanced-raw-01/intentional-stop-closeout.json`,
SHA256 `8554adf33eec1912449281a01d2a7f430673dbda780f7d8449dc8fd5888be557`.

A separate lowering pilot preserves the original emitted MLIR as the typed
source authority, changes only one exporter-metadata header in a separate
copy, and omits CIRCT canonicalization. Setting the maximum terms per exported
expression to two produced depth nine and failed the predeclared limit of
eight. The new one-term attempt met that unchanged limit: the same 64 guard
predicates have isolated AND depth **six**, with global consecutive AND depth
11. All 28 frontend registers, 1,403 register bits and 17 output fields remain.
This is a structural measurement, not mapped timing or a complete certificate.
The depth receipt is
`build/streaming-physical-development/lowering-balanced-fallback-terms1-attempt-unqualified-01/depth/report.json`,
SHA256 `242d9f2c32b408184a6a6334f5e23aa1032d450c640a70e5e3eb90b8782311ca`.

The first full frontend pilot exhausted the unchanged 6 GiB process-tree cap
before Lean compilation: its audit wrapper repeatedly retained and rewrote
all earlier SMT input maps. A new immutable attempt uses per-command input
bindings and append-only records, with a final rehash of every consumed input.
Host controls cover linear metadata growth and tampering with an earlier SMT
file. It completed 1,181 SMT proposals with sampled peak RSS about 794 MiB.
The next blocker is the generated `Sources` Lean module's 180-second timeout;
fresh `Hints` compilation passed. The outer job closed with unchanged inputs
and confirmed cleanup, but no full frontend certificate or mutation-control
pass is claimed. Separate bounded diagnostics reached the first 15 equations
before stopping at `last_reply`; an isolated CRC/reply equation probe is next.

The changed export also changes generated word-module membership. New replay
validation must derive its exact ordered module/source map by independently
regenerating the complete new parent. The historical 392-module inventory
remains specific to the old candidate; no module may be dropped or padded to
retain that number. Production lowering, a new source/producer binding, all
19 raw controls, actual optimization and the physical gates remain pending.

Offline tool inventory found usable compiler, CMake and binutils version
commands but no Make or Ninja. A complete pinned GNU Make source intake and
an offline bootstrap plan are ready. Five homogeneous-sphere smoke cases now
have exact mesh checks, analytic bounds, a source-derived output parser and
bounded worker host tests. The solver has not been built or executed, and
these preparations do not qualify process-stack RC models.

## Frontend certificate closed; fresh whole-component gate active at 18:44 UTC

The proof bottlenecks now have closed native results. Factoring three shared
source expressions preserves all 45 public equation statements and reduces
their compilation to 29.546 seconds. A narrow, independently checked sparse
bit-mask recognizer supplies bounded kernel proofs for eight of the 842 local
clauses; it refuses shifted, foreign-variable, wrong-mask and unsupported
expressions. The complete frontend pilot then passed all eight positive
modules, both output mutations and its private-axiom rejection control. Its 1,206
native commands closed with unchanged inputs and confirmed cleanup in 90.992
seconds; sampled peak process-tree RSS was 1,420,592 KiB. The certificate is
`build/streaming-physical-development/lowering-balanced-fallback-terms1-attempt-unqualified-04/certificate/report.json`,
SHA256 `f0dd0a20adb4bc2b231ffa3bf020aaa4cd9169f9e3291d9e33b02d70ca112542`.
Failed diagnostic attempts remain separate and unchanged.

Source-proof generation is committed in `ac86ed6`; the lower-only exporter
change is committed in `e2e8e38`. The latter is the frozen logical source and
producer for the new full raw gate. The selected 649-module foundation remains
usable because all 793 source-projection files and 822 runtime-projection
files match exactly; its complete 14,923-file runtime and 1,298 positive
library artifacts were rechecked. The new binding receipt is
`build/streaming-tt-recovery/balanced-real-binding-02/report.json`,
SHA256 `12c30a5a0a1de82ad6cfc975198b9802f9d53e7d6038bd3e5cd073bf402196fa`.

The fresh gate `streaming-tt-balanced-raw-02` started under the unchanged
6 GiB process-tree cap, serial bounded Lean and hard campaign deadline. It
retains all 19 original controls and both depth-two/depth-four component
families. The actual production frontend component has passed, including
state/output correspondence and its controls. Core compilation is still
running. Actual lowered frontend and depth-two core each preserve isolated
64-leaf guard depth six and global consecutive AND depth 11. The full raw
receipt, optimization, fresh mapped-state correspondence and physical flow
remain open; no routed timing improvement is claimed.

The exact-parent replay inventory is committed in `3a83e60`. It independently
regenerates the complete ordered module/source map from the selected immutable
parent; the old 392 count is not an acceptance condition for this candidate.
New final-proof preparation will consume closed source dependencies and
regenerate implementation-specific modules from the actual export. Commit
`fc0068b` makes the final clock-domain count explicit rather than inheriting
the old 803 default. This later physical-proof producer change does not move
the logical candidate away from `e2e8e38`.

The separate RC research lane remains environment-blocked. The pinned image
has no Make, AWK or diff. Complete build-source intake is retained, and an
official signed static helper package has been verified as data. Its first
native smoke attempt stopped before executing the helper because PATH lookup
did not find its private AWK/diff aliases; that receipt did not record
enough mount evidence to establish the cause. A new host-tested smoke plan
adds explicit executable scratch and actual mount/access diagnostics. It
awaits the single native lease after the current raw gate. No solver build,
numerical result or process-stack RC qualification is claimed.

## Whole fresh raw gate closed at 18:54 UTC

The complete `streaming-tt-balanced-raw-02` gate passed from frozen logical
source/producer `e2e8e38`. All four stages passed, including the frontend,
depth-two and depth-four all-state/output component proofs, private audits,
wrapper checks and exactly 19 expected rejections: 16 semantic mutations and
three private-axiom controls. The run recorded
4,682 actual native commands. Core source-equation compilation took 351.955
seconds for depth two and 357.391 seconds for depth four, both within the
unchanged 900-second per-module bound. All three actual raw components retain
isolated guard depth six and global consecutive AND depth 11.

The canonical receipt is
`build/validation/streaming-tt-balanced-raw-02/report.json`,
SHA256 `5bd0d0889787f9022b00fc97bb11eb6a0f685fe5fc72cb9b0fdebfc4fa4752d3`.
The worker receipt SHA256 is
`0523637252d7dd4b3c832bb5a30bf8138101cc6fca1b69ecc12cb27ef76c9ecc`.
The resource closeout is
`build/streaming-tt-resources/renewal-balanced-raw-02/report.json`,
SHA256 `a0ab72752f5ee462004ca0291722d4815b9bb31fa2d967073a8086dc598be03c`:
terminal exit zero, 963.723 seconds elapsed, confirmed owned cleanup, no
remaining owned processes and unchanged inputs. Root independently rehashed
all resource-bound inputs. The partial raw01 and separate pilot receipts
remain unchanged; this is a new complete gate.

Optimization and physical measurement are next. Host preparation rechecked
all 49 committed physical-producer files, the completed pinned PDK, corrected
power-grid geometry and explicit eight-sink CTS recipe. It performs no CAD
and establishes no routed result. Commit `ff4e7fb` adds the missing explicit
memory-equals-swap bound and OpenROAD `-no_init` to the actual-ODB exporter;
11 focused host tests pass normally and under `-O`, with independent review.
These two paths are outside both the frozen raw inputs and 49-file coarse
producer closure.

The actual routing admission requires complete independently closed source
replay plus its separate two private controls before detailed routing. It
does not require an intermediate GRT implementation proof. Final implementation
correspondence must instead use the actual final ODB after detailed routing,
repairs and filler/clock changes. The actual-target proof generator is being
prepared against that scope; no implementation proof result is claimed yet.

The separately leased helper03 smoke then passed all eight actual processes:
applet inventory/banner, three AWK fixtures and diff exits zero/one/two. Its
4.342-second outer run closed with unchanged inputs, no remaining owned
processes or containers, and independent exact-name container absence. The
private helper's actual executable scratch, access, bytes, aliases, ELF,
35 tools and runtime identities remained unchanged. Closeout:
`build/streaming-tt-rc-research/alpine-helper-smoke-preparation-unqualified-03/host-closeout.json`,
SHA256 `7adf96b48b3f15b0e9ad0f5cbabe86c242c276464747edee6d17c00ee0cfefb3`.
Root independently checked the reports, eight process results and all guarded
inputs. The solver itself has not been built or run; a new execution-ready
build plan must bind this successful smoke rather than rewriting the frozen
placeholder preparation. Optimization and initial physical measurement have
the next native-compute priority.

## Complete optimized-device proof and intake closed at 19:16 UTC

The complete optimized worker passed from the same `e2e8e38` source/producer,
including its all-state whole-device kernel join and 25 API names. The
independent intake regenerated the proof sources, checked all nine acceptance
conditions, and reimported the actual SystemVerilog. Every actual cell/pin
structure, all FF D roots and public outputs matched the kernel-interpreted
JSON. All 6,039 state bits remain. The actual independent source inventory is
**395 modules**: 161 frontend, 228 core and six device modules. A fresh replay
of those modules and the original separate two private controls remains
required before detailed routing.

Whole-device mapped measurements against the exact old `f801` worker:

| Measurement | Old | New |
| --- | ---: | ---: |
| Longest unweighted combinational gate path | 114 | 64 |
| Total mapped cells | 29,002 | 29,802 |
| Liberty cell area, square micrometres | 606,637.1178 | 612,878.6538 |
| Semantic state bits | 6,039 | 6,039 |

Area rises about 1.03%. Frontend path depth is 114 to 64 and core depth is
82 to 49. Exact path witnesses confirm that the long serial AND chains have
largely disappeared. These measurements establish mapped structure and
functional correspondence; routed timing, congestion, electrical limits and
physical acceptance still require fresh native physical work.

The new immutable controller03 fixed a report-directory mismatch discovered
in controller02 during host review, before any native work. The intake API
adds `parent-intake-` itself; controller03 passes the plain `balanced-02` tag
and verifies the exact expected output path. Two host tests check the actual
committed API convention. The unused controller02 remains preserved.

Closed evidence:

- Parent intake:
  `build/streaming-tt-optimization/parent-intake-balanced-02/report.json`,
  SHA256 `f49053aab54c09c171357d090336dfca0d3c1a28892df4cd3c4808ccc9481656`.
- Independent replay plan:
  `build/streaming-tt-optimization/parent-intake-balanced-02/native-replay-plan.json`,
  SHA256 `e2ffe5a0a051924f5fb60b007d4db8186a5735e9844e658be0e905a9f4c8085c`.
- Whole worker:
  `build/validation/streaming-tt-balanced-device-02/worker/report.json`,
  SHA256 `71b93782be3ac886fc1aa9dab86465b6b1528085567412dc06a79485b1f8cb87`.
- Controller:
  `build/streaming-tt-optimization/orchestration-balanced-03/execution-report.json`,
  SHA256 `6277295e76cf8e9de7958fccb4fbb43447ab3bdcb1a6d4e61e0b6fece536a3fe`.
- Resource closeout:
  `build/streaming-tt-resources/renewal-balanced-optimized-03/report.json`,
  SHA256 `a45485fb1ffe22e557dd82e5e7da3c3db3a8df7c5053078f85c4cbbc141f14dd`.

The outer job closed at exit zero after 706.127 seconds, with confirmed owned
cleanup and unchanged inputs. Root independently rehashed all 19,723 prepared
inputs and the complete 351-file canonical Python membership. There are no
remaining owned processes. Physical preparation and the coarse run now have
native-compute priority.

Host review also found a predictable source-replay timeout: the old runner's
180-second default cannot cover the newly closed core source module, measured
at 354.006 seconds under its accepted 600-second parent limit. A new immutable
runner/checker family will derive a narrow per-module allowance from that
closed parent command and exact source hash. Default limits, proof bytes,
candidate identity, foundation, global resource caps and the physical 20 ns
contract stay fixed. No independent source replay has been claimed yet.

## Physical preparation closed; coarse run started at 19:29 UTC

Both native Yosys preparation reimports passed. The complete cell/pin and
semantic-state checks retain all 6,039 bits, and the staged PDK contains the
verified complete 405-file membership. Preparation closed after 25.761 seconds
with exit zero, unchanged inputs, and no owned processes or containers.

- Prepared design: `build/physical/streaming-tt-balanced-d2-01/inputs.json`,
  SHA256 `4fc4d7a3e336cbe8a327fd7ca33bfb17ee5996ca5dacdb9f4a08a0a88b3231d5`.
- Preparation resource closeout:
  `build/streaming-tt-resources/streaming-tt-balanced-d2-prepare-01/report.json`,
  SHA256 `91bab0c208f8de4f47f94cdf65e1595107d0448d3ea0b511428b96a092a2cdd2`.
- Frozen coarse plan:
  `build/streaming-physical-development/balanced-physical-handoff-unqualified-02/coarse-plan.json`,
  SHA256 `6680c61fc876e7209f07649fc2459e6d39cd55542c7f750dd51250de810919bb`.

Root independently checked all 550 coarse inputs, the prepared-input verifier,
preparation cleanup and the unused output path before granting the separate
coarse lease. The actual run began at **19:29:03 UTC**, session 6532, through
`OpenROAD.STAMidPNR-3`. Its native Docker command has four CPUs, 6 GiB memory
and the same total memory-plus-swap limit, no network, the pinned image, and
read-only design/PDK inputs. Inner/outer ceilings are 3,600/3,660 seconds,
clipped by the campaign deadline. This is the sole heavy native job.

The run will establish actual placement, clock-tree delivery, global-route
timing and congestion measurements. It has not yet completed. Detailed routing
still requires the complete independent 395-module source replay and its
original two private controls. Final implementation correspondence and all
physical signoff gates remain open.

## First physical obstruction: global-route congestion

Coarse01 stopped at global routing with exit two after 130.5 outer seconds.
The resource closeout is
`build/streaming-tt-resources/streaming-tt-balanced-d2-coarse-01/report.json`,
SHA256 `0af0cee4b074d048f491d0ec1ab8df8d74d344eaaf2ee18c82f04bf847275dac`.
Owned cleanup completed, no containers or processes remain, and all 550 frozen
inputs still match; Root independently rehashed them. There is no completed
global-route state or global-route ODB. The latest closed state is
`30-openroad-stamidpnr-2`, consuming the actual post-CTS-repair ODB from step 29.

Fresh typical-corner placement-estimated timing at that ODB is setup slack
8.939695 ns and hold slack 0.055351 ns, with zero typical-corner setup, hold,
slew or capacitance violations. **Fast and slow corner fields in the carried
state were stale pre-CTS observations.** Root caught and corrected the initial
all-corner interpretation before another native run. Fresh three-corner
timing remains necessary; none of this is qualified extracted timing.

The actual typical-corner check report identifies nine fanout violations:
eight upper clock drivers each have 16 loads against the unchanged limit of
eight, and `input1/X` has 13 loads. The explicit CTS clustering size of eight
worked for its leaf clustering, but did not constrain every upper branch.
Complete actual-ODB load/FF-delivery inventory is being prepared.

The global router exhausted 50 congestion iterations with 251 overflow units:
25 on Metal2, 211 on Metal3 and 15 on Metal4. Total derated capacity is 501,137
versus demand 312,169; Metal3 has 78.02% aggregate usage. These aggregate
numbers do not rule out local hotspots. Signal/clock layers remain Metal2
through Metal4, with a global 30% resource reservation. OpenROAD documents
this adjustment as an artificial routing-track reduction intended to spread
routes; its flow guidance describes tuning it by repeated global-route runs:
[global routing](https://openroad.readthedocs.io/en/latest/main/src/grt/README.html),
[flow variables](https://openroad-flow-scripts.readthedocs.io/en/latest/user/FlowVariables.html).
An estimator adjustment cannot establish detailed-route or DRC acceptance.

Area growth is measured, not presumed to be logic cloning: post-placement
repair inserted 4,334 buffers and 6,926 tie-cell copies (659 low, 6,267 high),
with zero resized cells. Placement grew from 29,804 instances/612,893 square
micrometres to 41,072/694,672; CTS added 1,099 instances, followed by eleven
hold-repair cells. The latest ODB has 42,182 instances, all 6,039 semantic FF
bits, area 719,938 square micrometres and utilization 79.7788%. The failed run
and every input remain preserved. The next step is a bounded actual-database
and three-corner diagnosis before choosing the next physical change.

## Fresh three-corner diagnosis and exact repair proposal

The separately bounded actual-ODB readback and fresh three-corner STA both
closed at exit zero, with unchanged inputs and complete owned cleanup. Root
independently checked their input hashes and the actual fresh corner reports.
Every result below uses the unchanged post-CTS ODB
`a5c9815a4f1322c385bbbec1f08ae31a83f17ce80d1e58483d692dc4044cb35d`:

| Fresh nominal-wire estimate | Setup slack, ns | Hold slack, ns |
| --- | ---: | ---: |
| Fast, 1.32 V, -40 C | 10.0883 | 0.0218729 |
| Slow, 1.08 V, 125 C | 4.0613 | 0.154829 |
| Typical, 1.20 V, 25 C | 8.9397 | 0.0553511 |

All three have zero setup, hold, slew and capacitance violations, and each
still has the nine fanout violations. Their explicit assessment is rejected.
These are freshly calculated placement-based nominal wire estimates; they
provide no extracted-wire, RC-corner or tapeout qualification.

- Readback resource report: `build/streaming-tt-resources/streaming-tt-balanced-cts8-readback-01/report.json`,
  SHA256 `fb6df39e1273647caf5ffc268b39fb11e90d44d17ac64de92f4750167f20649c`.
- Fresh STA resource report: `build/streaming-tt-resources/streaming-tt-balanced-cts8-sta-01/report.json`,
  SHA256 `75da839549ec666acd6e6dae6010f0b028c54cbaf142dd59683e576e54e4634e`.
- Actual fresh STA result: `build/streaming-tt-sta/streaming-tt-balanced-cts8-sta-01/native/report.json`,
  SHA256 `3d24ee26a3d5eeff6439623df38243c01b6123ea65b7ea5a69cc215be12aaf10`.

Actual readback confirms 914 clock nets, root-reachable positive clocks for
all 6,039 FFs, and 776 FF leaf nets with at most eight FF loads. The eight
upper branches have sixteen buffer loads each. All 186 unused clock outputs
(131 positive, 55 inverting) remain visible in the inventory.

A preferred ten-clone host proposal closes the complete upstream load
partition: eight upper buffer clones, one root clock-buffer clone and one
signal-buffer clone. Full pin projection checks all loads at most eight,
retains every original instance and contracted pin identity, and preserves
the exact four-buffer positive clock depth of every FF. Public clock loads
increase from one to two. Actual placement, database roundtrip, clock-input
loading and fresh three-corner timing still require native validation; the
small fast-corner hold margin matters. The proposal is
`build/streaming-physical-development/balanced-upstream-repair-proposal-unqualified-01/report.json`,
SHA256 `c66ffab31b18937606c14da26bacb943f71b70b836263b4d65d627a4300e1f2c`.
It requires a new explicit post-CTS derivative profile. Existing fixed-clock
admission policies remain unchanged.

## Source replay preparation and host-validation performance

Commit `ca26fdf` adds a private invocation-local host boundary that performs
one real isolated source regeneration while retaining all live input,
membership, source, library, runtime, producer, import and receipt checks on
every call and at exit. No scope crosses a native operation; no cache survives
the invocation. A real 395-module host benchmark measured 83.500 seconds
across entry, two repeated checks and exit, with one 32.146-second child and
all 11,781 input identities checked. The final environment-bound variant
passes ten host tests normally and under `-O`, independently reviewed and
also rerun by Root. This addresses fourteen redundant child regenerations
per implementation-proof host boundary; it does not establish a new proof.

Actual independent source-only replay preparation now contains exactly
395 byte-identical sources, split 161 frontend, 228 core and six device,
with zero compiled targets. Root compared the complete ordered source/SHA
map with the original independent parent. The new reviewed N03 checker
retains the source-bound 180/600-second policy, shares the checked canonical
interpreter and closes the immutable-plan hash race. The source-only plan is
`build/streaming-physical-development/formal-balanced-e2-replay-unqualified-01/plan.json`,
SHA256 `152f1e5e3aeb0de339b6d0e35ce05724f31b4dd786ba78bfa0786c18b5e0bb0b`.
Native execution, its original two private controls and strict replay intake
are still pending. The upcoming controller freezes all 351 current canonical
Python files for its execution; physical preparation proceeds in separate
owned build directories during that interval.

## Offline RC build: concrete nested-Make failure and bounded retry

Build05 bootstrapped GNU Make successfully, then stopped when wxWidgets'
nested Expat configure called bare `make mkdir-init`: the newly built Make
directory had not been exported into PATH. It failed after 30.836 seconds
with complete cleanup and unchanged inputs. Its failed resource receipt is
SHA256 `207427a2786e9f86a9ab5eca47edf02de43d50d1cc57aafd095751a4bd09086b`;
all frozen artifacts and failed outputs remain unchanged.

New immutable build06 adds one owned shell line exporting the bootstrapped
Make directory into PATH. A host nested-shell regression reproduces the old
exit 127 and passes with that exact line. Root reran ten tests normally and
under `-O`, rehashed all 37 frozen artifacts and refreshed the actual host
preflight before granting the separate build lease. Plan SHA256 is
`c686b042cca5face70e37a84d78abee6622bf6a48eff0761510674f39cad7615`;
command SHA256 is
`7769acd750cde42f4d68d5466a97ff787bbe5246783325be19d318c8228d297d`.
Build06 is running under the unchanged 1,200-second outer ceiling, two CPUs,
6 GiB memory with no extra swap, pinned offline image and read-only intakes.
It does not run FasterCap automatically. Actual runtime ELF/loader/library
closure, a separately bounded sphere suite, process-stack numerical checks,
independent reference and manufacturing-corner qualification remain gaps.

## 20:10 UTC checkpoint: build closed, independent replay progressing

Build06 has now **passed and closed**: actual Make, wxBase and FasterCap
compiled and linked in 75.973 seconds. Its resource guard exited zero with
cleanup confirmed, no remaining owned process or container, and unchanged
inputs. Closeout SHA256 is
`f7c4ec1191223ea33c1ec8666bea4dbc0907f33b7e5b1c5eba64cf6df8da89a4`;
resource report SHA256 is
`0daa7ca1c929f99ee380e6db561dc484d950ef7ffa3e38a5daf22cd582a09dbe`.
The produced 331,256-byte FasterCap binary has SHA256
`b78b4938eb3e301653cee76808de12a5c37a5c567477f247b535a8319a1037d1`.
It has not executed. Runtime dependency collection, actual loader behavior,
analytic sphere controls and process-stack numerical qualification remain
separate obligations.

The independent 395-positive-module replay is running under guard
`renewal-balanced-frozen-replay-01`. Its 161-module frontend stage has closed
successfully. The longest core source module also compiled successfully
within its predeclared 600-second bound; the core stage and device stage,
the original two private controls, strict intake and complete input/runtime
closeout are still pending. All 351 canonical Python files remain frozen
until this controller closes. A successful prefix is not a completed replay.

The ten-clone post-CTS diagnostic plan is frozen at SHA256
`5f1c1520ea0bb26485bc9dc0dc1f90a71a42c52df5588669675268bb3a227670`.
Root reviewed the producer and all 646 frozen inputs, then independently
passed its seven host controls normally and under `-O`. This remains a host
preparation result. The precise proposed load changes include both public
`clk` and public `ena`, each from one to two input loads. Native legalization,
database roundtrip, all original placements and pins, all 6,039 clock paths,
fresh input loading and three-corner timing must pass before admission.
Its Native lease waits for the proof controller's complete cleanup. The
separate routing experiment will retain physical tracks and design rules
while reducing artificial global-routing reservation from 30% to 20%.
Detailed routing and extracted signoff have not completed.

## 20:25 UTC: independent 395+2 replay fully closed

The independent frozen replay has **passed and closed**: 161 frontend,
228 core and six device modules compiled freshly, followed by the original
two-command private-axiom control with exact expected exits zero and one.
The unused private axiom was explicitly rejected. The assembled receipt
joins all 397 original commands and journals; strict replay intake passed.

- Replay intake: `build/streaming-tt-optimization/replay-intake-balanced-e2-01/report.json`,
  SHA256 `2bdf6da15598ea03362a788fa918e0df50b3aaf1613672bfe2f6136f582224fa`.
- Controller: `build/streaming-physical-development/formal-balanced-e2-replay-execution-unqualified-01/execution-report.json`,
  SHA256 `f16d890dce2719480545f498f39fd5afe740519d80c9ea604a84257ee2bbd012`.
- Resource closeout: `build/streaming-tt-resources/renewal-balanced-frozen-replay-01/report.json`,
  SHA256 `6f4dfc974de9162bb99a020167f6e6f632c9ee22bd0f36c8319f8b56ebfc0e60`.
- Independent closeout: `build/streaming-tt-recovery/balanced-frozen-replay-closeout-01/report.json`,
  SHA256 `96d79347d3706ddae4b64520de91c5815d0819c760cc24cd0273cd3990190fcc`.

Session 95460 exited zero after 1,891.207 seconds. Peak sampled owned RSS
was 4,306,656 KiB. Cleanup and unchanged inputs are confirmed, with no owned
process remaining. Root and the independent reviewer each rehashed all
28,197 inputs and the exact 351-file regular canonical Python membership;
14,923 runtime files and all four phase receipts remained bound. The
duration-only canonical freeze is released. The four permanent source-replay
authority modules remain unchanged for the later actual-netlist proof.
This closes source correspondence and replay; final routed correspondence
and physical signoff remain separate.

## 20:32 UTC: targeted physical retry and closed runtime metadata

The first ten-clone run failed before creating any clones because OpenDB
does not accept placement status `FIXED`. It closed after 16.892 seconds,
exit one, with complete cleanup and all 646 frozen inputs unchanged.
The failed resource receipt is SHA256
`da62fc72b241d4db315aaa5cc7d29ecc7d0cb9b3b943e575f85754d6ff0d6ff5`.
All first-attempt artifacts remain unchanged. The exact pinned
[OpenDB API](https://raw.githubusercontent.com/The-OpenROAD-Project/OpenROAD/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/odb/include/odb/dbTypes.h)
defines `LOCKED` and its fixed-placement semantics. New immutable attempt02
uses that value and asserts actual `getPlacementStatus()` and `isFixed()`
for every original instance before placement. Its eight controls passed
normally and under `-O`; Root independently reran all eight, reviewed the
narrow change, and rehashed all 646 inputs. Plan SHA256 is
`de0911f1dd05e92562909f257c5dfce8d6e388b791b2711ddc31aecac9aaefcb`.
The bounded retry is authorized; its actual geometry and timing results are
still pending. No routing or physical acceptance follows from preparation.

Between the two physical attempts, the separate data-only runtime collector
passed and closed in 3.313 seconds. It identified ten ELF nodes and 24
dependency edges under explicit paths, with all 26 frozen preparation files
and 220 guard inputs unchanged. Its resource receipt is SHA256
`b82878112b5e465f7e4167f1c1b318755386880a335cea69805b8f53cabf4e53`;
Native metadata report SHA256 is
`5a11c1f711f2cc3e6ee423ebba2e1412cff0061e20bd25323213a324b4df15d5`.
Cleanup and independent exact-name container absence are confirmed. It did
not execute FasterCap, its loader or `ldd`; runtime admission remains false.
Actual solver execution, analytic sphere controls, process-stack calculations,
independent reference and manufacturing-corner qualification remain open.

## 21:00 UTC: ten-clone repair closed; routing export retry running

The ten-clone repair has **passed and closed** in immutable attempt04.
Attempt02's 100-micrometre vertical placement window left two new buffers
unplaced. The actual row-gap investigation found candidate gaps beyond that
window; attempt03 used 150 micrometres and legalized all ten new instances
while retaining all 42,182 original placements. Its database and fresh timing
checks passed, but the workflow incorrectly expected timing status
`accepted` where the canonical assessor returns `passed`. Attempt03 remains
a failed run. Attempt04 repaired only that status contract, added an actual
canonical-assessor control, and reran the complete workflow successfully.

- Final repair database SHA256:
  `323ded586fdd6cc37a051781ecaad67c026605622187c79d0b836c9d4f84c591`.
- Attempt04 host report SHA256:
  `a3e32a6f4d0e191774616fe51e846bdce28c02c1adefc0b3f873c5fa5696e437`.
- Attempt04 resource report SHA256:
  `7c16e240f780b7c4ddd178543810629066f9737a9787437526a9e729bd1a148b`.

The run exited zero in 67.009 seconds with complete cleanup and unchanged
inputs. All 6,039 semantic flip-flops retain their positive, depth-four clock
paths. All original placements, instance identities, contracted connectivity,
public pin geometry and power connections survived the written/read database
roundtrip. The ten clones increase total instances to 42,192. Both public
`clk` and `ena` now have two loads. Fresh fast, slow and typical nominal-RC
timing reports have zero setup, hold, slew, capacitance and fanout violations;
setup/hold slack is respectively 10.0896/0.0293373, 4.05536/0.25899 and
8.90504/0.125224 ns. These are nominal estimates, not extracted signoff.

Global-routing attempt02 reached zero overflow on all three actual routing
layers after reducing artificial reservation from 30% to 20%. Actual tracks,
layer limits, physical rules and the 20 ns clock constraint remained unchanged.
Its follow-up export failed because the embedded Python launcher omitted the
frozen worker directory from its import path. That complete attempt remains
failed; no routed topology or timing acceptance follows from its successful
routing prefix. Cleanup completed and all 826 frozen inputs remained unchanged.

New immutable attempt03 inserts the exact worker directory before `runpy`.
An actual isolated-Python host control reproduces the old missing-sibling
import and passes with the repaired launcher. Root reviewed the complete
delta, reran all eleven controls, and rehashed all 826 frozen files and exact
827 guard inputs. Plan SHA256 is
`212c1e22fe728f959bb6b70f46b4a892232476945dda4959b6aeb8ceeb6ba1a8`;
preparation seal SHA256 is
`3622b8f6271dc8f8873fb4cbcef11b974419b01673586b03ab4a528e7cdf27b8`.
The exact bounded run is authorized and running. Full global-route acceptance
still requires its actual export, preserved topology and fresh routed timing.
Detailed routing, final-netlist correspondence and physical signoff remain open.

The five-case analytic sphere execution packet is independently host-reviewed,
with seventeen controls passing normally and under optimized Python. Root
reproduced the normal controls under the exact isolated, no-site Python
environment, and checked all 59 frozen artifacts, 247 guard inputs and the
284-entry runtime bundle. This is preparation only; no solver execution or
RC qualification has yet occurred. The separate RC run waits for the routing
job's actual cleanup under the single-heavy-job policy.

## 21:02 UTC: routed timing exposes fast-corner hold repair

Attempt03 has now closed with typed exit two and complete cleanup after
82.604 seconds. Its actual routing, export, structural inventory and all
three fresh timing commands executed successfully. Zero routing overflow,
all original track resources, all 42,192 placements, all 6,039 positive
depth-four clock paths, contracted connectivity and public/power interfaces
are preserved. Root rehashed all 826 frozen inputs unchanged.

The actual timing assessment correctly **rejects** this intermediate state:
the fast corner has 16 hold violations and worst hold slack -0.0663482 ns.
Fast setup slack is 9.81689 ns; slow setup/hold is 2.54003/0.238113 ns;
typical setup/hold is 8.71389/0.0693592 ns. All setup, slew, capacitance and
fanout violation counts are zero. These are fresh, propagated-clock,
global-route estimates, not qualified extracted timing.

The host report SHA256 is
`f88292a38c4ffcc09a3e604d8547244a2cee32fdb216d501fbe56107ff838677`;
resource report SHA256 is
`73cb02be7e662d1ffab0f0cfa5918e2144124378b30dc9461a71fb236325a55d`.
The immutable failed run is retained and detailed-route admission remains
false. The installed standard flow provides a post-global-route timing
repair step before detailed routing; its exact configuration, source and
affected paths are being inspected before a bounded continuation is proposed.
No timing check or constraint has been relaxed.

After the routing lease closed, Root authorized the exact five-case sphere
packet under a separate 360-second, one-CPU, 2 GiB offline lease. Its actual
solver result and complete cleanup are pending. It cannot establish process
RC qualification by itself.

## 21:39 UTC: analytic solver pilot closed; standard timing repair prepared

The five-case analytic sphere pilot has **passed and closed** in immutable
attempt05. Attempt03 exposed an actual runtime error: the restricted child
PATH omitted the admitted `uname` binary, selecting an obsolete free-memory
parser. Attempt04 repaired that exact lookup and ran successfully, but its
host parser incorrectly treated the normal accuracy header as an error.
Both failed attempts remain preserved. Attempt05 recognizes only the exact,
source-derived, pre-iteration accuracy header and continues to reject the
original runtime error and malformed, duplicate or misplaced headers.

All five actual solver cases exit zero, have non-exhausted convergence
receipts and pass analytic bounds and scaling checks. The full guarded run
took 7.366 seconds, including 5.36 seconds of Native work, with complete
cleanup and all 59 frozen files, 255 guard inputs and 284 runtime entries
unchanged. Root independently rechecked those bindings, actual result
membership, numeric screens, runtime observations and container absence.

- Attempt05 host closeout SHA256:
  `54a33854e86fbd0a0459b7bc880fc4ee084b6fc36d7deb1a5e66c6cd8a7d56f3`.
- Attempt05 resource receipt SHA256:
  `7635d931a824b5e40f5bb627067e0c8601670346135e2e38b4d05d669b2c6296`.
- Separate Root scoped runtime review SHA256:
  `f27d57b754909db6f365f2925c9338ac250dd1dc0417b431e15d72a6a2fc5d98`.

This admits the exact contained runtime for bounded development geometry
pilots with fresh per-case supervision. It does not qualify an RC model or
manufacturing signoff. The finer sphere mesh changes the inscribed geometry;
its capacitance difference is not a fixed-geometry mesh-convergence result.
The next HOST packet selects only four existing development wire cases from
the frozen typical-corner suite; held-out geometries remain unused.

The actual flow configuration has `RUN_POST_GRT_RESIZER_TIMING=false`.
Root authorized a new candidate enabling that ordinary timing-repair step
and retaining its existing 0.02 ns hold margin, 0.025 ns setup margin,
three-corner configuration, 20 ns clock, routing resources and physical
rules. The complete seven-step standard prefix is retained with its ordinary
configured skips. Acceptance requires positive data-buffer contraction,
unchanged original logic and complete clock topology, an explicit placement
move ledger, legal placement and fresh three-corner routed timing. The
failed routing parent supplies repair evidence, not acceptance.

Frozen repair02 plan SHA256 is
`0cd225b803948b2afb7695922d43600e93b282056111a5031f26ed7cc63a8231`.
Its host preparation seal is
`c5e4f8f6dea7f9a359b4f90d1cbcf0b47713bc0f84d4409093f0d727383789d8`.
Root rehashed all 1,050 frozen files and exact 1,051 guard inputs unchanged;
six host control groups pass. Native launch awaits the independent review.
The earlier unexecuted repair01 packet is preserved after review found an
unlisted-symlink import seam and a missing fresh flow directory. Repair02
rejects unexpected symlinks before imports, preserves only the exact official
PDK alias map, uses isolated Python entry points and creates the fresh run
directory at the actual CLI boundary.

The separate source-ordering inspection has closed successfully; it confirms
the ordinary detailed-route tail exports a new netlist before equivalence
checking. The final continuation remains conditional on successful repaired
timing. No detailed route or actual final-netlist correspondence is claimed.
Commit `fdf3ca5` preserves 49 reviewed operational source files byte-for-byte
with their original identities and explicit archival scope for restart
recovery; those archived copies are not reported as executed producers.

## 21:45 UTC: standard repair completed, with explicit downstream failures

Repair02 completed the ordinary post-route repair prefix and produced actual
database SHA256
`8781fb5eea580b5972e77a5eea931b0b3c7708eeca904c2fc9fed04be66cce43`.
The prefix receipt is
`fe4e302bf529a5d08d79c6e3250009cffc93760a9560a534a484ac6546a04cc0`.
The overall candidate **failed and closed**, because its unchanged positive
data-buffer profile correctly rejected standard antenna cells before fresh
three-corner timing could run. The host report is
`b574ea14264c254ea1792f6da779be7e0f3959094baec02e6791e641afe85127`;
resource receipt is
`394197b64e31e2763f4ae0c7c80ed8c59b1d1d10044095e260bcac758e1701d4`.
The actual guard exited one after 164.528 seconds with cleanup confirmed and
no remaining owned processes or containers. Root rehashed all 1,050 frozen
inputs unchanged. No timing acceptance follows from the completed prefix.

The actual completed DEF reports 42,390 instances: the original 42,192,
171 antenna diodes and 27 hold-delay cells; all 6,039 semantic flip-flops
remain. Standard antenna repair reduced its reported violations from 93 to
zero. Source inspection identifies the new `antennanp` cells as input-only
digital sinks with actual rail-clamp devices, and the `dlygate4sd3_1` cells
as positive Boolean identities with real delay arcs. They need an explicit
source-bound profile, not a renamed or hidden actual inventory. A proposed
comparison projection will remove only validated new diode sinks and
normalize only validated new positive delay identities, while preserving
the full actual inventory and retaining real electrical behavior in timing.

HOST inspection of that native-written DEF also exposes a concrete physical
failure: 13 data nets exceed fanout eight after diode insertion, with maximum
fanout 17. The 171 diodes attach to 76 data nets, with no old clock-net
attachments. These observations are not an independent database readback.
The next bounded read-only diagnostic will obtain the full actual database
roundtrip and fresh three-corner timing, retain structural failures, and
remain rejected if either structure or timing fails. A subsequent fanout
repair needs an independently reviewed candidate; no limit is waived.

The four-case typical-corner capacitance pilot also **failed and closed**.
Its closeout is
`fdee8b0e788d8b96f5e3d512461ec2dacdd33afde06bf0922b491e38de4216de`;
resource receipt is
`fda678946eef0a27eb8375786eaa27887945e6a2bfc0644acaa97d4d3b5c7657`.
The guard exited one after 11.470 seconds with complete cleanup. Only the
first development case started. Its process-observation receipt has an
unknown solver exit code after `/proc/7/exe` disappeared while an immediate
poll still reported a running process. A log footer is not treated as exit
evidence. Separately, the actual log has eight skipped-quadrilateral
warnings and one diagonal-dominance warning; all remain fatal to admission.

Root and the RC owner independently traced the geometry cause to the pinned
solver source: the quadrilateral reader compares the unnormalized Newell
normal against the absolute `C3D_OP_TOL=1e-12`. The signal end face has a
nonzero normal magnitude about `1.344e-13` in metre coordinates and is
therefore skipped. This is a coordinate-scale tolerance problem, not a
collapsed face in the independent geometry certificate. A new, separately
certified coordinate-unit representation and explicit capacitance-unit
conversion are being considered, with analytic unit-invariance controls;
the original frozen 61-case suite is untouched.

Post-run checks preserve all 132 pilot files, 327 guard inputs, 284 runtime
entries, 80 selected geometry files, the complete 1,185-file original TYP
tree and the full historical sphere03/04/05 snapshots. No wire-case result,
calibration, model qualification or physical acceptance has been admitted.

## 22:09 UTC: independent readback and fresh timing retained

The source-bound passive/positive-delay checker has passed seven meaningful
actual-parent HOST control groups normally and under optimized Python, with
Native subprocesses blocked. Root independently reproduced all seven normal
groups in 79.950 seconds. Its source SHA256 is
`43f945842764115889c619ba63d1357caf627fd37ab3799242aca3081301f6ff`;
independent review receipt is
`2d417e3b611f9f4b7155656f684cae1359a0dccb6998423f1e5fa8c82a85fe8c`.
It retains the complete actual inventory, explicitly labels the temporary
Boolean projection, and rejects actual fanout violations even when the
projected comparison passes. No actual diode or delay cell is replaced.

The first read-only diagnostic packet was held **before Native execution**:
independent review found reuse of a populated OpenROAD `Tech` object, a
known failure under the exact pinned runtime. Immutable packet02 instead
uses an independent OpenDB database for readback, a pre-write fixed-geometry
snapshot and exact 1,000 database units per micrometre. Root reproduced its
eight HOST groups and rehashed all 1,264 inputs; independent review
`264431adb69acab351a38a388345ef4a8b4c8090243f9952ea00a8478ba16285`
cleared its source, effective 1,265 guard inputs and API correction.

Actual diagnostic02 then completed both Native commands: full independent
readback, legal placement, public/power geometry, written/read database
roundtrip and fresh propagated-clock routed estimates at all three corners.
The raw export is
`0223c92a7134054d2cf549a7183d107002e96de8075ab39d5343c6dba747fb9d`;
fresh STA receipt is
`9393be7e28b50f00251f285c742c7f05db9cdcbe054ff1a945f53e21100585b0`.
All 42,390 instances, the 171 diodes, 27 positive delay cells and all 6,039
positive depth-four flip-flop clocks are retained.

The actual timing assessment **rejects** the intermediate: fast-corner hold
improves to seven violations and -0.0231356 ns, with setup 9.79746 ns.
Slow setup/hold is 2.38336/0.257037 ns; typical is 8.27749/0.0676136 ns.
Setup, slew and capacitance violations remain zero. All three corners report
13 fanout violations, matching the independent full actual load counts.
Detailed routing remains unadmitted.

The Native workflow correctly returned diagnostic exit two. The outer host
validation then failed on a tuple/list serialization comparison in the
recomputed function profile, giving outer exit one. The original reports
remain unchanged: host SHA256
`c47cba59ae489dfc67e235dd7697290c0c1cb5230e99e85d989a2babc29e5142`,
resource SHA256
`c9e23240f9932f4032e775d3c6c2bedb0e310ac1e38ed3fedecc85225ca9f675`.
The 100.168-second guard closed cleanup with no remaining owned processes
or containers and all 1,264 inputs unchanged. A separate HOST-only strict
reopen is being prepared; it must normalize the JSON boundary, recompute
every check, and preserve both structural and timing rejection. Native CAD
will not be repeated solely for that host comparison repair.

The targeted fanout proposal now uses 32 downstream positive buffer branches
with at most six actual sinks each, including diode loads. This preserves
upstream input loads and avoids a recursive cloning cascade. Provisional
BUF4 selection has ample pin-capacitance margin in all three libraries;
wire capacitance, slew and delay still require actual routing and STA.
Fresh antenna checking is mandatory after moving diode connections.

The normalized six-case RC packet02 is HOST-frozen and under independent
review: two exact accepted-Sphere05 controls at coordinate scales 2^20 and
2^21, followed by four original development cases at 2^20. Both controls
must bind the exact same accepted four-file physical sphere, not merely
similar capacitances. Root reproduced all 38 HOST groups and rehashed all
155 frozen files; no Native run is claimed. The plan SHA256 is
`1a4985c638205ef04220ac9c8ec42688cf6b10e1b091e29a7259c548f87ce11e`.
Original suites, failed receipts and the unexecuted normalized01 packet
remain preserved. Raw matrices and exact physical-unit conversion stay
separate; model, corner and manufacturing qualification remain open.

## 22:21 UTC: diagnostic closure and two independent repair targets

The separate HOST-only strict reopen completed successfully, with Native
subprocesses blocked. It reran the entire original validator using canonical
JSON comparison at the tuple/list boundary; it did not bypass the validator
or rerun CAD. Its report is
`b23796ba7f8873950e017a9c9bc8113756ee74a998ed5797f61c928fb44d603d`.
All 1,361 consumed hashes and all 179 actual-attempt files remained exact.
The original outer exit one and Native diagnostic exit two remain recorded;
structural, timing, overall and detailed-route acceptance remain false.

The hold causal diagnosis is
`a03710f6e25ba81bc5d1eb2dcd0b1e8500733fd9fa25a8b2868844e15dd73e73`.
The actual resizer loaded all three corners. It repaired hold to about
+0.021 ns before ordinary detailed placement, mirroring and rerouting;
fresh timing after those steps showed -0.0231356 ns. Placement/parasitic
drift is supported by that sequence, but the exact responsible substep was
not isolated. None of the seven remaining failing data paths crosses the
13 overloaded source nets. Fanout repair is therefore not claimed as the
hold repair. The next combined candidate uses an internal ordinary hold
repair target of +0.10 ns instead of +0.02 ns, with the same 20 ns clock,
all three corners and unchanged acceptance limits.

The deterministic 32-branch HOST proposal now uses the existing positive
BUF8 master: BUF4 had no actual equal-master rail template for the unchanged
canonical actor. The final plan is
`e0a2377d5dbf2abf2c46642058a23460ea1c42164711057ff622231095548c18`;
its HOST seal is
`f4317f0de694ee082cd2672f40da54fded0d0a1c302ac52b93b9df08a65dd4e0`.
Seven control groups passed normally and under optimized Python. The
projection retains all 42,390 original instances, 209,348 original pin
endpoints, the 171 diode and 27 delay contracts and complete clock topology.
Every overloaded root drives two or three BUF8 inputs; each new branch has
at most six actual sinks, including diodes. The 32 cells add 754.7904 square
micrometres of library area. Wire load, placement, antenna repair, electrical
checks, timing and final correspondence still require actual execution.

The normalized six-case RC packet02 actually ran and closed with rejection:
closeout SHA256
`66ee72b9e6128c5d1503d824af69eccf4ff76e213609a60f62e36a3abc0d2ef1`.
Both exact Sphere05 unit controls passed, with identical converted physical
capacitance `56623/524288000000000000000` F. The first wire case exited zero,
passed runtime/geometry observation and emitted no skipped-face warnings,
but emitted one diagonal-dominance warning at its initial iteration. That
warning remains fatal; no training case was admitted and the other three
were not started. All prior frozen inputs and failed artifacts were retained.
A new HOST-only proposal subdivides each original rectangular face 2 by 2,
with independent exact rational coverage, boundary, orientation and material
checks. It preserves the physical surface; no solver tolerance, warning or
accuracy condition is relaxed. No Native execution of this new packet is
claimed here.

Local commit `b2b5e0c` preserves 32 reviewed controller sources byte for byte
under `closed-snapshot-02`; its README distinguishes these archival copies
from the actual consumed build-tree paths and inputs. The source manifest is
`6cd9ce30cbc0d1433fab1e75c135d35c314f0f2f7ab2d9c1e966d1c4ea35cf80`.
The two inherited dirty documentation files remain untouched.

## 22:29 UTC: finer RC pilot rejected; combined physical candidate frozen

The separately reviewed 2 by 2 tessellation packet ran under the one-CPU,
2 GiB, no-swap, offline 465-second bound. Root and independent review each
reproduced all 46 HOST groups normally and under optimized Python. The
independent review is
`3b705a240b0b5e4b114d9f4370197e8a5dba8f511a43b5ce4adc583073ddcaff`;
plan/command/freeze are respectively
`4fce9dd1b4cbcae9c81db3803b18dd0843c49cb190b4410998331aa549e9e628`,
`6b185e170e1d7f258f87331f4e06179412c221351c98a6b7fe0a360ac893373f`
and `16327c393a2337fe90f22afbfce65294db79a09f93f19d2138fd29c3722903c6`.
Its independent reader proves that 520 tiles cover the 130 original faces
exactly, including orientation, names, material sides and external boundaries.

Both unchanged sphere controls again pass and give identical converted
physical capacitance. The first wire solver exits zero in 1.701 seconds,
with 273 coherent samples of the ten main runtime nodes and a closed process
group. It still emits two diagonal-dominance warnings, both fatal. The
Native worker, container and outer job therefore fail; no wire case is
admitted and no remaining wire case starts. Actual solver exit zero is
distinct from pilot acceptance. No warning or convergence condition changed.

Resource report
`817348c357036f5d7246d746a096c4cfd11e8da22b955ab793b63a94dbb3a4fd`
closes in 8.463 seconds with all inputs unchanged and no owned process or
container remaining. The separate Root HOST closeout
`112621b5020bae9e1aa6eb1775cb8e8774d12288fa17c741556c4e14651fa339`
rechecks all 161 frozen files, 355 guard inputs, the full original TYP tree
and historical failed/accepted snapshots with subprocesses blocked. Native
report is `3399d22c4795abd29fdf0fc89b66ea33398d022fb4ae2e3890124d2b875ab92b`.
RC-model and manufacturing qualification remain false. There is no automatic
larger-mesh retry; physical routing and final correspondence take priority.

The combined 32-BUF8 / +0.10 ns hold-target candidate is HOST-frozen at plan
`43af7025030e7b9a7a4f1cd49c4928a1832ba7c15a95736ab4d41a5ca6be044f`.
Root has independently reproduced nine HOST groups in 19.677 seconds,
read the full Native/host source and verified all 1,466 current input hashes
and exact 1,467 unique guard paths. Independent full review remains pending
at this entry. Native output is empty; no candidate execution is claimed.
The initial 32-branch application must match the canonical projection
exactly. Ordinary later optimization may alter only those new branches,
with a complete retained/removed/resized ledger; every original 42,390
instance/master and source pin/clock contract remains strict.

One conservative diagnostic limitation is explicit: the separate unchanged
42,390-source oracle also enforces fanout. A refusal there is fatal and can
stop export before fresh STA, even if the global passive profile has already
reported a typed fanout failure. This cannot produce acceptance. Fresh STA
continues after an explicit global structural false only when the separate
source contract closes. A failed source contract may require a separately
bounded read-only timing diagnostic; the frozen packet is not rewritten.

## 22:35 UTC: actual 32-branch partition passes; one routing overflow rejects01

Independent full review cleared the combined frozen candidate:
`dfe8309336b39b2eff40b182af096fce9d2624d25964e12626ec1dab424252f5`.
It independently reproduced nine normal and optimized HOST groups, all
1,466 input hashes, exact 1,467 guard paths and staged source/input/PDK
membership. Root granted the separately bounded Native run of that exact
plan; the sources and frozen packet were not modified.

The actual initial 32-BUF8 partition passes canonical topology comparison,
the complete 42,390-source pin/clock contract, legal placement and independent
database roundtrip. It takes 38.01 seconds and produces ODB
`756f9b79a648f21ccf370754e51f30c36de2e1ce1ed27b07d4657b069f901e61`.
The ordinary continuation then fails its first global-routing stage after
50 overflow-repair iterations: exactly one Metal4 overflow remains. The
reported final total is `0 / 1 / 1`; every other layer has zero overflow.
The tool explicitly suggests lowering the capacity reserve from 20% to 16%.
No post-route hold repair or fresh timing ran in this failed attempt.

The workflow is
`63ae5cba5c70502375326dec9040ef7d9016f53600380272d0b3c53da8f61247`;
host report is
`60090897b82b89acfd683337a2cafeb6071304858499afd7b2bfa2fd7f2a4089`;
resource report is
`1561b653a0456c3021a40be94097142b3709cc2f24904d019b236ceb4de114fa`.
The outer job exits one in 81.933 seconds, with full cleanup, no owned
process or container remaining and all 1,466 original hashes still current.
The failure is retained without acceptance or a rewritten receipt.

A new immutable02 variant is authorized for HOST preparation: keep the same
source, exact 32-branch plan, complete ordinary schedule and +0.10 ns hold
target, and explicitly change global capacity reserve from 0.20 to 0.16.
The actual physical tracks, layer limits, rules, footprint, clock and all
acceptance conditions remain fixed. Zero overflow is still required;
congested routing is not admitted. Native execution requires review of the
new source delta, controls and frozen packet first.

`closed-snapshot-03` archives 15 reviewed source/protocol files byte for byte,
173,758 bytes in total. Manifest SHA256 is
`7f6ee67533771f866dfd63336f31553a5f36a07b6eaed34ad79dd942e7c3e027`.
These archival copies were not executed and are not standalone projects;
the manifest retains actual consumed build-tree paths. Both inherited dirty
documentation files retain their original hashes.

The independent RC diagnosis locates the two tiled-pilot numerical warnings
in iterations zero and one. Later positive row sums and the final reported
convergence metric do not promote the rejected run. Source/support intake
also verifies the official nine-check inventory and frozen support/PDK
inputs, while actual final PG, DRC/LVS/antenna, extracted timing and the full
official precheck remain open. The clean RC PATH selects a license-blocked
Apple Git stub; Root separately verifies working `/opt/homebrew/bin/git`,
version 2.50.1. Future HOST precheck can pin that executable. No Xcode license
was accepted or requested.

## 23:03 UTC: routing reserve closes; raised hold targets fail placement

Immutable candidate02 is reviewed at
`4d44041226a47bf9eb95ee1fdcc3e57b351456271c0dd2f11a0c519370e63976`
and actually runs plan
`1390bc3c542d67a5c05ffa365907c6f46a84520d4773b930983e499ba683ad73`.
Routing at 16% reserve reaches zero overflow. The +0.10 ns internal hold
target then marks 5,242 endpoints for repair, reports +11.8% area and
+0.100 ns internal WNS, but detailed placement fails on 918 instances.
There is no completed timing-step ODB, fresh STA or physical acceptance.
Resource `01dedc25e20d1a34f4a776180fe4b78ccb08364eb93df5a007456516c4d0f9e0`
closes failed in 294.651 seconds with cleanup and unchanged inputs;
host is `5515e6a50284b1194ac0f216b3e88a828afb2c49fb064c97b73ae8b1042a83cf`.

Independent HOST parsing of its completed pre-timing RepairAntennas DEF
counts all 44,703 signal/clock nets and 124,542 endpoints. It finds 96 new
diodes, giving 42,518 instances. All 42,422 prior masters and connected
signal endpoints are retained. Eleven nets now exceed fanout eight, maximum
14; every excess is caused by these new diode loads. The diagnosis is
`709234c4c136fd3182ce19d8832320e626b366f5876a14a698d646939af4ffb3`.
This is an intermediate diagnosis, not a final physical or timing result.

Candidate03 changes only that internal hold target to +0.06 ns with explicit
hold060 profile/tag; reserve, tracks, rules, footprint, clocks and acceptance
remain fixed. Root reproduces nine normal/optimized HOST groups in
20.448/20.102 seconds and verifies all 1,466 inputs and 1,467 guard entries.
Independent review is
`ded754bcddfa7a16c3fc7371579149633acece58611f415b35f0d0ca4f5a39ee`;
actual plan is
`b8992a4f39a3c5a8f4025d74b33e8e5d386e0bda91ed82601c8aa7cad8ce836a`.
It too fails the timing step's detailed placement, now on 349 instances,
after reporting +7.3% area. No fresh STA or completed timing-step ODB exists.

The hold-buffer log counter is not a trustworthy cumulative census. Its
value drops during rollback while area remains accumulated; pinned upstream
source analysis identifies a counter reset on journal restoration. The
terminal reported counter must not be described as actual added-cell count.
The trace reaches about +0.050 ns before a broad +0.052 ns plateau; a single
new +0.05 ns internal-target experiment is being prepared from that measured
threshold. No further blind raised-margin search is planned. Zero actual
setup/hold/electrical violations at every corner remains mandatory.

## Source-to-final handoff and same-proof layout preparation

The full fixed replay admission actually revalidates all 395 positive and
the same two private commands, 29,290 consumed hashes, canonical interpreter
membership and six complete source/proof trees in 218.418 seconds. Only its
already-reviewed isolated HOST Python regeneration child executes; proofs
are not recompiled. Observation receipt is
`3b83484927fc83817bb2982f88be18da5886b8c562da5288735df15f8e1e7b0b`.
A separate actual retained-diagnostic mapping witness closes all 6,039 FF
names, pins and sequential functions in 3.539 seconds:
`41e5fd5339ba8eac310f94cc2a8a345ec5948472f7ba014de34d572e6e246198`.
Neither result selects a final DRT target or proves actual M.

Final-flow HOST source review preserves the complete ordinary tail and its
source/PDK/input mounts. A common subprocess observer now binds both Tcl and
Odbpy OpenROAD invocations, inserts `-no_init` once and retains every other
argument; Root reproduces seven normal/optimized groups. The proposed final
Native budget is 900 seconds, outer 1,620 seconds, with pre/post complete
source replay and explicit distinction between budget timeout and actual
owned-process exit. Physical admission still deliberately pins a failed
parent and cannot start until a current candidate actually closes.

GEN04 is a separately frozen HOST optimization: all 3,966 generated Lean
modules and 220,262,451 source bytes are exactly equal to GEN03, in the same
global dependency order, on retained diagnostic inputs. Normal/optimized
whole comparisons take 134.074/136.404 seconds; all 15 original families are
retained as diagnostics, while one Native stage replaces 15 stage boundaries.
Every individual Lean process, proof body, namespace, scope, memory limit
and private control remains unchanged. No authority cache spans Native.
Preparation is
`b57c90296b8735eb57a3b30dcdffe1f1d5f7b7aca6844dbad1949094967e6af8`;
whole comparisons are
`6fc0bc7ade2dd74731440a6fdf138818ad646cb9351843592611b105bce1d396`
and `128d86a75e619ed2b3d8cbd92863008faf562ad75b5ab897f1bd8842ac6cc2eb`.
This removes repeated full-generation validation between families; it does
not establish a final module count or guarantee completion time.

## 23:09 UTC: final measured hold-target trial admitted

Candidate03 closes failed in 234.621 seconds with complete owned cleanup and
unchanged frozen inputs. Its resource receipt is
`b787a875e6d6d66333e67d603dacbd71678e9385280f6d08c9a978894574bac3`.

Root rehashes all 1,466 candidate04 inputs and verifies the exact 1,467 unique
outer guard paths. New owned sources, staged inputs and plan are read-only;
Native output is initially empty. Independent review is
`ea62c4c0c79940f832069003ebb3e041e2c5fd4cd56e062d9226d8fc56cec0bc`.
The actual guarded plan is
`9a2d791c26e39be9049db094f96185082c5d1ddca3f9d11904773831a0430312`.
It runs with 1,020 seconds outer, 960 seconds inner, four CPUs, 6 GiB,
no swap and no network. This is the single measured +0.05 ns internal-target
trial described above; actual placement/timing/electrical acceptance is
unchanged. The preceding container is absent before admission.

Root also reads the complete new M-handoff delta and reproduces seven original
and four variant controls normally and under Python optimization. Every
mapping/admission/regeneration function body remains identical to the old
handoff; only the actual fixed admission path and reviewed GEN04/resolver06/
private03 pins change. No final target or Native M is admitted by those tests.
Current final-flow cache-owner and pure-preparation dispatcher controls pass
seven groups normally and optimized. Its physical admission deliberately
continues to pin failed candidate02 pending an actually accepted replacement.

Snapshot04 preserves 24 reviewed source/test/protocol files, 398,275 source
bytes. Root independently verifies every archived byte against its actual
original owner and manifest. Manifest SHA256 is
`bc432fb85df8321f90de5a61f56e3ea6be6497f0c5598d0d4a3f8b50d29b7bfd`.
Interim final-flow admission is explicitly labeled unready and still bound
to failed02. Neither archived copies nor HOST controls establish Native M,
final routing, RC qualification, signoff or tapeout readiness.
The independent M-handoff review receipt is
`610e9f66285418eab1d681785697cb8f9805b5770e204272ee0f1f25a16e029b`.

## 23:12 UTC: measured hold plateau avoided; rerouting now limits closure

Candidate04 actually closes failed in 242.817 seconds. Unlike the larger
targets, +0.05 ns marks only 67 endpoints, reports 66 hold buffers and reaches
legal detailed placement and mirroring. The subsequent ordinary global route
fails with overflow 43: Metal2 12, Metal3 27, Metal4 4. Its tool recommends
reducing the routing adjustment. The buffer figure remains a tool log value,
not an independently exported actual cell census. No final repaired ODB or
fresh all-corner timing is accepted from this failed step.

Resource receipt is
`281078a4333781102dd041d6fd55d578a85cc4a71d863f4dffe56e03da6cbd7e`;
HOST receipt is
`3fc8cc9dcf0a0240b33e813bb04ab8bdc24ae6535388ba379dd297b29793a0d6`.
Root rechecks all 1,466 inputs unchanged, typed exit one and complete owned
cleanup, and makes the closed attempt/artifact files read-only. A new candidate
is being prepared with only reserve 16% to 12%, retaining the measured +0.05 ns
hold target. This responds to observed routing overflow; actual rules, tracks,
footprint, clock and zero-overflow/fanout/timing acceptance remain unchanged.

## 23:17 UTC: reserve-adjusted candidate05 launched

The complete candidate04-to05 source diff changes only router reserve 16% to
12%, explicit profile/tag identities, linked metadata and refusal controls.
The hold target stays +0.05 ns, the eight ordinary stages and all source,
clock, PG, zero-overflow and fresh three-corner checks remain unchanged.
Root reproduces nine controls normally in 21.550 seconds and optimized in
22.137 seconds. Author and independent reviewer also close their controls;
Root independently rehashes all 1,466 inputs, exact 1,467 guard paths and
the three changed source owners. New Native output is empty before admission.

Actual plan is
`d90a19f738623a3d2017d9f6c239382ea78bd75a7b85009ad92f8533bc571686`;
preparation receipt is
`6cee62ee3be12a1b1645d29e2986589947fe04f25e11a4711a866a70b5bed9fa`;
independent review is
`2f0786f782b4a42569a742b1c9a540d7b883498f606002cfaf04f8d6e2a1e951`.
Root owns the sole heavy Native lease under the same 1,020-second outer,
960-second inner, four CPU/6 GiB/no-swap/offline limits. No result is inferred
from admission. The previously reviewed journal/tooling checkpoint is local
commit `3634053`; the two inherited dirty documents remain unchanged.

## 23:22 UTC: candidate05 completes repair, with six measured fanout failures

All eight ordinary prefix stages, actual raw readback and fresh three-corner
STA complete. The actual repaired ODB is
`0ee49c5d1de81b366fa4c832fc6db196f9793f287394c41d881b8d056d546bb3`.
Its 42,540-instance profile preserves the full original clock topology and
all 6,039 positive depth-four FF clock paths; the original 42,390-instance
pin/Boolean/rail contract passes. Logical PG inventory checks all 85,080
power terminals, while geometric PG connectivity and IR drop remain unproven.

Fresh nominal global-route STA reports zero setup, hold, slew and capacitance
violations at all three corners. Fast setup/hold slack is 9.81564/0.0155542 ns,
slow 2.21072/0.347706 ns, typical 8.41217/0.13984 ns. Each corner has exactly
six fanout failures, on net1705, net2095, net2108, net300, net3197 and net875;
maximum actual fanout is 20. Strict structure, fresh assessment and overall
acceptance remain false. This is unqualified nominal RC, not extracted signoff.

The HOST closeout also fails on a separate representation bug: Native JSON
serializes route-summary tuples as lists. Root directly compares all three
actual route logs and confirms identical keys, log hashes, call counts,
resource/demand/overflow values; only tuple/list types differ. No old source
or receipt is edited. A separately owned HOST reopening is being prepared to
run the unchanged full validator with only the exact JSON boundary normalized,
all subprocesses forbidden and full before/after hashes. It must retain every
real failure and the original exit statuses.

Original HOST receipt is
`75988d14520c298386850317943f5a4478f6b705dc0c36732a03024a94b36055`;
resource is
`ffd0b17314e3afdaae5729490f0c178b340d24a993d15d48e2c4b758c07224aa`.
Outer exit is one, Native exit is two, cleanup closes and all 1,466 inputs
remain unchanged after 240.666 seconds. The next proposed physical repair
targets the six measured fanout nets, preserving this repaired placement
rather than rerunning broad timing repair.

At 23:26 UTC the separately owned reopening actually closes in a HOST-only
process, exit zero. Root has read its complete source and all controls and
reproduced six normal/optimized groups in 0.248/0.244 seconds. Its unchanged
fixed full validator now closes the diagnostic after the sole exact route-row
tuple/list serialization adapter, with every subprocess/exec path forbidden.
All 1,466 inputs, 320 attempt artifacts and two resource artifacts stay bound
and unchanged. Six fanout failures and strict/fresh/overall false remain.
New reopening receipt is
`2ada096b5cd3b96f3ca6ca6746ffe45c21899a991b67e38ef1663f22c9d2c3a1`;
actual owned adapter source is
`5a2a960454c95d60b301c67b061cf5ccbc3e015622d7d76f4b2088b8a89a7a37`.
No old Native/HOST/resource outcome is rewritten or promoted.

## 23:40 UTC: eight measured branches, with every original placement retained

The passive-first plan moves 29 antenna A pins and six functional buffer A
pins through exactly eight new BUF8 cells. It touches only the six measured
overloaded nets; each repaired root has seven loads and branch outputs have
at most six. All 42,540 original masters and pins contract back exactly, and
all original clock topology and upstream A loads remain unchanged in the
HOST projection. Diode counts remain 238 and total delay-cell count is 89.
Moving a diode behind a buffer may remove protection from its original root;
fresh zero antenna violations remains mandatory, not assumed from the plan.

The new Native source locks every original instance and checks actual
`isFixed()`, places only the new cells, restores and independently compares
every original location, orientation, master and placement status. Both the
Native and HOST checks require exactly 42,548 final instances and the declared
eight new masters. The resolved config is byte-identical to candidate05.
Only ordinary GlobalRouting and CheckAntennas run before full raw readback,
complete source/clock/rail/placement contraction and fresh three-corner STA.
No broad hold repair or diode insertion is repeated.

Root reads the complete new planner, Native/Host controller and controls.
Review catches and corrects an O(n²) geometry capture, stale configuration
metadata, the old 198-versus-current-348 addition map, and insufficiently
explicit independent zero-movement checks before the packet is frozen.
The route-summary JSON boundary is now compared exactly after normalization.
Root reproduces six planner groups normally/optimized in 69.390/72.901 seconds
and six controller groups in 15.184/15.010 seconds, all passing. Source owners
and those test bytes remain unchanged through freeze.

Actual plan is
`27b6218e651d754a894e5a01dc33d0abc7feff0cddd8ba9d9e1ce5578664ca05`;
preparation is
`31b57ad2fbf8af815634a0db0ca98501082973efdd09923b8ac2f3d0f3129071`;
independent review is
`7788908d378edb2b888d6bc57aeacc0a3e7ef51f71e775fa58749299e2edf0a0`.
Root rehashes all 1,804 inputs and exact 1,805 unique guard paths, confirms
empty Native output and the unchanged config. Guard arguments use 323,972
bytes, safely within the observed 1,048,576-byte OS limit including environment
and pointers. Native runs under the same four CPU/6 GiB/no-swap/offline
resource guard. No acceptance is inferred from launch.

The child planner report's phrase about passing fresh timing is qualified:
candidate05 has zero setup/hold/slew/cap counts, but aggregate fresh timing
remains false because of six fanout violations. The actual admission code
requires those original false statuses and failed receipts unchanged.

Candidate06 actually stops at initial placement. The legalizer reports one
new failing instance, `streaming_tt_postgrt_passive_first_buf_03_00`, which
serves the net300 branch; its prior source/projection checks ran, but no new
routing, antenna or STA result exists. Resource receipt
`76014ef78f8455798276bd941ce6948ad94ea0076220d8a35ae8ac2bfc584a86`
closes failed in 33.457 seconds, exit one, complete cleanup and all 1,804
inputs unchanged. HOST receipt is
`c2be3609917429f9752f49f15af89d0b694b6a7921d890bb7db9e2b66387f81c`.
No partial placement is admitted as a completed target.

Read-only DEF/LEF analysis finds plausible row gaps for all eight buffers,
which remains a placement-model inference until Native legal checks pass.
A separate candidate07 is being prepared to widen only the new-cell Y search
from 150 to 500 microns; all originals remain locked and exactly unmoved.
The exact installed OpenROAD revision's [placement documentation](https://raw.githubusercontent.com/The-OpenROAD-Project/OpenROAD/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/dpl/README.md)
confirms separate X/Y integer displacement limits in microns. Rules, footprint,
configuration, graph and actual placement/timing acceptance are unchanged.

Snapshot05 preserves 23 reviewed source/test/protocol/proposal files,
1,294,229 source bytes. Root independently verifies every copy against its
actual original and SHA. Manifest is
`4d142a8e9c34e0aff30985fa4386aef1301a5eeb1db04bdf18c42713ce629728`.
It preserves the candidate05 format failure, separate reopening, targeted06
source and its eight-branch proposal with the timing-wording qualification.
Copies were not executed and do not claim physical, M or tapeout acceptance.

## 23:50 UTC: fixed-placement routing closes; antenna remains an explicit failure

Candidate07 changes only the new-cell legalizer Y search to 500 microns,
matching its profile/tag and exact Tcl/refusal controls. Root reads the narrow
diff, reproduces seven controls normally/optimized in 15.276/14.900 seconds,
and verifies all 1,804 inputs and exact 1,805 guard paths. Plan is
`a4fe3da504d22de04ab1dc6afc5f9398877de5185d4e44ae3f9c8156bee965e0`;
preparation is
`f8f5ed3222f931694a875a18f013287cae13d356d1107e3f4eeb336283dac849`;
independent review is
`4a4d45eac1792a3ada56ec3f37302c8def2053c1b70d593fd48da6d7c2eef48b`.

The actual partition completes in 42.476 seconds: legal placement, full pin/
source/clock contraction, exact restoration of all 42,540 original placements
and independent database round-trip pass. The largest new-cell displacement
is 269.5 microns. Fresh global routing reaches zero overflow, then CheckAntennas
reports 70 violating nets and 72 pins. These are not confined to the six edited
roots; the global reroute changes other routes, so moving diode loads alone
is not established as the cause. No final raw readback or fresh three-corner
timing is produced after this strict antenna rejection.

Resource receipt
`23006a96c19004e9952b4ae1d85c5c77d99b5083b76ad0a65b5766681b90ca88`
closes failed in 73.135 seconds, exit one, cleanup and unchanged inputs.
HOST is
`723d4511c0119f9c9c1c73b84d2891a3f1b38cf194da0051237deb8690ad7929`.
The completed GRT ODB exists as a rejected development target. The next
preparation tests a source-supported route-only jumper repair, preserving all
42,548 cells, pins, placements and the strict final antenna/fanout/timing gates.
The pinned installed antenna script must be read before admitting that action.

## 00:03 UTC October 19: jumper diagnostic preserves the remaining uncertainty

The source-only container intake closes with exit zero and complete owned
cleanup. It captures the exact installed antenna script, SHA-256
`ac89a9dafd46e5f8803d2ca9937a85f2ec8d19e6aa3617261413ae52f46663b1`.
The script supports `-jumper_only` and contains no explicit placement command.
Candidate08 will nevertheless independently compare all 42,548 actual cells,
connections, placements and statuses before and after native repair. Its sole
configuration delta is the explicit jumper-only flag; the unchanged source07
failure remains an input, not an accepted parent.

Review catches two evidence boundaries before execution. RepairAntennas is a
composite step, so the exact three nested state receipts and both actual
OpenROAD commands must be included. Its repair log prints no congestion table.
The pinned [FastRoute implementation](https://raw.githubusercontent.com/The-OpenROAD-Project/OpenROAD/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/grt/src/fastroute/src/FastRoute.cpp)
refreshes persisted congestion, but narrows intermediate usage to `uint8_t`.
An exhaustive saved-grid comparison therefore cannot independently establish
fresh global zero overflow without an additional no-truncation bound. Both
Root and independent review reject that broader implication.

The revised candidate retains a narrower persisted-grid measurement and
explicitly sets `global_zero_overflow_established=False`; strict structure
and overall acceptance remain false, with diagnostic exit two even if antenna
and timing counts become clean. It records the actual typed antenna count
and collects raw readback and complete fresh three-corner timing after an
antenna failure. This is diagnostic collection, not an antenna waiver.
All guide and via endpoints must stay within Metal1–4, with unchanged Metal1
pin-access scope and unchanged physical capacities. No Native08 result exists
at this journal entry.

A separately reviewed diagnostic continuation may later run the complete
ordinary detailed-routing/signoff tail from an authenticated failed parent.
That permission must preserve the parent failure and all final antenna,
electrical, proof, RC and manufacturing gates. No such continuation has yet
been admitted or launched.

## 00:10 UTC: actual jumper repair closes its diagnostic; all nominal timing/electrical counts are zero

Root admits the exact frozen08 plan
`25720323d71e41266d391ca11c541e72694bd8aee09b349c2f60fc9cd4286122`
after source review, nine controls normally/optimized in 31.621/30.846 seconds,
all 1,962 source/input hashes, exact 1,963 unique guard anchors, read-only
staging and argv limits. HOST preparation is
`79ed9f87ed563e8b059564ba45280dd0be87dab246a024da3aa57d7aeda4268d`;
independent review is
`03f46d4751a41d825d4a4da7eb9db4ec07ac7911952d8b041e4911eada726586`.

The actual source-readback, ordinary repair, raw export and three-corner STA
commands all exit zero. Repair inserts **48 jumpers for 38 nets**, reducing
antenna violations from 70 to **32 nets** without adding diodes or changing
any of the 42,548 cells, pins, placements or statuses. Source/clock contraction,
logical PG, independent database round-trip and legal placement checks pass.
All 335,842 guides and via endpoints stay within Metal1–4; Metal1 pin access
is unchanged. Saved-grid capacities are unchanged and its measurement passes;
fresh full global zero overflow remains explicitly **unproven**.

Fresh propagated-clock global-route nominal estimates have zero setup, hold,
slew, capacitance **and fanout** violations at all three corners:

| Corner | Setup slack ns | Hold slack ns |
| --- | ---: | ---: |
| Fast | 9.73128 | 0.0117854 |
| Slow | 2.1238 | 0.318759 |
| Typical | 8.44321 | 0.145805 |

The six earlier fanout failures are closed at this actual target. The
32 antenna failures and unproven fresh-global-zero keep strict structure,
fresh timing and overall acceptance false. Native/HOST exit two and resource
status failed are retained; diagnostic integrity passes, not physical
acceptance. Actual ODB SHA-256 is
`845b8cda41dba6eeeb0e63639e6c3c9bd942c6c1454cd23b639b715fa3c2dc3b`.
HOST receipt is
`ed3c4e5795184d55256b3746038d52546732b6af91e98fdff98cda8727dc40dd`;
resource receipt is
`ce2367d37d6addfa3353bfc4f480b54e537150e6e2bf06b9c3a8a1f7b50a9da4`.
The outer guard returns one, records its child exit two and closes in
167.849 seconds with complete owned cleanup, no errors and unchanged inputs.

Snapshot06, local commit `e8b4eec`, preserves 17 source/data files totaling
318,404 bytes. Manifest is
`f969ed02b267eac46bab007324411363b87f3bd446ec9d376b65cf61a6a9cd52`.
It was created before Native08 results and makes no outcome claim. Root
verified every archival copy against its original bytes and SHA.

A proposed diagnostic full ordinary final-tail admission requires all these
actual source and timing checks, authentic failed typed-two receipts and
complete artifact/resource closure. It preserves both remaining physical gaps
and all final checks. Independent review catches a late-use artifact race in
the first sealed HOST draft; a separately named revision repeats the original
membership/hash/terminal identity checks after semantic use and snapshot
closure. No final-tail Native run has been launched at this entry.

## 00:15 UTC: diagnostic final-tail authority is bound and source replay preparation is running

The bound revision02 admission source is
`681cc66b74e240e3f43c8204a4262356baddae06450d65ee6323c13c52b7326b`;
controls are
`e80870deceea3fb6b715379b01772042861c46974416bfeb44068a86e19af186`.
Root reads the complete source/delta and mutation controls, reruns seven
normal/optimized controls in 0.022/0.027 seconds and independently verifies
all 244 exact closed08 output members against manifest
`ece05650283eb10d8f104ed5b918e7665069146b8ed8a8d829155b4460c84294`.
Only three terminal/output SHA constants change from the reviewed unbound
revision. Full actual fixed HOST validation closes in 41.279 seconds with
every subprocess launch blocked; observation is
`15a39a32c12346b24f7a9ea277f04f96417e466aed5809ece1926dc59481b278`.
Independent final review is
`3f429a964ba16f5103da1efc57724b3423f78585e23211b1782048f8ef8ff12c`.

The admission requires exact original source/clock/placement contracts, the
clean complete nominal STA/electrical assessment and authentic failed typed-two
receipts, while retaining antenna32 and unproven global zero overflow. Its
`passed=True` means permission for diagnostic full-tail measurement only.
The previous unexecuted interim admission is preserved; the new file is
installed byte-identically in the actual owned Final producer. Fixed final.py,
entry.py, dispatch.py and replay authority remain unchanged. Root repeats the
seven existing Final controls normally/optimized in 0.062/0.058 seconds.

HOST-only dispatch preparation starts at 00:13:00 for the exact final tag and
900-second Native budget. It is still revalidating source replay at this entry;
no Native final flow has launched. Root still must review the frozen final
packet and exact guard before GO, within the 00:26:07 candidate cutoff.
Read-only analysis of actual08 antenna.rpt finds exactly 32 violated rows on
32 unique nets, all Metal3 cumulative-area ratios above 200. A layer-ceiling
explanation is consistent with this result but remains an inference.

Snapshot07 preserves twelve reviewed source/data/protocol files, 140,301 bytes,
including the original held draft, late-use fix, exact installation record and
prior interim authority. Manifest is
`b950b7b2bd96e930d6a0184035bdc134aa1518774982a3a5c550b0b96a6f517b`.
Every copy is independently byte/SHA verified; no relocated archive code was
executed and no final-flow/M/signoff acceptance is claimed.

## 00:23 UTC: final guarded continuation admitted before candidate cutoff

HOST dispatch preparation closes at 00:18:24. Metadata is
`3e4dd1e7e9bd4aae00c72d31e62dfae679bde50de32e4828dde9cbb9f393a368`;
guard plan is
`2f1e7e4d83b3636fbca2fa92cb1d995638518bc182f2e49178141db8624d33de`.
Preparation seal is
`4a2c878678bc312c1eadca0c1ff287c0616e69f43243037ec3bdacea444c9237`;
independent packet review is
`fd3dec15fcd42b98f7c7e00c1bb6264b1c7de3a09d0c3667819c9396008c7a21`.

Root independently verifies all 92 exact read-only staged inputs, 54 actual
and staged canonical producers against committed `4732bb2`, four exact owned
executables and 2,117 external anchors. The full 395-positive/same-two-private
source replay authority and its 29,290 consumed files are preserved. Guard
binds 2,231 direct inputs plus its own plan, exactly 2,232 unique paths;
395,968 argv bytes plus environment/pointers fit the 1,048,576-byte limit.
Metadata and guard are frozen read-only, with no prior flow/report or active
lock. Root launches the exact reviewed guard at 00:19:35.

The fixed controller completes initial verification and enters pre-Native
source replay at 00:20:41. At this entry the replay is still active, within
resource bounds; no actual detailed-routing result exists yet. The guard
permits 1,620 seconds total and 900 seconds for the Native flow, four CPU,
6 GiB with no swap, offline execution, read-only source/PDK mounts and only
the owned flow host-output mount writable. Full pre/post source validation,
all 34 ordinary tail stages and final checks remain unchanged. The failed08
parent and both physical gaps remain explicit in frozen permission metadata.

Further proof preparation is conditional on an authenticated terminal result
and a completed DetailedRouting state. An earlier or partial routing ODB is
not an M target. All subsequent derived observations/exports/proofs must stay
outside the immutable final-output root. Positive M alone is insufficient:
the separate actual-M private pair and whole import/source/runtime closeout
remain mandatory, with time reserved before the 03:26:07 hard stop.


## 00:43 UTC: Final01 times out before a completed detailed route

Actual CAD began at 00:23:43 UTC, before the candidate cutoff. The complete
first routing pass reported 41,449 violations; repair iterations had begun
when the 900-second Native allowance expired. These are intermediate router
counts, not terminal DRC. No completed state survives; states=[] and there
is no eligible final-M target. No earlier or partial ODB is substituted.

The physical report is `timed_out`, typed exit 124, Docker after-cleanup exit
137 and actual native-entry exit unavailable. Its SHA-256 is
`4861310538889c6b02db00a8a9b81be9adc18a13dea1eb53de0ebb594e9de170`.
The full source replay before and after has identical digest
`1f7f7b6fcbe8839f6291ed89f93507fccfd81e310b2af479106652a30bbb1138`.
The outer guard closes at 00:42:28 UTC after 1,367.230 seconds, typed 124,
all 2,232 guarded inputs unchanged, cleanup confirmed, no cleanup errors and
no remaining owned process or container. Resource report SHA-256 is
`f55d975f26b901330c2b647e3b219e39a077ce32cedc49ae62f12596cb718438`.
The Native lease is released only after that closure.

Root authorizes HOST preparation of separately owned Final02/A02/handoff03
for the exact same frozen 845b candidate, config, SDC, PDK, routing recipe,
layers/rules and all 34 ordinary tail stages. Native entry source f153 stays
byte-identical. The only changes permitted are owned paths/tags, provenance
and the 3,600-second Native / 4,320-second outer allowance. This validates an
existing hash-bound candidate under approved plan lines 56–59; no new
implementation experiment is admitted after 00:26:07. Original Final01 and
all its sources and receipts remain immutable. The new parent is UNBOUND
until authenticated by the original Final01 authority. Independent and Root
review remain required before Native GO. The 03:26:07 hard stop and actual
final-M/private-audit obligations are unchanged; deadline fit is uncertain.


## 00:49 UTC: same-candidate validation source review and archival checkpoint

Final02 source is frozen at 80f98d2a35cfad9e13990802287c33a1046abab48d29a585cd7b814ab6988962;
Native entry remains byte-identical f153. Root and independent review accept
only the owner/provenance/budget changes. Ten Root HOST controls pass normally
in 0.877 seconds and optimized in 0.860 seconds; all original terminal 124,
cleanup, candidate/source/config/SDC/PDK equality, full-tail order and late
parent-byte/membership refusal checks remain. A02 is
2f9cea85a303f03c9e511b1c1ae661a0097665c8fa769477f319ff34dd86246b;
handoff03 is 220dac90546b8095932348050051e0905cb3d9aca09fe6e7afe28317e6f51eee.
Root's existing admission 14 plus owner 3 controls and handoff 7 plus variant 3
controls pass. Independent and author normal/optimized controls also pass.
These are HOST/controller checks, not actual final-netlist proof acceptance.

Authorized HOST preparation starts 00:48:39, session 81131. It authenticates
original terminal Final01 using unchanged fc1, then validates actual08 and
generates a fresh A02-owned full-replay snapshot. The earlier A01 snapshot
cannot satisfy the new owner check. No Native Final02 flow has launched.

Snapshot08 preserves nineteen source/control/terminal-receipt files,
888,763 bytes, with every original and copy independently rehashed. Its
manifest SHA-256 is
9312daf0ce1059eac98112fe69b16aa50a47e4c306f1490d8f1fc4323533e8f9.
The archive is not executed or standalone; it preserves the actual failed
Final01 and HOST-only Final02 preparation scope without acceptance claims.


## 00:58 UTC: exact same-candidate Final02 validation admitted

HOST preparation closes exit zero at 00:56:42 after approximately 483 seconds.
It authenticates terminal Final01 through the unchanged fc1 authority and
freezes 2,247 parent inputs/artifacts with exact membership. A fresh complete
A02 replay closes with the correct executed-admission owner. Metadata is
`1b6f464bb4a9802061b6ba0fec47593ecb2df00826a789ea34b2f2fcf6454714`;
guard is `b1f7fc5bd064652cd4faeafc70c570a6f4ac8cdf8e0bec8d82af6ee9089b9a08`.
Author seal is `fdfba6a691a9c20aff8404b396efa8182947cc8d28acf7044b0e98f2f0581c5b`;
independent packet review is
`aaad34609e5ce5a407acd6c7bd77483a563a8c4e2f84ef499f6ef7851a2bc31a`.

Root independently verifies all 92 exact read-only staged inputs, 54 unchanged
canonical sources, four fixed owned sources, 2,250 external inputs and every
frozen terminal-parent byte. Exact candidate/config/SDC/entry/rules/order and
source/PDK metadata equality hold. Guard has 2,345 direct anchors plus itself,
exactly 2,346 unique input arguments. Its 412,967 argv bytes and 456,792 bytes
including environment/pointers fit the 1,048,576-byte limit. The worker,
existing-parent cad-validation kind, original typed-124 parent, 3,600/4,320
budgets, 6 GiB limit and 03:26:07 hard deadline match the reviewed source.
Metadata/guard modes are 0444 and no prior Native output or resource job exists.

Root launches the exact frozen guard at approximately 00:58:13, session 75084,
as the sole heavy job. At this entry only preflight/source validation is
running; actual Native CAD has not yet been observed. No candidate variant,
partial-ODB substitution or acceptance waiver is introduced. Actual final-M
selection still requires authenticated closure plus completed DetailedRouting.

A separate pure HOST classification of the original08 antenna report confirms
32 unique nets and 32 Metal3 cumulative-area violations against ratio 200.
Printed ratios range 200.03–466.22, median 224.715. Analysis SHA is
`dc90c9b20e300e2cb2c9141decefd98fbb678e04794e7ed0d265d3e326f95036`;
independent transcription check is
`c2a18d4692b8dec5ff77a5cfe2040aac1f9697e6c29b86fd10f61d5f1f67afe3`.
Printed precision is limited; no causal repair proof or final-route result is
inferred, and no new physical experiment is admitted.


## 01:10 UTC: actual Final02 CAD and conditional validation handoffs

The new A02-owned complete pre-Native source replay closes at
`74b7fcface5707cebcd0eb805bb26a65eb630ae318ad771c51f98beb9978ecb9`.
Actual CAD starts at 01:01:53 UTC. Pin access and track assignment complete;
at this checkpoint the first detailed-routing optimization pass is active.
No completed routing state or final-M target exists yet. The one-hour Native
limit and unchanged full-tail/guard/deadline remain in force.

Optional Final02 timeout export and prerequisite sources are separately frozen
at d3700aa0 and 8cdb948b, with only A02/handoff03 path and hash rebindings.
All execution/validation function ASTs and inherited test bytes match their
original owners. Root reviews the complete diffs and new ownership controls;
seven exporter controls (one mode skip), six prerequisite controls and two
owner controls pass. Independent normal/optimized tests pass. Actual use
requires terminal typed 124 plus completed DRT and a separately admitted
canonical Native export; no partial routing data qualifies. Owned selection
closeout, pure prerequisite receipt and source pins must enter M AND wire
outer guards/reports if used. Neither H03 nor the wire adapter consumes that
separate prerequisite implicitly.

The first optional public-wire adapter is held, never executed: independent
actual shortname-import reproduction finds that a cached workspace module can
shadow a fresh selected module at context entry. Finding is
`a7860336ac4c8e78c1d24094c1037cad95b85a10a1a3b99799a588db94e99ab5`.
A separately owned revision02 removes the saved project module names at entry,
preserves exact exit cleanup/restoration and changes no canonical main,
actual-export body, full 6,039-state sampler or fourteen-command worker.
Root reads the full initial adapter and corrected diff; nine controls pass
normally/optimized in 0.103/0.100 seconds. Independent nine-plus-nine controls
and a separate actual import-owner probe also pass. Source is
`cce85b85abf26e5fde4bb628c8674f9b8a76cc4bb07d88c383d3ca52071cab31`;
independent review is
`569973b33107b3eabeef4ec8a1e95838cebba17a3ae04859ee1df4dac05be154`.
These are conditional HOST readiness checks only. Actual completed route,
export, regenerated semantic mapping, Root lease and enough time after M
remain required. No Native public-wire execution is authorized at this entry.

Snapshot09 preserves 57 source/preparation/review/control/transcription files,
253,628 bytes, with every original and copy rehashed. Its manifest is
`e3f78848342c828fa4c2bb87c219006280858e6f1208992192639dad56df89a7`.
Both held first draft and corrected revision are retained, with their actual
review scopes. Archived copies are not executed or standalone; actual Native
outcomes and complete runtime/PDK/source closure remain outside this archive.


## 01:20 UTC: first complete Final02 repair iteration reduces router count

The first routing pass finishes with the same 41,449 reported violations as
Final01, in 8 minutes 23 seconds. First repair iteration then closes with
29,969, a reduction of 11,480 (about 28%), after 7 minutes 2 seconds. Its
reported wire length is 2,271,608 microns and via count 298,328; peak memory
is 2,132.77 MB. Most remaining reports are Metal2 shorts (19,687), Metal2
spacing (6,684) and Metal3 shorts (3,189). These remain intermediate router
counts, not terminal DRC or signoff. Second repair iteration has begun.
No completed routing state or eligible actual-M target exists yet.

The resource supervisor's 01:17 observation shows 69% host memory available,
21,559,394,304 bytes free disk, approximately 360,752 KiB owned HOST RSS and
35.55% of the 6 GiB container cap, with no swap expansion. No resource alarm
is observed. The exact one-hour Native allowance and original hard deadline
remain unchanged.

Independent report audit rehashes all fifteen listed closed/frozen receipts
and checks foundation/raw/optimized/N counts and A02/H03 identities. It finds
two wording issues, both corrected: global-route overflow response cannot
establish detailed routability, and Final02's actual parent binding is now
completed rather than future work. Audit receipt is
`0bad28d165301cf4751fdf3742e0c2f41a5b2757017b272dabb26aaf00ab37e5`.
It binds the report at that audit time, not future edits or final outcomes.


## 01:37 UTC: routing reductions and corrected concrete M handoff protocol

Full reported iteration counts are 41,449 (initial route), 29,969, 30,815,
8,535 and 5,992. Iteration five is active. The initial reduction is not
monotonic, but later iterations make substantial progress. These remain
intermediate router counts; there is no completed DRT state or eligible M
target yet. The unchanged one-hour Native/4,320-second outer bounds apply.

A data-only H03/A02/Final02 handoff protocol binds 21 fixed sources and nine
tools, with actual target/count/commands pending. Root catches a concrete
first-plan invocation error before any use: the canonical ordinary exporter
imports sibling scripts at module entry, so `python -I` fails before its
parser even on `--help`. A new, separately frozen plan02 uses the canonical
supported `python -B` invocation without `-I`, after checking the clean
inherited environment and complete source closure. Timeout02/helper/proof
entrypoints already establish their fixed script paths and retain `-I`.
Nine actual CLI help calls and nine process-blocked import/help checks pass;
Root additionally reproduces both the old failure and corrected help success.
No canonical or Native implementation body is changed; original plan01 remains
preserved. The new plan is
`d35a8c8dbdac8c39de6aad3e6d12068e0f110860dcb46b9f17f118b7077613c9`.

The protocol requires actual closed Final02 and completed DRT/latest ODB;
canonical 1 CPU/2 GiB/offline/120-second export (or exact reviewed timeout02
branch and its separate prerequisite); full regenerated 6,039-state mapping;
GEN04 complete actual M, executor01 with no stop-at, and the separate private03
pair plus whole audit. Direct guard anchors bind actual manifests and full
internal validators recheck all deep memberships; 29,290 paths are not blindly
expanded into argv. Positive M stops no later than 02:46, preserving forty
minutes for actual private/audits/report before 03:26:07. Proposed export outer
600 seconds/3 GiB is not a Native lease and still needs Root's measured actual
command/budget review. Nothing in the data plan authorizes a pending command.

Snapshot10 preserves 28 data/procedure/CLI-check/audit artifacts, 140,495 bytes,
with original/copy hashes verified. Manifest is
`a3bf4fa4dbaf732e665fe4291718c0c88ba87295ff04f52d0fcf047fb417d45d`.
No archive copy is executed or standalone; the independent report audit binds
its old recorded report SHA/time rather than later edits or live outcomes.

## 02:06 UTC: final routing timeout and exact open prerequisites

Final02 continues to reduce routing violations through complete iterations
41,449 → 29,969 → 30,815 → 8,535 → 5,992 → 5,282 → 4,910 → 4,698 → 4,367 →
4,124. The last completed iteration has 3,195 shorts and 929 spacing errors;
the following iteration reaches provisional 3,777 at 90%. The one-hour Native
allowance expires without any completed `state_out.json` or final routed ODB.
None of these intermediate counts is terminal DRC, and no inference of
unroutability or guaranteed convergence is made.

Actual Native result remains timed_out/124; owned Docker cleanup exits 137.
The physical report is `c589f650ee276e967ae8835571f67a83eca8c46320438fa8620e29c608de5902`.
The resource receipt closes failed/124 at 02:05:42 UTC, in 4,044.868 seconds,
with all 2,346 guarded inputs unchanged, cleanup confirmed, no remaining owned
process/container and no cleanup errors. Resource receipt SHA-256 is
`e9ae8fcf06b4e96023a78f04bf7baab96f931166b9580dc425c6749b63d5b2bd`.
Full pre/post source replay hashes are both
`74b7fcface5707cebcd0eb805bb26a65eb630ae318ad771c51f98beb9978ecb9`.
The 107-artifact final map and empty completed-state list remain immutable.
No export, actual M preparation/execution, private-M pair or final public-wire
run is admitted from this incomplete target. The hard deadline is unchanged;
Root closes out existing evidence instead of admitting another experiment
after the candidate cutoff.

The independent RC provenance audit is
`build/streaming-tt-recovery/renewal-RC-provenance-audit-01/report.json`,
SHA-256 `25e130546cf2c0114a9f72a344c8742d6737ca3ad7d8a739b65728aa632f69a4`.
Root reads the gap matrix and independently rehashes all 44 reviewed objects.
Final02 selects only nominal RC through the CMOS5L alias to a seven-layer
SG13G2 deck, whereas the actual CMOS5L LEF has five routing metals. Three cell
PVT corners sharing nominal RC do not establish a qualified RC-corner envelope.
All 21 retained upstream intake objects are verified: three merged official
ITFs and 18 draft/common/rule objects, not 21 merged files. Basic stack data
is available; a justified five-layer extraction deck, consumer coverage,
numerical/reference R/C/via calibration and actual SPEF/STA remain open.

The private build and scoped five-sphere runtime controls passed. Both actual
uniform-wire attempts exit zero and report terminal Frobenius changes below
1%, but early diagonal-dominance warnings fail the unchanged strict protocol.
This refusal is neither proof of nonconvergence nor of wrong process data.
Layered and held-out wire calibration were not reached. No solver/model retry
is admitted. Older no-build/no-pilot setup statements remain historical and
are explicitly superseded in the current outcome report, without modifying
the original receipts or the two inherited dirty documents.

No immediate user input, installation or new basic process document is needed
to describe or pursue these engineering gaps in a future authorized window.
Qualified process-specific extraction decks/reference data would help if the
user already has them. Full TT/tapeout acceptance remains open.

## 02:18 UTC: independent terminal refusal, report audit and owned cleanup

The outcome wording audit is
`build/streaming-tt-recovery/renewal-outcome-report-independent-audit-01/report.json`,
SHA-256 `4fbe496613a2f2839485699803131648d3880d67bfe4933a9ae7b8698761dbbb`.
It binds outcome report `7807074e2d89347d8aba69366e3ff004b46dac821a6ffd20d9a5de4302e55021`
and journal `d4333ce53e666793c298a75327fcd79597141bb2a9d82c70228dca7a5b9dc70a`
at review time, not these later journal additions. All 2,346 guarded inputs,
107 closed artifacts, 15 evidence-table references and A02/H03/protocol pins
match. Root corrects one stale running-status table label before final review;
no unsupported closure finding remains. The outcome report stays byte-identical
after that audit.

The first independent terminal-audit driver observes a successful return from
the original fixed Final02 authority and the actual A02 refusal, but expects
a later DRT-specific refusal message rather than the earlier empty-state
message. Its own assertion exits one before persisting the captured return.
This audit-driver recording failure is preserved as
`renewal-final02-terminal-independent-audit-01/initial-audit-expectation-failure.json`,
SHA-256 `43cf2106ffbf7ff9a5a5946dd80a046437fcbabda4cbb938ba4397001489330c`.
The actual submitted inline stdin is recovered from its tool transcript and
retained as archival-only text; no executed Python-file owner is invented.
No physical authority source or original result changes.

A separately named audit02 corrects only recording and expected-refusal
handling. Three normal and three optimized cheap recording controls pass.
Root reads its complete driver before the one bounded HOST reopen. The
unchanged A02 calls the unchanged fixed Final02 authority exactly once;
`sys.setprofile` observes and durably saves its successful return before the
selector refuses `ValueError: Missing closed final artifacts/states`.
Selector outcome and full final membership are saved before assertions.
Popen and os.system are blocked; no Native, proof or source regeneration runs.
All 108 Final02 files (107 artifacts plus report) and both resource files have
identical membership, hashes and modes before/after. This authenticates the
closed failed producer; **M_eligible and M_target_selected remain false**.

Audit02 report is
`build/streaming-tt-recovery/renewal-final02-terminal-independent-audit-02/report.json`,
SHA-256 `45891227d95afc59f769a7561b80bedce16a22217959a11e6bb05b00ebe5e1ba`.
The exact original authority return has SHA-256
`d51ab8a5a1459523cd8e87c38bcf5b0703fd98112558b75c40d9399a5a4798b2`.
The 480-second/6-GiB HOST guard closes completed/zero in 121.622 seconds,
with unchanged inputs, cleanup confirmed and no remaining owned processes;
resource SHA-256 is
`68523b1b1a246a05d750a40cd704b90b21b2968252a7b756cc762224f3580b68`.
No partial route is promoted, and no final M/private/public-wire gate executes.

Root verifies the exact owned `caffeinate -i -t 43105` process, PID 88556,
then stops it. Cleanup receipt is
`build/streaming-tt-recovery/renewal-owned-cleanup-01/report.json`, SHA-256
`46af86b433c9a720d6dc4dfe83c5dad02469e0009de5c0763b0d2a602a956785`.
The actual last Native owner has no container and the Native active lock is
absent. The two inherited dirty documents retain their original byte hashes.
This renewal ends as a partial result with full acceptance unmet, before the
maximum deadline. No push, PR, publication, external message, shared-PDK edit
or fabrication submission occurs.

The auditor's final independent postcheck rehashes all fourteen HOST guard
inputs and confirms the original 108 Final02/two resource files still match
complete before/after/current path, byte, hash and mode inventories. It also
observes both relevant worker PIDs and the exact Final02 container absent.
Postcheck SHA-256 is
`c87b8d18bdf2a4c1555e18400b05424bc4bb6cc129131b96b21a86a46dac340b`;
the file-index SHA-256 is
`77f985bd996a3b4e659c3e4e5c16fb223e14176a3a5c906acc237c0b43d131d2`.

Snapshot11 preserves 37 selected closed records and reviewed controller/recording
sources, 2,332,110 bytes, with byte-identical copies and original hashes checked
before/after copy. Its manifest is
`97e7b6cb8eea35102b8c82f6b73c19164f03f173ae61c754daf147df0c20d479`.
The final postcheck and file index finish after that immutable selected snapshot;
snapshot12 separately preserves those two additional records, 9,460 bytes,
manifest `71faf62adce6d0a1e97d0fe2536f46313d2c5738f284c0f35a93059ef8135e3e`.
Neither archive is executed or standalone. Full frozen metadata, replay trees,
proof objects and PDK/runtime installations remain at original bound paths.
Archival copies do not convert the failed physical attempt into acceptance.

### Archive bookkeeping correction

The preceding claim that the postcheck and file index arrived after snapshot11
is incorrect. Root's enumeration had already included both among its 37 selected
files when the agent's final message arrived. Snapshot12 duplicates those two
records; it adds no unique validation evidence. Its copied bytes, original
paths and manifest hash remain correct. Root corrects only the explanatory
README and this journal; both manifests, all copied source/receipt bytes and
the independently audited outcome report remain unchanged. No proof or
physical result changes.
