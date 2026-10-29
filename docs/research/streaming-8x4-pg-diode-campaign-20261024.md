# PG-aware diode placement campaign, 2026-10-24

This is a new physical intervention and its HOST preparation, not a closure
result. The previous 8×4 campaign never completed the whole DetailedRouting
step. Its diagnostic replay associated all 36 observed signal/PG shorts with
new diode A-pin projections; that evidence motivates this intervention but
does not prove that placement is the only remaining routing problem.

The approved campaign began at 2026-10-24 14:38:15 UTC. Primary routing is
budgeted through 20:38:15 UTC. There are at most two physical variants in the
entire campaign; the second can instead be a timing ECO. No automatic second
variant or additional repair is authorized by this helper.

## Mechanism and scope

`scripts/streaming_8x4_pg_diode.py` leaves canonical antenna detection,
insertion, connectivity and antenna counts in control. Its Tcl bridge wraps
the public `repair_antennas` command, delegates the original arguments and
return value, detects newly named diode instances, and then applies a finite
placement search. It also exposes `pg_diode_apply_existing` for the known
39-device postdiode seed. There is no 39-device ceiling: every newly inserted
canonical diode must be protected, or the call fails.

Both canonical insertion paths are reachable through the wrapper: LibreLane
`antenna_repair.tcl` calls the public command, and every in-DRT antenna-loop
call in `drt.tcl` calls the same public command. The new flow controller must
inject the prelude after each process's `read_current_odb`; editing only the
initial/GRT path would leave late insertion unprotected. Package source files
remain unchanged; declared staged overlays and their hashes belong to the
new flow's authority.

Policy A searches the original row, at most 16 sites in either x direction.
The original unexecuted B proposal searched at most 50 sites and one adjacent
row in either direction; its exact source remains in Git `0285207` and the
frozen A preparation. After A's actual failure, Root authorized one explicit
revision of the still-unspent fallback: B searches every legal official-core
row/site, selecting the nearest admissible vacant site by Manhattan distance
from the original bbox lower left. Ties prefer smaller row displacement,
lower row y, then lower site x. One lazy x generator per row feeds a best-first
heap; the full 665,508 candidate positions are never sorted/materialized.
The request binds the complete movement-policy definition. A's candidate order
and geometry predicate remain unchanged. Root must separately admit B as the
second and last variant; there is no additional fallback after it. All targets
are planned together with mutual occupancy. No site, timeout or failure
permits changing the footprint, moving other cells or waiving an access rule.

The geometry certificate uses the complete pinned CMOS5L technology LEF
(SHA256 `3edd5a1ad31e8307be537d0d1b85c3258fefeb21aac04aaa476e4f72de4cffd5`)
and the actual antenna cell LEF. It transforms all three A-pin rectangles for
R0/MX/MY/R180 about the placed bounding-box origin. Every rectangle clears M2
PG by the complete width/PRL-table maximum (600 DBU) plus the default-via M2
extent. A concrete Via1_YY landing on actual M1/M2 track grids must overlap A,
fit its M1 enclosure inside the diode body, clear M1/M2 PG, and admit a two-M2-
pitch vertical M2 escape. PG-via bounding boxes conservatively obstruct both
layers. This is one access witness and a conservative PG envelope; signal
pin access, full routing, antenna signoff and physical DRC remain mandatory.

Only the live OpenROAD Tcl process changes the database. The Python helper
reads TSV/DEF/LEF and emits moves; it never loads or writes an ODB. Its entire
process lifetime has a fixed 60-second alarm, and its search loop also checks
a deadline. The parent runner separately bounds the complete Native job.

Before/after snapshots bind unique live block instance names, masters,
placement boxes/orientations/status, every terminal/net/port endpoint, public
pin geometry, PG shapes and hard/soft blockages. Canonical repair may not
remove an existing instance or change its master. The hook may change only
the target diode locations/orientations; it must preserve their signal net,
all other instances, connectivity, official PG and public geometry exactly.
Only movable PLACED diode targets are admitted. The bootstrap's subsequent
canonical `write_views` may assign previously null PG ITerms; that distinct
flow action needs its own before/after receipt and is not hidden in this
hook's invariant.

## Pinned API audit

All source references below are at OpenROAD commit
`dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`.

* [db.h](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/odb/include/odb/db.h#L192)
  directly declares box coordinates/isVia (198–218), net getSWires (2041),
  dbInst orientation/location/bbox/status (2794–2862), dbSWire getWires (3824),
  and dbBlockage getBBox/isSoft (4106/4132). `setLocation` is explicitly the
  placed lower-left bbox coordinate, after `setOrient`.
* [common/odb.i](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/odb/src/swig/common/odb.i)
  directly includes db.h and the Tcl container typemaps. It does not include
  dbObject.h; [swig_lib.cmake](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/cmake/swig_lib.cmake)
  does not enable recursive include-all. The provisional inherited getId call
  was therefore removed before Native admission. Unique dbInst names and
  exact full membership/master checks are the declared identity boundary.
* [GlobalRouter.i:155–163](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/grt/src/GlobalRouter.i#L155)
  exposes `grt::start_incremental` and `grt::end_incremental`; the Tcl latter
  explicitly calls `endIncremental(true)` to save guides.
  [GlobalRouter.cpp:320–340](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/grt/src/GlobalRouter.cpp#L320)
  installs movement callbacks, updates dirty routes and finishes with that
  guide-save policy. The hook brackets only its live placement changes and
  retains the canonical caller's layer/route options.
* [Opendp.tcl:123–143](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/dpl/src/Opendp.tcl#L123)
  supports `check_placement -verbose -report_file_name`. The command returns
  no success boolean; [CheckPlacement.cpp:130–136](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/dpl/src/CheckPlacement.cpp#L130)
  throws DPL33 on placement violations. The hook preserves that failure.

These source checks do not substitute for observing the pinned image's
actual command execution. An absent method, malformed snapshot, failed
placement check or incremental-routing error must stop the cheap probe and
preserve its logs and intermediate ODB/DEF/guide files.

## Cheap-first admission and remaining gates

The first Root-owned cheap probe must use the exact historical postdiode seed,
official 8×4 geometry, unchanged SDC/20 ns clock, pinned PDK/runtime and new
policy-A request. It must retain complete pre/post snapshots, all planned
moves and access witnesses, live applied views, a successful actual placement
check, incremental route refresh, graph/PG/public conservation and canonical
PG assignment readback. A canonical insertion smoke must also exercise the
public wrapper from the clean pre-insertion seed and retain its actual
antenna counts; the historical 35-net/36-pin→39-device replay is a
reproduction expectation, not permission to discard newly required diodes.

Only after cheap admission should the new candidate run the complete ordinary
DetailedRouting/antenna loop with original routing iterations, rules and
resource limits. New post-insertion calls must each close their hook receipt.
No prefix, bounded diagnostic route or internal clean iteration is a final
target. Whole DRT completion, final diode/PG/connectivity conservation, no
route DRC/antenna/disconnection violations, qualified CMOS5L extraction and
timing, final-target digital correspondence, applicable official prechecks,
DRC/LVS and artifact custody remain separate acceptance gates.

At 2026-10-24 15:12 UTC the eleven initial portable HOST controls passed under
normal and optimized Python. They covered the measured ANTENNA_115 failure geometry,
all four orientations, full-PG clearance, finite/no-site failure, conservation,
more-than-39 new devices, exact row/LEF excerpts and complete live snapshot
endpoint accounting. That initial checkpoint claimed no Native result. The compact fixtures
are exact HOST excerpts with full-source hashes; Native admission still
requires the complete pinned technology LEF and actual cell file.

## Actual A failure and revised-B HOST proposal

Root's first cheap Native A probe closed with exit1 in 14.753 seconds. The
canonical replay reproduced 35 affected nets, 36 affected pins and 39 inserted
diodes. Live snapshots contain 42,138→42,177 instances, 8,860 PG shapes and
zero placement blockages; the planner failed at ANTENNA_132 before any move or
detailed route. Root's independent terminal readback reopened all 552 input
seals and the failed inner/outer receipts with confirmed cleanup. This is a
placement-policy failure, not a completed physical candidate.

`build/campaigns/8x4-20261024-01/pg-A-feasibility-HOST-01/report.json`
retains all 39 ordered targets and all 33 policy-A slots per target. Its
necessary-only model ignores M1/PG-via obstructions. For ANTENNA_132, even
ignoring every other diode target, all 19 M2-access-witness sites overlap
preexisting cells; earlier greedy choices cannot free them. Whole greedy
trajectory failures in general are not monotone under added obstructions,
because earlier choices can change; this stronger per-slot independent result
is deliberately distinguished. A portable exact-geometry control preserves
the ANTENNA_132 failure under unchanged A.

`build/campaigns/8x4-20261024-01/pg-B-global-feasibility-HOST-01/report.json`
binds the actual closed A snapshots/receipts, all 552 frozen input seals, full
PDK LEFs, old and new helper sources, complete 39-device certificates and a
simulated unchanged-instance/graph/PG check. It also reruns the superseded
unexecuted B50 source: that trajectory fails at ANTENNA_113 after five targets.
The revised global B plans all 39 under the complete actual 8,860-shape PG
census: 26 devices move, 19 change row, maximum absolute x displacement is
25.920 µm, maximum y displacement 22.680 µm, and maximum Manhattan displacement
37.260 µm. Planning took 1.131 seconds; the whole HOST packet including source,
capture and receipt rechecks took 4.140 seconds, below the unchanged 60-second
helper bound. Every access certificate was recomputed after the simulation.

Fourteen portable controls now pass under normal and optimized Python. The
new controls check complete/unique best-first order against a small explicit
finite universe, nearest-site selection, movement-definition binding and the
actual A failure geometry. This is a reviewable HOST proposal only: no B
variant has been selected/registered by this helper, no ODB was changed, and
actual placement legality, live conservation, incremental guide refresh and
routing remain unmeasured for B.

## Same-B native-legality correction

The first actual B cheap probe reproduced 35 nets/36 pins/39 diodes and applied
the exact HOST plan. Incremental guide refresh returned, all non-target
placements/connectivity/PG were conserved, and the complete live moves matched
the HOST proposal. The unchanged native placement checker then failed DPL33:
one blocked-layer violation on ANTENNA_110. There was no verified hook receipt
or detailed route. The failed run and its 557 frozen input seals remain intact.

ANTENNA_110 was moved to bbox `(1112160,3780)-(1113600,7560)` DBU. Its A-pin
access witness clears the VPWR M2 stripe beginning at y7340, but the complete
cell bbox overlaps the stripe's bottom 220 DBU. The planner had omitted an
applicable placement-legality rule. At the same pinned OpenROAD revision:

* [network.cxx:87–99](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/dpl/src/infrastructure/network.cxx#L87)
  marks each routing pin layer and its upper via-access layer as used. The
  pinned antenna master has only M1 pin geometry, hence used levels 1 and 2.
* [Grid.cpp:141–190](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/dpl/src/infrastructure/Grid.cpp#L141)
  marks all special-net non-via, non-DRCFILL, nonhorizontal M2/M3 rectangles in
  the covered row/site pixels. This applies to special signal nets too.
  [geom.h:636–643](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/odb/include/odb/geom.h#L636)
  treats a square as horizontal. [Grid.cpp:578–639](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/dpl/src/infrastructure/Grid.cpp#L578)
  floors the start and ceils the end on the core-relative site/row grid and
  clips it to valid core pixels.
* [PlacementDRC.cpp:157–178](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/dpl/src/PlacementDRC.cpp#L157)
  rejects any covered full-cell pixel whose blocked layers intersect the
  cell's used layers. It does not restrict this check to A's rectangles.

Root authorized correcting that omitted legality rule within the same
registered B strategy. Its exact movement definition, Manhattan/tie order,
variant ledger, A-pin/default-via/escape predicate and fatal placement check
stay unchanged. There is no third strategy. New version-2 live snapshots
record every net's actual `isSpecial` flag and every non-via special routing
shape with its wire-shape class. A new independent rule uses the exact official
480×3780 DBU grid and actual master used-layer applicability. Full special
geometry and flags are also conserved before/after application.

The exact source intake is
`build/campaigns/8x4-20261024-01/pg-blocked-layer-source-02/manifest.json`,
SHA256 `a1006bd413d06facf149b583a0bad640769e92ec686f137ce72691d9a3f31350`.
The first unexecuted intake copy had an extra trailing newline and is retained;
only source02 supplies the exact primary bytes used here.

The fresh HOST packet at
`build/campaigns/8x4-20261024-01/pg-B-legality-feasibility-HOST-01/report.json`
reopens the failed Native B artifacts and all 557 original input seals. An
explicit HOST-only adapter reconciles every one of the 355 non-via special
DEF shapes against the old full PG census; Native never falls back to that
adapter. The corrected source rule independently reproduces exactly the
ANTENNA_110 blocked-layer failure, then finds all 39 sites with complete
access/legality certificates and simulated conservation. Only ANTENNA_110's
location changes relative to failed B01: the new bbox ends at x1112160, exactly
outside the first blocked pixel. The maximum displacement stays 37.260 µm.
Planning took 0.765 seconds and the whole HOST packet 5.466 seconds. Seventeen
portable controls pass under normal and optimized Python, including the exact
raster boundary, shape/layer/class applicability, complete snapshot census and
unchanged A failure. Corrected Native placement, routing and signoff remain
pending.

## Corrected B02 bounded Native result

The corrected B late probe closed at 2026-10-24 16:12 UTC with exit0 after
306.830 seconds. Its actual placement check passed, the version-2 special
census contained all 355 non-via special shapes and both special nets, all 39
target moves preserved non-target placements/connectivity/PG, and the helper
independently verified the applied access and blocked-layer certificates.
Incremental guide refresh produced the retained 12,825,131-byte guide file.
The actual banner observed two OpenROAD threads; cgroup observations were
`cpu.max=200000 100000`, memory 6,442,450,944 bytes and zero swap.

The bounded detailed route's completed violation counts were
`805 → 162 → 135 → 3 → 0`; its final `bounded.drc` is empty. This is a clean
bounded diagnostic route, with the full ordinary DRT/antenna loop still
pending. It does not establish that the complete new flow closes or that
qualified extraction, timing, final-target proof or signoff passes.

The independently reopened inner report is
`build/campaigns/8x4-20261024-01/native-pg-B-late-02/report.json`, SHA256
`18c2d822741d2e184fb6b891754a428fdea3bb6707d16b48a894885870a2b88a`.
Its full artifact inventory matches. The outer resource report is
`build/streaming-tt-resources/8x4-24-pg-B-late-02/report.json`, SHA256
`efe273cb1bc196ac5774a31a51a8abb8e9168247ebe9401099c9925d41f9e6b0`.
It closed completed0, all 647 actual input seals rehashed unchanged, cleanup
confirmed and no owned processes/containers/errors remained. The earlier
failed A and B01 receipts remain failed and preserved.

## Full-flow routing observation and remaining antenna failure

The seeded full B01 run has written its own completed `02-openroad-detailedrouting`
state (SHA256 `ec681023c4f6890e8ba4c308c984a165b55976a1842e5dd0f2f454783181e544`).
The whole configured DRT loop reached zero route DRC errors. It ran all three
configured antenna repairs, added seven new diodes in batches 5/1/1, and verified
every corresponding PG-aware placement/access/conservation receipt. There is no
fourth repair pass or additional placement strategy. At this observation the
ordinary downstream flow was still active; completed DRT does not close antenna,
qualified timing, final-target correspondence, or signoff.

The retained detailed antenna report identifies one remaining net/pin failure:
`engine.core._0083_.Y`, `fanout276/A` (`sg13cmos5l_buf_1`), Metal3 cumulative
area ratio **213.80 against 200.00**, a 6.9% excess. The canonical summary uses
the partial ratio 209.73/200, approximately 1.05; that is not the violated
cumulative ratio. The full report gives a zero partial-area limit and explicitly
marks the cumulative criterion as violated. The report hash is
`b75e3226d0d8f15f7a81573fbea6189069718ef6f77384e443d959d4fc0f1206`.

Four actual `sg13cmos5l_antennanp` A pins connect to this net: ANTENNA_95,
ANTENNA_134, ANTENNA_139 and ANTENNA_140. Their LEF declares
`ANTENNADIFFAREA 2.0154 LAYER Metal1`; the protected buffer gate declares
`ANTENNAGATEAREA 0.1807 LAYER Metal1`. Full-net connectivity therefore does not
explain the failure by absent diode instances or missing diffusion metadata.
The problem is layer-prefix connectivity: the diodes join the vulnerable input
only once Metal4 is included. At Metal3 the vulnerable branch has no connected
diode; the actual checker retains the limit 200 there, and only at Metal4 raises
the diffusion-sensitive cumulative limit to 173880.

The immutable HOST diagnosis is
`build/campaigns/8x4-20261024-01/pg-B-full-antenna-diagnosis-HOST-02/report.json`,
SHA256 `1238325b6bfc5882d3dbd618100aee6eef40fa2506ac2f9536fbfc52ff48d5d7`.
Its exclusive producer/read-only `--check` reopener binds 13 exact input files,
the complete selected DEF net record, final DEF-to-snapshot endpoint positions
and orientations, all transformed pin rectangles, and pinned source. It admits
every clause: 27 wires, 27 named technology-via placements, eight relative RECT
patches, seven endpoints and 106 routing/pin rectangles. Even with conservative
square wire end caps, all Metal1–3 components separate fanout276 from all four
diodes; including Metal4 connects all seven endpoints. This is a diagnostic
rectangle-graph result anchored by the actual ARC report, not a second ARC area
calculation or selected final-target authority. HOST01 is preserved as an
unexecuted superseded analysis packet; HOST02 adds exact final-DEF placement and
pin/layer report joins. Normal and optimized readback reproduce HOST02 exactly.

Pinned `WireBuilder.cc` lines 51–63 explicitly skip existing detailed ROUTED
wires, so the repair check does not silently replace them with a global-guide
estimate. `AntennaChecker.cc` lines 999–1019 explicitly describe cumulative
repair as a naïve one-diode-per-gate approach. Canonical insertion and incremental
global-guide refresh therefore do not guarantee clean antenna results after
the subsequent detailed route. The observed remaining repair need is to make
diffusion protection reach the vulnerable Metal1–3 component, or reduce its
cumulative exposed area under the unchanged rule. No such geometry change is
authorized or made in this packet; antenna acceptance remains false.

## Unqualified inherited-RC timing diagnostics

The completed `13-openroad-stapostpnr` observation uses the inherited,
unqualified extraction model. Its input hold path is
`ui_in[5]` to `engine.frontend._0230_/D`: slack is −0.043539 ns
at `nom_fast_1p32V_m40C` and −0.031654 ns at `nom_typ_1p20V_25C`.
The worst setup slack is +2.137782 ns at
`nom_slow_1p08V_125C`. The same metrics report zero maximum
slew, capacitance and fanout violation counts. These observations cannot pass
qualified timing, qualify the CMOS5L RC model, or authorize an ECO or third
physical strategy. In particular, positive setup/electrical observations do not
erase either negative input hold result.

Exact retained raw files under
`build/campaigns/8x4-20261024-01/native-pg-B-full-01/flow/13-openroad-stapostpnr/`
are bound by SHA256:

- `nom_fast_1p32V_m40C/min.rpt`:
  `478034194ce67f994d0ad6c14d4d7e38fcebb927d68d7ff873c9e2091cd2539d`.
- `nom_typ_1p20V_25C/min.rpt`:
  `c1d871ad7e3837ebe34d9abc9f62ddc5f39152a915473a3a0a2983aeb00eba5f`.
- `nom_slow_1p08V_125C/ws.max.rpt`:
  `9e066a291654a6a245baeafdfb3bf3e5021a717c9aefc8c4fedf6b6668a6dd63`.
- `summary.rpt`:
  `dea6387062c56b0484612a8b405722c961013ec4308f336a565a76824c1bed27`.
- `state_out.json`, containing the exact per-corner and aggregate electrical
  metrics: `5b3eceff197a2bc5a9b22fcf35142e9ed256715294f9836b81cb44850a57eb83`.

The separate initial-path probe remains failed after its 94-diode canonical
repair and subsequent hook guide-refresh congestion; it has no verified
initial-path closure. Its retained failed1 report hash is
`5b787ab2af78acfd0668ebdbc4181dc1ce773e21340af5b046be0fcd8d5463d2`.
The seeded full run's downstream terminal/cleanup remains pending at this
observation. Neither this stage report nor the earlier antenna diagnosis is a
selected final-target or final-flow acceptance receipt.

## Seeded full B01 terminal closeout

The full run closed at 2026-10-24 17:42 UTC as a normal failed2 flow, with
deferred hold errors at the fast and typical inherited-RC corners. Its actual
terminal metrics report router/Magic/KLayout DRC zero, Magic illegal overlap
zero, and zero reported LVS errors, device/net differences, property failures
and unmatched device/net/pin counts. The detailed antenna failure remains one.
The flow reached ordinal 32 (`Misc.ReportManufacturability`) and wrote 31
completed state files; ordinal 29's failed Hold checker did not write a state.
No third physical strategy or extra antenna repair was executed.

The independently reopened full report is
`build/campaigns/8x4-20261024-01/native-pg-B-full-01/report.json`, SHA256
`d311e45b88a58d00ac2a7fa76d546c27f51d1a12743b8ff4f96cadf947baf244`.
All 449 recorded artifacts match. The outer resource report SHA256 is
`9f77fe4a679299c47b25aac9f2fbe293b8130c34f98c62ae2eae49df5dc612d9`;
it closed failed2 with inputs unchanged, cleanup confirmed and no remaining
owned processes or containers. The current preparation and resolved contract
also independently reopen, preserving the registered B policy, 20 ns clock,
85% target density, 64 routing iterations and two-worker resource policy.

The normal-failure selector admits the latest authenticated state32, SHA256
`3ecda55452e3b37821c371d3aefa9948e598e5711fffd69e2ee68e60b6c2ba2c`,
whose actual ODB is the fresh `11-odb-cellfrequencytables` output, SHA256
`f516ffbca3cd86e5cd214c515ca0be457a91a517dbe715caa47336aec907eee0`.
It contains 98,957 instances after filler insertion, versus 42,184 at DRT02;
the earlier DRT/diagnosis database must not replace this selected authority.
Selection is eligibility for fresh fixed-target proof and signoff. It does not
turn the failed flow, antenna result or unqualified timing into acceptance.

The terminal warning inventory also matters: `Checker.WireLength` skipped its
check because no threshold was configured, and `VSRC_LOC_FILES` was unset for
the nominal IR report. The latter cannot establish qualified supply delivery
or package/IR-drop acceptance. EQY, KLayout XOR and linter remain explicitly
disabled. A scheduled or completed state is not evidence that a skipped check
ran. Fresh actual-target GDS geometry, official precheck, independent antenna/
transistor LVS, all-terminal geometric PG, final correspondence and qualified
extracted timing retain their separate evidence requirements.

The diagnosis was independently reproduced by Digital and Root under normal
and optimized Python, with all 13 input seals and all 106 shapes unchanged.
It does not establish that B relocation caused the final miss. The canonical
postrepair snapshots repeatedly put ANT134/139/140 at the same starting bbox,
already about 45.06 µm Manhattan distance from fanout276's bbox. B guarantees
legal PG-safe access and conservation; it does not constrain the later router
to join a particular etch-prefix component. The observed remaining mechanism
is established by the actual detailed topology, without a counterfactual run.
