# Same-candidate routing diagnostic replay

This diagnostic starts from the sole repaired candidate's saved
clean internal `drt-run-0` database. It creates no physical candidate and cannot
be selected as a final route, signoff, timing, or Boolean-proof target. The
original interrupted repair and all frozen producers remain unchanged.

The source ODB is 51,679,576 bytes, SHA256
`596af58622f1e194f4e55897e0c27c1420a28450c8d2848fa913849eb877f0d8`,
at `build/campaigns/8x4-20261022-01/native-repair-02/flow/03-openroad-detailedrouting/drt-run-0/tt_um_pinwheel_streaming_ready_d2.odb`.
Its internal DRC report is empty. The parent run remains interrupted130;
the campaign resource guard stopped it124 near the memory threshold and
confirmed cleanup. Neither receipt supplies a completed DetailedRouting state.

The new producer pins the actual parent report, resource receipt, complete
artifact inventory, repair/original preparations, native image, full staged PDK,
unchanged DRT configuration, original actual command and full20ns SDC. It uses
the canonical LibreLane DetailedRouting class's configuration/environment,
cell-corner and subprocess machinery with a separately identified Tcl body.
No earlier placement, CTS or routing prefix is executed. The body loads the
saved ODB and performs the following fixed sequence:

1. Capture the before ODB/DEF, power-inclusive netlist and complete
   instance/master/location/terminal/net ownership census.
2. Run unchanged `check_antennas`, using pinned `tee -variable` to observe the
   command's own messages. Require35 returned net violations and exactly36 pin
   violations. Mismatch terminates before repair/routing.
3. Run the original `repair_antennas sg13cmos5l_antennanp -ratio_margin 10`.
   Capture postdiode ODB/DEF/netlist/census/guides, then require returned39 and
   exactly39 added instances before any DRT call. The HOST reader independently
   requires39 new canonical diode masters, preserved existing connectivity and
   complete endpoint membership, then reports touched-net fanout deltas.
4. Run `detailed_route -droute_end_iter 6 -or_seed 42 -verbose 1
   -drc_report_iter_step 1 -output_drc .../bounded.drc`; retain actual iteration
   DRC reports, final bounded DRC coordinates and postroute ODB/DEF/netlist/census/
   guides. This termination differs explicitly from the original64-iteration
   routing allowance. Postdiode evidence survives later timeout/failure.

The API/source chain is pinned at OpenROAD
`dcf36133a369abc8f3c5e5738cd4d82e4903c0e0` in
`build/campaigns/8x4-20261022-01/intake/routing-replay-source-02/manifest.json`
(SHA256`c047454e404408023508a1930a9d897e812e0fd6a3a18877303af55235f03425`).
`GlobalRouter.cpp:480–575` initializes its routing structures, invokes canonical
diode repair, updates dirty routes and saves guides. `RepairAntennas.cpp:169–241`
fixes other detailed-route instances and runs detailed placement of the repair.
`AntennaChecker.cc:1232–1247` logs both counts and returns the net count.
`Utl.tcl:100–173` implements the observation-only tee. `TritonRoute.tcl:88–98`
supports `-droute_end_iter`; `FlexDR.cpp:1973–2012` stops once the iteration index
exceeds6 and writes the final DRC report.

The version query observes both return values and printed output of
`ord::openroad_git_describe` and `ord::openroad_version` through the pinned tee.
The Oct18 inventory observed an empty describe return. `OpenRoad.i:278–288` and
`OpenRoad.cc:724–731` show that these commands expose separate build strings.
The new script preserves all four raw observations and requires exactly the
pinned full40-character revision, rejecting empty-both, wrong, conflicting or
prefix-only evidence before any capture/repair. This handles empty return with
correct printed revision explicitly; it does not bypass version verification.
The earlier source01 remains unexecuted and unchanged.

Reproduction is limited. The historical second DRT used an existing in-memory
router and `updateDesign`; the fresh process uses `readDesign`
(`TritonRoute.cpp:573–585`). Count agreement does not prove identical historical
diode positions, route decisions or residual40 shapes. Any new shapes describe
this declared reconstruction. Counts, added-cell identities, locations,
connectivity, route trajectory and DRC ownership must be reported explicitly;
absence of a matching historical postdiode ODB prevents stronger identity.

Resources remain4CPUs,4OpenROAD threads,6GiB with no additional swap,
512MiB temporary filesystem and the existing95% memory guard. A1770s native
process-group bound leaves closeout within1800s work; Root's separate campaign
guard has1860s outer allowance and unchanged shared lease/host reserves. Root
must admit and start it before the03:00:35Z physical cutoff. No Native process is
launched by preparation or the HOST tests. Reproduction observation, bounded
route return and successful controller closure are separate receipt fields;
all final physical/model/timing acceptance flags remain false.

## Executed reconstruction and preserved adapter failure

Root dispatched the exact preparation under its external GO
`7e52da975ba34e626cc193a36e47fa02c1d7442ec79c9042588ee7bf5813337e`.
The Native process completed with exit 0, reaped its process tree and used
221.704 seconds of its 1800-second work allowance. The strict actual query
observations were empty describe return/output, exact full pinned revision in
the version return, and empty version output. Reproduction was exactly 35 net
violations, 36 pin violations and 39 diodes: 42,138 → 42,177 instances. All 39
new canonical diode masters and the existing terminal graph were captured;
none of the 35 touched single-driver nets exceeded 10 endpoint loads.

The original HOST report adapter failed. Its display-line equality rejected
Rich's trailing-space padding after the correct revision. Its next strict
argv check would also reject the canonical `openroad` alias because it expected
an absolute executable path. The frozen independent HOST command was executed
and failed with exit 1 at the version comparison; its failure trace is retained.
The original replay report and outer resource receipt remain failed 2. Cleanup
and all 150 guarded input seals closed; remaining process/container lists are
empty. No frozen producer, report or gate was changed, no CAD replay was run,
and no corrective HOST adapter has been admitted.

The retained outer metadata also records the macOS framework Python executable
behind the Homebrew launcher stub. These are different paths and bytes. The
separate HOST analysis records both identities explicitly and verifies the
remaining complete argv rather than silently asserting path equality.

The bounded reconstruction has 42 Metal2 DRC records: 36 Short and 6 Metal
Spacing. Every record pairs a VPWR/VGND rail with one of 19 newly diode-loaded
signal nets. A separate unqualified HOST analysis checks exact typed owner
membership, actual DEF/LEF geometry, all captured artifact/input hashes before
and after, and exact integral 1000-DBU coordinate conversion. All 36 Short
rectangles equal intersections of actual signal wire/via/patch rectangles (or
exact filled rectangular unions) with actual Metal2 PG stripe rectangles. All
36 also project onto the Metal1 A pin of an associated new diode. Fifteen of
the 39 new diodes have every A-pin rectangle fully beneath one of the 70
positive-width Metal2 PG stripes in cross-layer projection. New diode locations
remain unchanged during this bounded route.

For example, net343 receives ANTENNA_115 at lower-left (1112.160, 461.160) µm,
orientation MX. Its A-pin x range 1112.540–1113.210 µm lies entirely below the
VPWR Metal2 stripe spanning x=1112.380–1113.380 µm. The actual Via1_YY at
(1113.120, 462.420) µm has Metal2 enclosure
(1113.020, 462.275)–(1113.220, 462.565) µm, exactly the first Short marker.
The signal's default-width Metal2 wire intersects that same PG stripe in
(1113.020, 462.320)–(1113.380, 462.520) µm, exactly its second Short marker.
This identifies actual local power-strap/access conflicts in the reconstruction;
the cross-layer pin projection alone would not establish an electrical short.

This evidence points the next physical investigation toward PG-aware placement
and access of newly inserted diodes. Increasing routing iterations or reducing
global density has not been shown to remove those fixed local intersections.
Any proposed repair still requires a new authorized physical candidate. The reconstruction
does not prove identity with the historical 40 markers or qualify a final ODB.
The original full-flow DRT, antenna, DRC/LVS, extracted timing and proof/signoff
gates remain open. New diode PG ITerms are still unassigned at this canonical
pre-write_views point; the later global-connection stage was not executed.

| Retained artifact | SHA256 |
| --- | --- |
| Original replay report | `9b7e033886de222377878ca7b191e2de68cdcb2daac429602bb0a25052f41c07` |
| Original failed-2 resource receipt | `428700d572fdef8b74ae2e4b5ebc583bd186520c29972fb468467a49f1b466c8` |
| Frozen HOST reader failure trace | `df0c646175141abb6764b9e0e97dbc8c6820290ec891a055ad38e6f441bc196b` |
| Actual postdiode ODB | `a0c41ff2ffef86fd7fc0d2e592184832b6158079d9f5824258a9539aaa8e1f4f` |
| Actual bounded postroute ODB | `034d2f31d3a4b368894e80201d14a5c0c345c1d257cc90b7e0c6f5758c233f8c` |
| Actual bounded DRC report | `72942ab535ae5e54606b9c3b9545322cf5bd1f8c66502db54a9b341d4b66d8f8` |
| Separate HOST shape analysis03 | `a73fb5aede7059b823d990d463bf95b0f2e9daaabdb0bc30a100ec4a1cdd1308` |

Raw run artifacts are in
`build/campaigns/8x4-20261022-01/route-replay-preparation-01/`.
The separate HOST source and full 42-record analysis are in
`build/campaigns/8x4-20261022-01/route-replay-coordinate-analysis-03/`.
Earlier analyses01 (24 exact Short matches) and02 (36 matches before the
additional end-of-analysis/integral-coordinate guards) remain unchanged.

The [measured illustration](../physical/figures/streaming-8x4-diode-strap-conflict.png)
is a static rendering of the ANTENNA_115 / net343 example in analysis03, using
equal physical x/y scales. Its scene is retained at
`build/campaigns/8x4-20261022-01/diode-strap-conflict-scene-01.json`, SHA256
`a62ecfcec614cb19b135ea89c39826728d837b323a72144ae5aa285f2e35ef6b`.
The source-controlled SVG SHA256 is
`3978476fbdc03be18d6a90aaa939c6fe9247ca50e84c09602266535e24510749`;
the rendered PNG is
`580fa49d30bcc5a0cd60fa8c768486702f9ff0330e47dc1030b078f2e57d69b5`.
The plot grants no additional physical acceptance.

## Six spacing-marker readback

A separate HOST-only fixed-data analysis now explains the six remaining
`Metal Spacing` records. Each marker bbox equals the positive horizontal gap
between an actual Metal2 PG stripe edge and signal wire or via enclosure:

| Ordered marker IDs | PG / signal | Gap |
| --- | --- | --- |
| 37–38 | VGND / `net755` | 80 DBU (0.08 µm) |
| 39–40 | VGND / `engine.core._5933_.Y` | 80 DBU (0.08 µm) |
| 41–42 | VPWR / `net1759` | 200 DBU (0.20 µm) |

All eight original capture/LEF hashes match before and after analysis. The
complete retained Metal2 spacing table has PRL thresholds 0/1/10 µm and width
rows 0/0.39/10 µm, with entries 0.21/0.21/0.21, 0.21/0.24/0.24 and
0.21/0.24/0.60 µm. Every measured gap is below its minimum 0.21 µm; each
parallel overlap is below the first nonzero PRL threshold. No internal checker
rule ID is present in the DRC text, so the claim is exact geometric
incompatibility with the retained LEF table, not reconstruction of that ID.

The producer and report are retained under
`build/campaigns/8x4-20261022-01/route-replay-spacing-analysis-01/`:
source SHA256 `dd8f2ee811822f31e3b5ed6dfd9f2e8af69eafceb90237bf3f184cbee9300c57`;
report SHA256 `94d5d84be05a2fdcd9638d64af041901eb21eaf960e1344a5f77520942c57016`.
Root independently rederives the entire result in memory and recomputes all six
gap rectangles; its readback SHA256 is
`945735a122cbd4a88910b961575c3ee49ee745b81db743df322bdfa214c7feb1`.
This is a restricted direct-rectangle analysis, not a general DEF parser or
signoff run. All 42 reconstructed markers now have same-layer geometric
explanations. The original replay adapter remains failed, historical 40-marker
identity remains unproven, and all physical acceptance flags remain false.
