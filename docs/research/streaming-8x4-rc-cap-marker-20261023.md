# Frozen v1 zero-distance lookup discriminator

This is a synthetic dispatch experiment. Root has now executed the frozen
packet; its original quantitative prediction failed, as recorded below.
It does not fit a physical coefficient or qualify capacitance,
timing, the five-layer model, or the original failed C5L measurement.

The two calls use the same six nets/twelve ports: centered Metal1/Metal2 pairs
at lengths 50, 100 and 150um, separated by 512um, with 32um padding. Drawn widths
are .16/.20um; vertical conductor bounds and the complete TYP material stack
are bound to the original reference case. There are no cells, ITerms, vias or
NDRs. Geometry is checked before and after extraction. Both calls retain the
original command version 1.0, coupling threshold 0, context depth 5, cc_model 10,
and omit lef_res/merge_via_wire_res. Table format Version1.2 is a separate field.

The retained table is SHA256
`bf2af2235b102d7bb58fe782d8d8b41a64cb3efde46593562314a499e9c4a612`.
The marker changes exactly the first distance-zero fringe token in
`Metal 1 DIAGUNDER 2`, from `0 0 0 0` to `0 0 0.000001 0`.
Reversing this single token restores every original byte, including all nearby
rows. Marker SHA256 is
`b212c4ddd5e092288564a0190813e8528082ca7828e6fe22c403c8ddd25ef71c`.
The token is a lookup tag, not measured physics.

Pinned OpenROAD commit `dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`
selects the v1 flow for command version 1.0. The captured `extmeasure.cpp`
shows overlapping transverse intervals produce distance 0 (`calcDist`,
lines 516–527). Its ordinary DIAGMODEL1 branch calls `calcDiagRC`; that branch
multiplies length by the selected fringe coefficient with DOUBLE_DIAG=1
(lines 2129–2153). The pinned `extRCmodel.cpp` parser reads the third numeric
column as fringe, selects the first row for distance at/below its first
distance, and `getDiagUnderCC` returns that fringe value. Model1 is selected
by DIAGMODEL ON. The higher accuracy vertical branch is statically disabled
by `skip_high_acc=true`; these facts are source evidence, not a runtime trace.

The source prediction is `1e-6 fF/nm = 1e-12 F/m = 1pF/m`. Both consecutive
coupling length slopes must match that value within 0.1% and each other
within 0.1%. Complete matrix/ground consecutive slopes retain a 5% gate.
An absolute endpoint intercept is not predicted. Actual aggregate dispatch
could count another context or fail to reach this branch: factor2, zero, other
slopes and warning/exit failures must remain failures without tuning.

The retained call must still fail the frozen positive intended-coupling gate
with its exact original error. A separately typed inventory rechecks all
unit, six-net membership, CAP/RES node/graph, complete D_NET totals and mirrored
pair semantics, and requires all three explicit couplings to remain exactly
zero. It constructs no baseline Maxwell matrix. The marker call must pass the
unchanged full strict SPEF parser, including positive intended coupling. A
zero process exit cannot override either parser failure.

The fixed resource budget is two 30s calls, 90s observed work and 120s outer,
one CPU, 2GiB RAM, 128MiB tmpfs within that RAM, no additional swap. Both declared
calls are attempted after closed numerical failures; resource/custody failure
stops the packet. The reader requires complete ordered membership, observed
actual work and source/input/cgroup/shared lease/cleanup custody. Eight focused
HOST controls pass normally and under Python optimization; no Native ran here.

The new source intake
`build/campaigns/8x4-20261022-01/rc-cap-marker-source-intake-01/manifest.json`
has SHA256 `95da0f94b1eccd8a91e5f5ca121f1cba9d4b9cb3807af33823e6383bce3a766b`.
It captures the 72148-byte extmeasure.cpp, SHA256
`d44faac2f40ee4e1e28315c26967887d957ec53112b77b94f561869d3009e8b7`,
Git blob `b865cb31f34bbf2ce43837a328444fff9bf1f835`.
Its primary source is [pinned OpenROAD extmeasure.cpp](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/rcx/src/extmeasure.cpp).
The existing model/dispatch intakes are copied and independently verified by
manifest hash, file size, SHA256 and Git blob. All retrieved source is data;
none is imported or executed.

Preparation01 lives at
`build/campaigns/8x4-20261022-01/rc-cap-marker-preparation-01/plan.json`,
SHA256 `fc7ae74c34b0cfacb2413cf1180c379863be8fc786cf18ecec14459364bfd57a`.
Command proposal01 SHA256 is
`e9e6a3aba0464c5b1d988a0e0ca021f75c04efb4e074866c836adacbe302c3e8`;
HOST readiness01 is
`3c2f8442c897c642fad36392eb98690bffbefca341bd42962b2bfa6aa92b9540`;
launcher/reopener01 is
`25dd0525455056c3fb7d20f29cd1a1da95df3a9523744bd43e89a51d9fae2a43`.
Root must supply and seal its explicit GO before the wrapper invocation.

The original source of the zero table endpoint is still unproven. Root recovered
the authenticated four common generator scripts as data, but no raw pattern,
caps file or generation log accompanies this selected intake. The marker tests
consumer selection; it cannot establish the credibility or physical generation
of the draft table's zero endpoint.

# Actual failed prediction and source explanation

Root executed source commit `874fbe5` under GO SHA256
`913467128a38d61233bfedace03fd2aef1217e43c7ded884d2738e2c49073fd9`.
Both fixed calls completed with exit 0 and no warning/geometry/unit failure.
The retained call preserved its original strict positive-coupling failure and
all three explicit mirrored couplings were exactly zero. The marker call
passed the unchanged full strict SPEF parser. Its unique pair couplings at
50/100/150um were .10032/.20032/.30032fF. Both consecutive slopes were exactly
2pF/m, versus the frozen 1pF/m prediction: **100% error, diagnostic failed**.
Coupling slope linearity was exact; the largest complete matrix/ground
consecutive change was 0.000827942%. Neither observation relaxes the prediction.

The frozen independent HOST reader produced
`build/campaigns/8x4-20261022-01/rc-cap-marker-independent-readback-01.json`,
SHA256 `633725e5669b788df4200af45db46c183f1b8c008136e7291308357f533bf59d`.
Observed work was .51398425s. Resource receipt SHA256
`f24c830199c4235118f27a6161791c0ddaa3676d4dddd0fbb5d1f20e466b3e20`
closed failed with exit2, input seals unchanged, cleanup confirmed and no owned
process/container residue. The exact GO was independently matched to its input
seal. The one-token intervention establishes that this row influences actual
centered-pair extraction; it does not establish physical correctness.

A subsequent source audit explains the additional accumulation. This audit is
after measurement and cannot turn the frozen prediction into a pass:

1. `extCC.cpp`728–756 calls `Track::couplingCaps` twice for the same source
   track, reversing target direction between calls. `grids.cpp`2718–2720
   implements that reversal. The second pass suppresses ordinary same-layer
   coupling but retains empty-space processing.
2. `extCC.cpp`446–487 emits no-neighbor callbacks for the unoccupied source
   length on each side. It explicitly sets `ignore_visited=true`, so the second
   empty-side callback is not suppressed by the first pass's visited flag.
3. `extmain.cpp`726–740 calls `measureRC`, whose `defineBox` stores the side in
   `_toHi`. The captured `extmeasure.cpp` contains no other use of `_toHi`.
   The diagonal path therefore repeats the same centered-overlap lookup on
   both side callbacks. Ordinary `calcDiagRC` still contributes `len*fringe`
   once per callback; its literal DOUBLE_DIAG remains 1.
4. `extmeasure.cpp`1918–1942/2011–2024 requests merged parallel CC segments
   and adds each contribution. `dbCCSeg.cpp`501–538 reuses an existing node
   pair when `mergeParallel=true`; lines206–216 add rather than replace its
   capacitance. The two contributions accumulate in one physical CC segment.
5. The writer prints `getCapacitance()*_cap_unit` (`extSpef.cpp`950–973),
   with PF factor .001 (1517–1519). Symmetric source/target SPEF rows repeat
   the stored value; they do not double that value. The frozen parser requires
   equal mirrored copies and counts each unordered node pair once. The actual
   packet has three unique CC segments, not six. At DBU 1000 the model reader's
   dbFactor is 1 (`netRC.cpp`1635–1639), so its coefficient rescaling adds no factor 2.

This static control flow plus the measured differential supports two native
1pF/m contributions as the cause of the observed 2pF/m slope. It is not an
instrumented callback trace or proof for other geometries/policies. No new
coefficient, producer, prediction tolerance or Native call was introduced.

The postmeasurement primary-source intake is
`build/campaigns/8x4-20261022-01/rc-cap-marker-factor-source-intake-01/manifest.json`,
SHA256 `528c34d24c50960d83489727ae3ceb50fc527f6f614fd06db9ddf62caa190acb`.
It binds exact size/SHA256/Git blobs for
[extCC.cpp](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/rcx/src/extCC.cpp),
[grids.cpp](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/rcx/src/grids.cpp),
[dbCCSeg.cpp](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/odb/src/db/dbCCSeg.cpp)
and the grid header. All are read as data; no retrieved code was executed.

# Conditional generation-side convention

A final read-only source check found an additional explanation, conditional
on the generator executable using the helper-pinned OpenROAD source
`e304dc6304a5ef637bb69388935af37fdbddb112`. The authenticated generator shell
reads both one-wire and three-wire pattern tables, but does not pin its
`OPENROAD` executable. The selected archive has no raw caps files or model
generation log, so this is not an authenticated trace of the retained table.

At that commit, `extRCmodel_solver.cpp`130–131 marks one-wire patterns open;
229–231 initially sets their total coupling to zero; 298–300 forces distance
zero. Lines235–237 can further change coupling when context coupling is
positive, so a zero endpoint is not guaranteed for every open pattern.
For a diagonal row with zero context coupling, lines240–255 store normalized
coupling in the fringe field rather than the separately read solved ground
capacitance. This can produce `0 0 0 0` even when solved ground capacitance
is nonzero. It is a representation mechanism, not physical evidence that two
vertically overlapping conductors have zero coupling.

The same source divides total coupling by wire length **and by two** before
storing it. That is consistent with the two-side runtime accumulation described
above. A factor of two between a synthetic table token and the final pair
slope is therefore not itself evidence of a physical or serialization bug.
The original marker experiment's frozen one-pF/m prediction remains failed;
this later source context neither changes that result nor calibrates a model.

Primary source pins, fetched only for inspection and not saved as a new intake:

- [OpenROAD diagonal table import](https://github.com/The-OpenROAD-Project/OpenROAD/blob/e304dc6304a5ef637bb69388935af37fdbddb112/src/rcx/src/extRCmodel_solver.cpp),
  Git blob `b0f09255ed5528800192d6bbcd2d5d2d5966460d`.
- [OpenROAD DIAGUNDER writer](https://github.com/The-OpenROAD-Project/OpenROAD/blob/e304dc6304a5ef637bb69388935af37fdbddb112/src/rcx/src/extModelGen.cpp),
  lines349–365, Git blob `85485617402ffd0b0f96e9fed8c8ae0473b7f19a`.
- [OpenROAD four-column row serialization](https://github.com/The-OpenROAD-Project/OpenROAD/blob/e304dc6304a5ef637bb69388935af37fdbddb112/src/rcx/src/extRCmodel.cpp),
  lines151–153, Git blob `6745de3132123e3f82052f3fed866cd3a59e8c78`.

The recovered shell/source custody is
`build/campaigns/8x4-20261022-01/recovery/generator-source-01/SOURCE-CUSTODY.json`,
SHA256 `1bc822d2c8c468e70dc3f7617f05d67c0deca2100fc3b371383616451d651c50`.
No generator, solver or new Native call ran during this audit. No numerical
start followed the campaign cutoff; completion01 and the OOC600 proposal add
no executed extraction evidence.
