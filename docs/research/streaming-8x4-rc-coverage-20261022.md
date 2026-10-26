# CMOS5L RC coverage, terminal numerical state on 23 October 2026

This checkpoint records the executed extraction results after the campaign's
05:00:35Z numerical-start cutoff. No five-grid completion or 600-second OOC
solve launched. Independently reviewed preparation is not an observation.
All eight mandatory model coverage fields remain incomplete. Numerical call
completion, empirical reference stability, consumer behavior and full model
qualification remain separate states. No result below establishes qualified
CMOS5L extracted timing or a continuum error enclosure.

| Executed study | Actual result and limit |
| --- | --- |
| Layered M1 FVM reference04 | All 25 calls and six-case empirical gates pass: maximum mesh change 1.316004%, domain change 0.243027%, reported residual 9.991928e-10, energy/flux error 4.331996e-14. Potential/edge arrays were not retained; these latter values are source-bound producer diagnostics, not freshly recomputed linear algebra. |
| Complete uniform55 in-core pilot | All 55 numerical/resource calls complete, but the limited pilot fails its unchanged mesh gate: wide .32um/L20 case changes 2.296835% at the penultimate refinement. Ten of eleven cases pass; the final .143815% change does not waive the earlier failure. The extra-fine point has no accepted solve. |
| Finite real-stack M1 BEM | Original mandatory native06 first case fails; the fresh full150 policy is incomplete. Separate coarse/finest point diagnostics do not supply its full five-mesh/length/boundary universe. Finest disk-backed point times out at 120s without an accepted matrix. |
| Original upper-layer FVM32 | All 32 grids pass strict numerical controls, but domain stability fails for TopMetal1 self (5.05555%), M3/M4 pair (2.50265%) and M4/Top pair (6.42107%), against the same 2% gate. |
| Expanded E32/64 FVM32 | 27 strict grids pass; global027 times out at 120s and globals028–031 are unrun. Observed work 1017.972s, no OOM/memory preemption, cleanup closed. Complete reference authority remains false. |
| Six-call semantic R/via consumer | All six physical/custody calls close. All 72 original absolute wire-R controls fail at 0.1%; all 30 named-via difference controls pass. The composite via gate still fails its mandatory default-wire prerequisites. |
| Separate R26 length/width diagnostic | All six calls and separate slope/linearity/42 held-out length checks pass. Local per-corner LEF RPSQ plus explicit -lef_res restores the doubled-width slope ratio to .5. However, 123/126 new absolute audits still fail; this does not repair the original 72 failures. |
| Actual M1 C1 | All four strict measurement calls pass. Provisional FVM differences: isolated ground 47.06% low; minimum-gap pair ground 31.42% low, diagonal 13.12% low, coupling 5.82% low. Full frozen accuracy stays unmeasured because its mandatory finite-BEM prerequisite fails. |
| Version-only C2 | Both isolated slopes equal source-predicted 110.7332pF/m, but both pair cases lose intended coupling and fail strict controls. No coefficient changes. |
| Synthetic far-row study | All four measurement calls pass; the isolated training target is reproduced, but the untouched .36um held-out coupling fails the 10% gate by 18.86%. No postfailure retuning. |
| Five-layer consumer C5L | Both calls fail strict controls despite exit zero. Every centered adjacent-layer pair family prints zero intended coupling at all three lengths; no valid pair Maxwell matrix or accuracy is promoted. |
| One-token marker | Retained zero failure is preserved. Marker positive-coupling parsing passes, but both slopes are 2pF/m against the frozen 1pF/m prediction: 100% error, quantitative diagnostic failed. A postmeasurement source explanation is not a changed acceptance gate. |

The [five-grid completion](streaming-8x4-rc-reference-completion-20261023.md)
was implemented, HOST-prepared and independently reviewed at exact plan
`7bd27dc9a7f6e9b7f8e44189886f271a2ae8e20c5321ed662c49d26deb70abd9`.
It remained **unexecuted at the cutoff**, so no composite32 authority exists.
The [600-second OOC point](streaming-8x4-rc-ooc-600-proposal-20261023.md)
remained a proposal, with no corresponding numerical observation. The earlier
failed reference and OOC receipts remain unchanged.

| Mandatory field | Current executed evidence | Remaining obligation |
| --- | --- | --- |
| `resistance` | R26 establishes bounded slope/width behavior under its distinct policy; original and new absolute endpoint audits still fail. | Adopt and independently validate the intended route/endpoint/width consumer policy, including actual routed widths/current paths and justified process corners. The local diagnostic policy is not canonical signoff policy. |
| `ground_capacitance` | M1 FVM is empirically stable. C1 ground terms materially disagree; v1 regular last-distance selection is source/measurement grounded. Far-row isolated training fails an untuned spacing case. | Independent finite-BEM prerequisites; actual table/SPEF accuracy over spacing, width, ground, layer and layout contexts. An isolated fitted target is not validation. |
| `coupling_capacitance` | M1 minimum lateral coupling is provisionally within 10%, while its ground/diagonal terms fail. C5L vertical coupling is zero; marker proves row influence but fails its quantitative prediction. | Physically justified positive vertical/adjacent coefficients and independent validation across larger gaps, offsets, nonadjacent/orthogonal/diagonal and shielding contexts. |
| `via_resistance` | Owned tables provide 52 explicit tech-via names per corner; five fixture names pass the declared difference arithmetic across corners. Composite original gate remains failed because default wires fail. | Actual final design-used names/cut families, generated dbVia coverage, spreading/contact physics, independent-cut assumptions and process authority. Five names do not validate all 52 or generated vias. |
| `dielectric_interfaces` | Interface-anchored M1 FVM cases and equation controls pass. Original upper-layer FVM domain gates fail; expanded32 is incomplete. | Full independent finite-wire/reference agreement, upper-layer/passivation/air truncation and actual context applicability. Empirical FVM stability is not a rigorous continuum bound. |
| `layer_coverage` | Five nominal self and four centered adjacent contexts are measured, but consumer pair controls fail; full upper-layer reference authority is absent. | Complete reference stability and actual consumer accuracy for all applicable interactions and the final routed envelope. A passing layer sample is not full layer/context coverage. |
| `width_spacing_range` | One draft drawn-width sample per layer (.16/.20/.20/.20/1.64um); R26 and wider M1 FVM add limited controls. Consumer width clamping and finite far-row behavior are observed. | Held-out C width/gap ranges, interpolation/extrapolation/isolated limits, power/wide wires, finite ends, multiconductor contexts and the completed design's actual envelope. |
| `consumer_units_and_semantics` | C1 closes C_UNIT/full incident/mirrored/D_NET semantics; R semantic/R26 close bounded physical/units/rounding readbacks. C5L and marker preserve actual numerical failures. | Complete table-format/version/flag applicability and annotation on the same final ODB, followed by propagated-clock extracted timing at justified model/cell corners. |

The canonical timing path retains -lef_res and the retained technology LEF's
MAX sheet resistance. R26's local per-corner LEF substitution is a distinct
explicit diagnostic policy; it is not an adopted change to that path. Via
behavior is version-dependent and cannot be transferred between v1/v2 or
flag policies without the matching consumer evidence. No qualified corner
pairing is inferred by running arbitrary model/cell-corner combinations.

M1's ER-only FVM corner controls retain nominal geometry. Draft effective
widths change (.16um M1 drawn becomes .096/.160/.176um; 1.64um TopMetal1
becomes 1.340/1.640/1.740um). Those controls therefore do not establish the
correlated resistance/geometry/dielectric process-corner envelope. No final
routed signal-width/via/context census yet establishes required model coverage.
Sixteen empty width sections per corner are inventory facts, not sixteen
proven defects; available DIAGUNDER/OVERUNDER tables are not accuracy proofs.

The [marker source analysis](streaming-8x4-rc-cap-marker-20261023.md) supports
two empty-side callbacks accumulating into one merged CC segment. The writer
prints that stored sum and the reader counts mirrored copies once. This
postmeasurement explanation preserves the failed prediction. The authenticated
generator scripts delegate model assembly to an unpinned OpenROAD executable;
a conditional open-pattern representation mechanism is source evidence, not an
authenticated historical generation trace or physical coefficient validation.

Exact current evidence under `build/campaigns/8x4-20261022-01/`:

- Layered FVM25: `rc-layered-reference-independent-readback-01/report.json`,
  `128681523cd638cf4ef8be0c1aa57cb601f07cef581b72bd62014b1d8c2e2906`.
- Uniform55: `rc-uniform-incore-full-independent-readback-01.json`,
  `81547850af1c84bcb4a8398f80c19a9c5e5ba30e1fd89a02faed6b57df717d2f`.
- Expanded incomplete32: `rc-reference-expanded-independent-readback-01.json`,
  `f7061991c8aea61b5de02867bd7f5bee1b2dd26cfc0184fed0e4ce94f5490ae2`.
- Six-call R: `rc-consumer-semantic-independent-raw-readback-01.json`,
  `abce0d09344562621fd6df1b4e10b25d4c62af7a2cc478c40fe66ce87fe4d2d3`.
- R26: `rc-r-length-width-closeout-01.json`,
  `9e4394463fb1a1ac7f12e53410826968a5cac35248bc59c4e3ccd165db57c7b4`.
- C1: `rc-consumer-cap-independent-readback-01.json`,
  `b89ee54c5c95a4880abc5108586733587c18e1c0637d830b5328dc618da7b9b3`.
- C1 provisional FVM: `rc-consumer-cap-provisional-FVM-comparison-01/report.json`,
  `e90d52fb0b2e2be03009900b9223c9c08b0e245b218b7eb41238e879c8243532`.
- Far row: `rc-cap-far-independent-readback-01.json`,
  `bfc10aaacb56a4f6ae89aa6b5367b4faf51678c3928a4b89a05ab7bec8042051`.
- C5L: `rc-cap-all-layers-independent-readback-01.json`,
  `834764b8725748294ce22792bfa596fa487062112d3f7d95f7549e8d0bd932e3`.
- Marker: `rc-cap-marker-independent-readback-01.json`,
  `633725e5669b788df4200af45db46c183f1b8c008136e7291308357f533bf59d`.
- Finest OOC120: `rc-ooc-independent-readback-01.json`,
  `18070daf9090a528ff8373ccfb7d5f60d6ca39ca1045a7169ca209774b6f968f`.

## Preserved earlier 22 October snapshot

The remainder records the earlier state before the later executions above;
its statements that particular jobs are unexecuted are historical.

This is a coverage ledger, not an extraction-model qualification receipt. The
eight rows are exactly `MODEL_COVERAGE` in
[`streaming_8x4_acceptance.py`](../../scripts/streaming_8x4_acceptance.py). Every
row remains incomplete. A passing point experiment cannot fill an unmeasured
row or define the full process corner envelope.

The current executed numerical evidence is five manual FasterCap meshes of the
historical uniform U geometry and eight independent Cartesian finite-volume
references. The U's last two complete matrix changes are 0.693% and 0.272%.
The independent uniform reference's mesh/domain changes are below 0.5% for
widths 0.16 and 0.32 µm. The ten new native width/length/ground-extension cases
have not yet executed, so the uniform pilot has not passed its cross-solver
comparison or held-out gates.

| Mandatory field | Executed evidence and exact limit | Independent reference | Missing evidence / next bounded experiment |
| --- | --- | --- | --- |
| `resistance` | Exact merged ITF, draft RESOVER and retained LEF arithmetic reviewed for all five metals and MIN/TYP/MAX. Retained LEF sheet R equals MAX; TYP M2–4 draft rounding differs by about 0.0464%. No native R microextraction yet. | ITF sheet R × length / width is an independent arithmetic target for the synthetic wire controls, not an independent physical process measurement. | Frozen six-call consumer experiment covers every layer and two wider controls. Actual routed width/current-path census, corner semantics and the effective linewidth interpretation remain required. |
| `ground_capacitance` | Historical uniform U matrix passes warning, sign, energy and two-successive-mesh gates. No finite-wire length-slope comparison yet. | Eight uniform FVM runs cover two widths, two meshes and two grounded-box extents, with true residual ≤1e-9. | Complete the frozen ten-case native continuation, then actual layered M1 self C with third length and boundary extension. All other layers and final layout context remain open. |
| `coupling_capacitance` | No executed two-wire physical reference comparison in this campaign. U's ground/signal off-diagonal is not a lateral-wire qualification. | Planned independent multiconductor FVM: two separate unit excitations, full Maxwell matrix and cross-flux reciprocity. | Actual layered M1 lateral minimum spacing and held-out spacing, then all applicable adjacent-layer, diagonal and shielding contexts. Ground C and coupling C need separate error comparisons. |
| `via_resistance` | Exact ITF RPV and LEF cut/explicit-via inventory reviewed. All three draft VIARES stanzas are empty. Pinned consumer source predicts the LEF MAX fallback across corners; no Native readback yet. | Per-cut ITF RPV, plus an explicitly limited identical-independent-cut parallel arithmetic control. This does not validate spreading/contact physics. | Frozen consumer fixture measures Via1/2/3/TopVia1 and an explicit Via1 two-cut before/after an owned VIARES-only repair. Generated dbVia objects, all final design via names and process authority remain separate gaps. |
| `dielectric_interfaces` | Earlier coated-sphere interface exercise establishes a limited input/interface orientation seam; current executed U/reference are uniform 4.1 only. | Analytic layered planar capacitor and a new independent layered FVM operator are the proposed equation controls; coated sphere is a separate analytic geometry. | Real fox/nitride/oxide/passivation/air interfaces, layer ordering, material-side orientation, truncation/domain and mesh error. No claim that one sphere establishes mixed-layer wire accuracy. |
| `layer_coverage` | ITF/draft data cover five metal names; executed numerical wire experiment is only M1-like uniform geometry. LayerCount=5 is a table declaration. | Proposed M1 layered reference first; no completed adjacent-layer or TopMetal1 independent reference. | M1/substrate, every adjacent metal gap, upper-layer/passivation/air sensitivity and actual design-used layer/via census. |
| `width_spacing_range` | Source inventory: one nonempty drawn width per metal in draft rules; 16 empty width tables per corner. FVM widths 0.16/0.32 µm are stable; native held-out width has not run. | Held-out 0.32 µm has an independent uniform reference prepared and executed without tuning. | Native held-out comparison; minimum/larger spacing for lateral and vertical contexts; wide/power wires and consumer interpolation/extrapolation behavior over the final design's observed range. |
| `consumer_units_and_semantics` | Pinned OpenROAD source read; no six-call microfixture yet. Existing native matrix conversion explicitly scales coordinate units into F. | Exact synthetic series chains and strict SPEF OHM/KOHM, complete net membership and resistor graph readback; ITF targets constructed independently of OpenRCX. | Native wire/via corner readback, capacitance table-to-SPEF units/signs/ground-vs-coupling semantics, complete actual-net annotation, and all-corner STA tied to the exact model and final ODB. |

## Bound evidence paths

All generated paths below are relative to
`build/campaigns/8x4-20261022-01/`; these retained reports are evidence data,
not replacements for source-controlled protocols.

- `rc-manual-preparation-04/plan.json`, SHA256
  `2ae5d3b357b92677963eed5e27d4e847e3ffc896ab86f70c73ff5b861990f260`.
- `rc-native-outputs/rc-U-mesh-block-02/report.json`: all five native U jobs.
- `rc-independent-reference-01/report.json`: all eight independent uniform
  references, strict recomputed residuals and energy/flux controls.
- `rc-plan04-U-reference-independent-review/report.json`: independent raw-log
  readback and explicit missing-case gates; model qualification stays false.
- `rc-process-review-01.json`: data-only process audit. A later source revision
  adds cut bounding boxes and the explicit-rules repair contract; this historical
  audit remains unchanged.
- `rc-process-intake-01/manifest.json` and
  `rc-consumer-source-intake-01/manifest.json`: exact pinned primary-source
  bytes, SHA256/Git blob identities and URLs.
- `rc-consumer-preparation-02/plan.json`, SHA256
  `51a58576fe349c88b6900185db8c7134172564d1ffcda40e46595747e3c1378a`:
  unexecuted new consumer experiment. Its declared work budget is 210 seconds,
  six fresh 30-second calls, 1 CPU, 2 GiB including 128 MiB scratch. Shared PDK
  bytes stay read-only. Root GO is required before execution.
  Preparation/proposal 01 remain preserved, unexecuted and superseded: plan 02
  reconciles the protocol's exact seventeen net labels with fixture membership;
  tolerances, scope and resources are unchanged.

The final qualification packet must bind exact model, LEF, process stack,
consumer, report and corner-definition hashes. Each row needs complete declared
and executed case membership, a predeclared protocol and independent reference
hash, a stated relative tolerance and a measured maximum error within it. The
current evidence does not satisfy those conditions. Neither nominal routed STA
nor a successful synthetic R repair can supply the missing capacitance envelope.


## Later executed evidence and terminal closeout

The distinct [synthetic far-row study](streaming-8x4-rc-cap-far-20261023.md)
executed all four fixed calls after independent review. Raw measurement controls pass, while the candidate development gate fails its predeclared larger-gap coupling comparison.
It changes only one regular M1 table count and appends the declared finite
endpoint; all original rows remain intact. Only isolated .16um FVM trains the
coefficient. The .36um held-out consumer coupling actually fails the
unchanged 10% numerical gate by 18.8569–18.8572% and remains untuned. The fitted training result and the stable but clamped wider-width result close
no mandatory coverage field. Frozen independent readback SHA256 is
`bfc10aaacb56a4f6ae89aa6b5367b4faf51678c3928a4b89a05ab7bec8042051`;
full accuracy remains unmeasured and model qualification false.

The supplementary five-layer consumer C packet was separately HOST-prepared
and independently reviewed: two calls, all five isolated self cases plus four
centered adjacent-layer pairs, 39 nets/78 ports per call, retained TYP table/v1
and default widths. Plan SHA256 is
`886670431c23b57f77d4251b8fedc985628a44c4efcd598f84503cbb27db34d2`.
That preparation checkpoint preceded the actual failed results below. Its frozen provisional comparison requires
the actual complete passing reference-only32 authority at exact plan
`bd24cf673c33be53a2a83a1d4c27d3c14ea989208cfb8689a09d861baec69e32`,
plus unchanged full FVM25 raw/custody controls. Absent or failed references stay
unmeasured/blocked, with their failure evidence visible. Full finite-BEM
accuracy, model and timing qualification remain false. See the
[prepared consumer protocol](streaming-8x4-rc-cap-all-layers-proposal-20261023.md).


Actual [supplementary five-layer C](streaming-8x4-rc-cap-all-layers-results-20261023.md)
now failed both fixed calls despite OpenROAD exit zero: every one of four
centered adjacent-layer pair families has only printed-zero coupling at all
three lengths in both spacing fixtures. Exact geometry/default widths and units
match; no valid pair matrix or numerical accuracy is promoted. Frozen raw
readback SHA256 is
`834764b8725748294ce22792bfa596fa487062112d3f7d95f7549e8d0bd932e3`.
The supplied complete original32 authority also fails three domain gates
(Top self 5.05555%, M3/M4 pair 2.50265%, M4/Top pair 6.42107%), so provisional
comparison is explicitly blocked. A separately typed fresh E32/64 full32
experiment then ran with the bound domain/node-admission kernel, 70k structural
storage admission, unchanged numerical/2% gates and an observed 1800s work guard.
It passed 27 strict grids but timed out at its 120s leaf clock on global 027
(M3/M4 pair, .02um, E64um); the final four grids were not run. Observed work
was 1017.972s, with no OOM or memory preemption. Independent readback SHA256
`f7061991c8aea61b5de02867bd7f5bee1b2dd26cfc0184fed0e4ce94f5490ae2`
preserves its incomplete/failed status and clean source/resource closure.
No complete expanded reference or consumer accuracy authority exists.

The separately typed [five-grid completion proposal](streaming-8x4-rc-reference-completion-20261023.md)
predeclares fresh globals 027–031 at 180s per leaf under 1050s work/1110s outer.
A new HOST composite must reopen the exact old 27 successful observations plus
all five fresh observations before the unchanged complete32 empirical analysis.
The old failed 027 and failed packet remain visible. The independently reviewed
completion packet never launched before the numerical-start cutoff and closes
no coverage field. It requires a separately authorized future campaign.

The [one-token marker experiment](streaming-8x4-rc-cap-marker-20261023.md) tested
whether the v1 centered-pair path selects the draft M1→M2 zero-distance fringe
row. Its synthetic 1pF/m prediction and retained-zero strict failure were frozen
before measurement. The actual marker yields 2pF/m on both length intervals,
so the quantitative prediction fails by 100%; the original retained zero failure
is preserved. The intervention shows row influence. A subsequent pinned-source
audit supports two empty-side callbacks accumulating into a single merged CC
segment; the SPEF reader does not double mirrored copies. This explanation
cannot retrospectively pass the prediction or establish a physical coefficient,
generation provenance or model accuracy. Frozen marker readback SHA256 is
`633725e5669b788df4200af45db46c183f1b8c008136e7291308357f533bf59d`;
postmeasurement source/numeric audit SHA256 is
`f39cbc691e2c0dda98092a392c78a16c6cb04165d8434dab8e52228d978607a7`.
The precise origin of the draft zero endpoint remains unproven.
