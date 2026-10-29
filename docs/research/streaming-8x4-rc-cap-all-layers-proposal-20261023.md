# Supplementary five-layer consumer capacitance proposal

Root approved the proposal below for a separate HOST implementation. The
checkpoint at the end records its frozen preparation; no Native consumer
measurement is claimed at that checkpoint. It is a distinct supplementary
consumer diagnostic. The original gated all-layer BEM authority remains
unexecuted and its admission rules remain intact.

The useful next consumer measurement is **two fixed TYP calls**, each containing
five isolated wires and four centered adjacent-layer pairs at 50/100/150 um
lengths. The calls differ only in 512/1024 um separation between fixture groups.
Each contains nine cases, 27 groups, 39 nets and 78 ports, with no cells, ITerms or
routed vias. Every wire uses its actual LEF default width, so no NDR is needed.

| Metal | Drawn width, um | Process bottom–top, um |
| --- | ---: | ---: |
| Metal1 | .16 | 1.040–1.460 |
| Metal2 | .20 | 2.000–2.490 |
| Metal3 | .20 | 3.030–3.520 |
| Metal4 | .20 | 4.060–4.550 |
| TopMetal1 | 1.64 | 5.400–7.400 |

The four pairs are Metal1–Metal2, Metal2–Metal3, Metal3–Metal4 and
Metal4–TopMetal1. Their transverse centerlines coincide exactly, while the two
conductors retain their distinct metal layers and physical heights. The full
TYP dielectric/passivation/air stack is the same process-derived stack used by
the independent FVM cases. Reference transverse x maps to DEF y relative to
each group center; extrusion maps to DEF x. DBU is 1000/um and all coordinates
are integral. Actual before/after readback must check every pin, route, layer,
endpoint, width, outline and exact group membership.

The table is the unchanged retained C1 TYP table, SHA256
`bf2af2235b102d7bb58fe782d8d8b41a64cb3efde46593562314a499e9c4a612`.
The fitted far-row candidate is excluded. No fitting occurs. Extractor options
remain v1.0, coupling threshold 0, cc_model 10, context_depth 5, no via merging,
and neither LEF resistance nor LEF RC overrides. This isolates new layer/context
coverage from version and coefficient changes.

The source contains regular OVER/UNDER and OVERUNDER tables and dispatches,
but data presence is not applicability or accuracy evidence. In particular,
vertical pair coupling must actually appear and reconcile. The reader should
reuse the frozen C1 strict actual C_UNIT and PIN_CAP_NONE conventions, full
CAP-to-Maxwell reconstruction, positive ground, mirrored coupling identity,
single global counting and every full incident D_NET total. Missing intended
coupling or coupling to an unintended fixture group must fail. No pin loads
are admitted.

The complete matrix and every ground row participate in both length slopes.
Keep 5% consecutive-slope and 2% fixture-isolation gates; this spacing control
is not a physical ground-boundary experiment. A separately named provisional
comparison can use 10% across every matrix/ground cell only after actual raw
reference evidence passes all empirical and custody gates. Printing intervals
must be retained, not used to absorb physical disagreement. All warnings are
fatal; all fixed calls and failures remain visible without prefix promotion,
adaptive retries, coefficient changes or fallback policy.

The existing M1 reference04 provides the isolated M1 target. The proposed new
reference-only32 authority supplies four grids for each of the eight upper-layer
self/centered-pair cases. Its exact new plan, reader and executed closeout hashes
must be pinned before consumer preparation. The eight old physical cases are
bound by original all-layer plan
`37628d053afaf9fd2987bcd7917873cabec76932a9fa4597c190e65391c43f12`;
that hash supplies geometry/operator provenance, not permission to execute its
historical gated BEM plan.

Without a complete passing reference32 packet, provisional numerical accuracy
stays unmeasured. Even with stable reference32 and a passing consumer comparison,
full accuracy remains unmeasured until a separately typed complete finite BEM
policy actually passes. The known retained M1 isolated discrepancy must remain
a failure if repeated. Five nominal widths and four centered adjacent pairs
cannot qualify ranges, corners, nonadjacent/offset/orthogonal/diagonal contexts,
multiconductor shielding, finite ends, or the final design's actual routed
width/via/context envelope.

Proposed resources are two 30 s leaves, 90 s work and 120 s outer, one CPU, 2GiB
including 128MiB scratch, no extra swap and 128 PIDs. The offline pinned image,
read-only inputs/sources, owned fresh output, shared campaign lock and exact
wrapper/guard/cleanup/input-seal joins remain mandatory. Root approval of this
concrete scope precedes implementation; Root alone would admit Native after
independent review and commit.

The immutable HOST proposal is
`build/campaigns/8x4-20261022-01/rc-cap-all-layers-proposal-01.json`, SHA256
`efb7664565d43a934c3b2b71e21a7dd189652ea5a7f71064174e8fce7b103884`.
Its reference32 execution-plan hash is deliberately unset and mandatory before
preparation. It confers no execution or accuracy authority.

## HOST implementation checkpoint

Root approved implementation. The new, separately typed family is
`scripts/streaming_8x4_rc_cap_all_layers.py`, `_geometry.py` and `_readback.py`.
The fixed two-call worker preserves C1's process/copy/raw/failure control flow,
with only its receipt schema, call count and bounded work guard adapted. The
strict SPEF parser and full matrix length arithmetic reuse the frozen C1 code.
Tcl differs only by adding actual observations of all five default widths.
No Native consumer call has run at this checkpoint.

The frozen reference-only32 preparation is now explicitly pinned:
`bd24cf673c33be53a2a83a1d4c27d3c14ea989208cfb8689a09d861baec69e32`.
The consumer preparation copies and reopens it plus complete original FVM25
raw/custody controls. This verifies physical/operator/reference provenance;
it does not assume that the new 32 execution passes. The optional comparison
reader invokes `closed_authority` on the actual complete 32 readback, rederives
its raw/mesh/domain/resource gates, checks the exact new plan identity, and
reopens FVM25 before selecting any fine target. An absent authority yields
unmeasured; a failed or incomplete authority yields blocked reference evidence
with its exact path/hash and error. No partial or failed reference can confer
provisional comparison authority.

Under `build/campaigns/8x4-20261022-01/`:

- `rc-cap-all-layers-preparation-01/plan.json`: SHA256
  `886670431c23b57f77d4251b8fedc985628a44c4efcd598f84503cbb27db34d2`.
- `rc-cap-all-layers-command-proposal-01.json`: SHA256
  `a222d30199985388fe759412780322d8ca675ea1462e5431acef9ce7dee833a8`.
- `rc-cap-all-layers-host-readiness-01.json`: SHA256
  `dbb4854bb1b63ae4aa39f117da939ef1a358bb328fcce34ac80979a09b6d6f38`.

All 33 transitive source hashes are bound. Twelve focused HOST controls pass
normal and optimized Python: exact 39-net/78-port geometry, actual writer syntax,
centered different-layer pairs, complete physical width/height/stack joins,
full 39-net CAP grouping, strict warnings/units/inventory, immutable extraction
options, matrix membership, slope/isolation failure, blocked reference failure,
all-cell numerical mismatch and unchanged worker control flow. These are HOST
controls, not Native or field-solver results. Independent review precedes Root
commit/Native. Full accuracy stays unmeasured and finite BEM, model and timing
qualification remain false in every consumer/provisional result.

The Root launcher uses the command proposal's exact `argv`, `container_name`,
`timeout_seconds=120`, absolute `plan_path`, `plan_sha256` and all 33 entries
of `producer_sha256`. It must seal those files through the campaign wrapper
with kind `solver`, the shared heavy lock/sentinel and exact wrapper/guard
identity. The result owner is `rc-native-outputs/rc-cap-all-layers-01`.

After the actual consumer terminal, HOST measurement-only reopening is:

```sh
python3 -B scripts/streaming_8x4_rc_cap_all_layers_readback.py \
  --inputs build/campaigns/8x4-20261022-01/rc-cap-all-layers-preparation-01 \
  --plan-sha256 886670431c23b57f77d4251b8fedc985628a44c4efcd598f84503cbb27db34d2 \
  --directory build/campaigns/8x4-20261022-01/rc-native-outputs/rc-cap-all-layers-01 \
  --resource-report build/streaming-tt-resources/8x4-rc-cap-all-layers-01/report.json \
  --command-proposal build/campaigns/8x4-20261022-01/rc-cap-all-layers-command-proposal-01.json \
  --output build/campaigns/8x4-20261022-01/rc-cap-all-layers-independent-readback-01.json
```

A distinct fresh HOST result may add `--reference32-authority` naming the actual
complete independent 32 readback when it exists. The reader keeps measurement,
reference prerequisite and provisional numerical-comparison states separate;
its full accuracy status stays unmeasured even if every provisional cell passes.


Root subsequently executed both calls. Both retain strict zero-intended-coupling
failures and the actual original32 reference comparison is blocked. Read the
[executed failure inventory](streaming-8x4-rc-cap-all-layers-results-20261023.md);
the historical HOST checkpoint above confers no numerical accuracy pass.
