# Pinwheel 8×4 qualified timing intake

**Open.** Apply this checklist to the frozen SG13CMOS5L candidate
`tt_um_pinwheel_streaming_ready_d2` from the [November 4 rehearsal](streaming-8x4-tt-rehearsal-20261104.md).
Its post-fill ODB is `b7e60eded5198fc53df7e5dd1e3ab0f5162720516ab0c1692a1cf7c7bb62602b`
and its GDS is `041ff30708e46be33db330e2f1dcafab889824b689499e931ec9d180a11c1689`.
Model admission and a qualified timing pass require separate receipts.

## 1. Admit the parasitics source

- [ ] Obtain an extraction authority accepted for the intended SG13CMOS5L
  signoff scope. Record its issuer, revision, process option, applicability
  statement, limits, and approval. Use either a qualified extractor and
  deck, with one exact ruleset per required RC corner, or SPEFs produced by
  an accepted extractor for this exact layout, with the extraction receipt
  and naming map. Identify the authority for the underlying model and the
  authority accepting its use for this candidate.
- [ ] Seal an input manifest with a relative path or immutable reference,
  SHA-256, byte count and role for each artifact. Bind the ODB/GDS, canonical
  DEF, logical and powered Verilog, technology and cell LEFs, exact PDK
  release, source constraints and all Liberty files. Identify the extractor
  and STA runtime by version and binary or image digest. Record the
  commands, options, warnings, exits and raw reports. Supplied SPEFs also
  need provenance linking their source layout to the frozen candidate and
  matching each extracted net and pin to the STA design.
- [ ] Verify that the authority covers the actual routed geometry and its
  electrical context. Inventory signal, clock and applicable special-net
  geometry, used widths, spacings, vias and cut arrays, routing ends and
  branches, layer pairs, fill, shields, substrate, and pin and cell context.
  Include any upper-metal field effects relevant to the model. List each
  exclusion with its physical basis, validity range and signoff impact.
  An unsupported context that can affect a checked path leaves admission
  open.
- [ ] Keep physical accuracy and software transport evidence separate.
  For a foundry- or provider-qualified deck, retain its qualification
  statement and independently reopen its release, options and layout
  applicability. For an in-house or otherwise unqualified model, require
  physical references independent of the candidate tables, importer and
  fitting data. Freeze the candidate geometry, query membership and
  untouched tests before fitting. Reopen the raw evidence for resistance,
  ground and coupling capacitance, vias, dielectrics, layers, width and
  spacing range, and actual consumer units and semantics. The earlier
  f516 study specifies the [oracle contract and empirical criteria](streaming-8x4-golden-reference-request-20261026.md).
  Establish the criteria's applicability on b7e60 and retain the
  historical measurements under their original target.
- [ ] Seal the required scenario matrix before launching STA. Each row
  identifies the RC corner and ruleset or SPEF, Liberty files and operating
  conditions, mode and SDC, and the check purposes. Give the process or
  integration authority for each RC/Liberty pairing and show that the set
  bounds the required setup, hold and electrical checks. A single nominal
  extraction reused with several Liberty corners remains diagnostic.

## 2. Run and independently reopen timing

- [ ] Agree on the integration contract for clock frequency, duty cycle,
  latency and uncertainty, min/max I/O timing, drives and loads, reset,
  enable and bidirectional I/O. Give every timing exception an explicit
  mode, endpoint scope and source. The rehearsal used a 20 ns clock,
  0.200 ns minimum input delay and 0.200 ns uncertainty. Verify those
  assumptions against the integration source, particularly for Host MOSI 1
  on `ui_in[5]`. Keep `clock_hz: 0` until a frequency is qualified.
- [ ] Run one bounded extraction and propagated-clock STA on the frozen
  design, or STA using the admitted external SPEFs. Pin the exact
  extraction and analysis options, including the coupling treatment and
  via handling. Verify each SPEF's units and name map, connected
  resistance graphs, ground and coupling conventions, and matching net
  and terminal membership. Reopen the raw annotation reports per scenario.
  Require annotation of all relevant data, clock and control paths, and
  account individually for unannotated or unconstrained objects. Retain the
  coverage and exclusion lists with the receipt. If clock summary flags
  disagree with endpoint clock paths, query and record the effective clock
  state in the analysis engine. Stop on missing scenarios, unexpected tool
  errors, unresolved warnings, annotation gaps, input drift or fallback to
  estimated parasitics.
- [ ] For every applicable scenario, require nonnegative setup and hold
  slack, zero TNS and zero violating endpoints, and passing slew,
  capacitance, fanout, recovery/removal and pulse-width checks. Any
  approved exception must be independently reviewable and scoped to its
  scenario and endpoints. Seal the raw path, clock, annotation and
  electrical reports with a readback that independently rederives the
  outcome. The historical campaign reserves a typed G2 admission
  endpoint and currently blocks qualified timing and ECO through its
  [policy](../../scripts/streaming_8x4_closure48_policy.py#L40).

## Local work before model admission

Audit the constraints, build the exact annotation/exception inventory,
and prepare a reader for the two intake paths. The legacy nominal
diagnostic reports `ui_in[5]` to `engine.frontend._0230_/D` at −24.696 ps
fast and −7.519 ps typical. Reopen that min path with the admitted model
before sizing a hold ECO. Reducing frequency does not remove a same-edge
hold violation. [Frozen endpoint and load audit](streaming-8x4-e982-timing-audit-20261104.md) ·
[Legacy model scope](streaming-tt-extraction-scope.md)

The sealed DEF and pinned standard-cell Liberty independently explain five
fanout violations. The route configuration targets ten, while Liberty
sets a maximum of eight and counts each antenna input as one load.

| Net | Functional sinks | Antenna inputs | Total |
| --- | ---: | ---: | ---: |
| `net2157` | 8 | 4 | 12 |
| `net2298` | 8 | 2 | 10 |
| `net11223` | 4 | 5 | 9 |
| `net2333` | 8 | 1 | 9 |
| `net840` | 6 | 3 | 9 |

Plan the smallest correction that respects the eight-load rule and
preserves antenna protection, including the fixed geometry on `net840`.
Any adopted physical change creates a new candidate. Rebind model
applicability, rerun extraction and STA, and refresh the affected route,
DRC, antenna, LVS, digital correspondence and precheck evidence before
assembling a new package. Shuttle admission remains a separate decision.

## Software preflight

The [local reader](../../scripts/streaming_8x4_e982_parasitics_preflight.py)
reopens a reviewed request against the exact rehearsal ODB, GDS, logical
netlist and exported inventory. Use workspace-relative regular-file
bindings with `path` and `sha256` keys. The request has schema
`pinwheel.e982-parasitics-preflight-request.v1`, a `target` object keyed
by `odb`, `gds`, `netlist` and `inventory`, and a `scenarios` object
keyed by the reviewed scenario labels. Each scenario provides
`rc_corner`, `sta_corner`, `mode`, bindings for `sdc`, `spef`,
`annotation` and `run`, and an ordered `liberties` list of bindings.

The `run` receipt uses schema `pinwheel.e982-spef-annotation-run.v1`.
It records `top`, `scenario`, both corner names, `mode`, digests for
the target ODB/GDS/netlist and the SDC, SPEF, annotation report and runtime
as `<role>_sha256`, plus the ordered `liberty_sha256` list. It records
`annotation_mode` as `read_spef` and the observed `exit_code`. Supply the
native report with its OpenSTA corner markers and raw
`report_parasitic_annotation -report_unannotated` section.

```sh
python3 -B scripts/streaming_8x4_e982_parasitics_preflight.py request.json \
  --request-sha256 "$reviewed_request_sha256"
```

The reader supports scalar detailed-net SPEF with explicit `PIN_CAP NONE`,
resolves name maps and OpenRCX escaped hierarchy, checks consumed-net and
terminal coverage, validates resistance connectivity and capacitor
references, and reconciles reported annotation gaps with the ODB inventory.
It rejects identical extracted graph digests presented as different RC
corners. A software pass applies to the supplied scenario matrix.
Physical model authority, completeness of the signoff scenario matrix,
and qualified timing remain separate decisions.
