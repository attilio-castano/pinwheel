# Pinwheel 8×4 qualified timing intake

**Open.** Qualify the exact five-net SG13CMOS5L ECO of
`tt_um_pinwheel_streaming_ready_d2`. The 8×4 outline is
1,724.16 × 710.64 µm. The router reported zero DRC markers. The ECO
passed main DRC, supplemental enclosure, foundry antenna, transistor
LVS, geometric rail connectivity, digital correspondence and the
nine pinned Tiny Tapeout checks. The Tiny Tapeout rehearsal used support revision
`d66cf179e7bc4d296362ab7e2e3b344dc3c4f665`. Model admission, qualified
timing and shuttle acceptance each require their own receipt.
[Exact ECO evidence](streaming-8x4-e982-fanout-trial-20261104.md)

| Exact ECO input | SHA-256 |
| --- | --- |
| Routed ODB | `e40e40804ddf5c4093f83710ec27b0a5b975f3a047e5c95810e175fbe6aa78f9` |
| Streamed GDS | `dcc496d71202677f6d2fe3785dca6ff9bb225ef954953bf7925171174d4b7e82` |
| DEF | `fbccaa1f145b74050eb5ff257db80cbdd9a3a1b56a530ab27a2d6ba9ad6d23ff` |
| Logical Verilog | `3167eaaed4365ffc373f9a8609172eeebca48f792134d84a19f259e5f16951ec` |
| Powered Verilog | `d3780db1d817252cefe22a401e7712a7939236879ed47a0e2c3653c7a0f97401` |
| Canonical LEF | `d4764da20d86bcd919b03e6926f06fa13246491800eae2fda1ea5a44b53bdc20` |
| Exported ODB inventory | `af31d89940af5af559d2a8fceb5c0767887faa952298a0e7b684b8ee91658ee8` |
| Local precheck readback | `dd3507c40f5e72f643c8f26a866f57e8d05fc83acb9f4bd5d911ff436bbce1ed` |

## Provider inputs

TTIHP27a is the proposed shuttle. Allocation, run-specific
custom-GDS acceptance and extraction authority remain open.
[Prospective custom-GDS interface](../../.github/workflows/tt-rehearsal.yml)

| Owner | Requested deliverable |
| --- | --- |
| Tiny Tapeout allocation | Written confirmation that an independent project can reserve a contiguous 8×4 allocation on TTIHP27a, with availability, reservation procedure and the reservation and artifact deadlines. |
| Tiny Tapeout integration | The accepted custom-GDS upload path, mandatory artifact set, exact PDK, support, workflow and checker revisions, required check or waiver evidence, and the run-specific receipt that would confirm acceptance of the selected GDS. The local workflow's custom-GDS reference is a proposed interface. |
| Tiny Tapeout timing | A mux and board I/O contract or versioned SDC covering supported modes and clock period, duty cycle, edge, latency and uncertainty. Supply min/max input and output timing, drive or slew, and load per relevant port, with reset, enable, bidirectional direction changes and exception scope. Include the host path through `ui_in[5]`. |
| Tiny Tapeout power | Parent VPWR/VGND contact geometry and reference plane, voltage and temperature limits, allowed current and the applicable package or board impedance model. Identify any required local voltage, current-density or activity limits. |
| IHP or an accepted extraction provider | An approved SG13CMOS5L deck and extractor release with exact options, coverage and RC-to-Liberty pairing authority, or an exact-ECO extraction service returning the required corner SPEFs, naming map, commands, raw logs, source-layout identity and applicability statement. |

The minimum timing response is an applicable corner matrix and its
authority. Ask for each row's mode, SDC, RC corner and exact deck or SPEF,
Liberty releases and operating conditions, check purposes, and the
source justifying the pairing. The matrix must cover setup, hold and
the applicable electrical checks including slew, capacitance, fanout,
recovery/removal and pulse width. The provider can use multiple rows
for any check or cover multiple checks with one row.

If a supported deck or service is unavailable, request an independent
reference packet with stack geometry and physical tolerances, calibrated
wire and via resistance, ground and coupling capacitance, applicable
width, spacing and layer context, and consumer units and conventions.
Include raw calibration patterns, extracted results and reproducible
commands. The in-house admission route also needs untouched validation
cases and an authority that accepts its use for this candidate.
[Reference request](streaming-8x4-golden-reference-request-20261026.md)

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
  Establish the criteria's applicability on the exact ECO and retain the
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

## Frozen baseline and local work before model admission

The November 4 baseline rehearsal remains bound to post-fill ODB
`b7e60eded5198fc53df7e5dd1e3ab0f5162720516ab0c1692a1cf7c7bb62602b`
and GDS `041ff30708e46be33db330e2f1dcafab889824b689499e931ec9d180a11c1689`.
[Baseline rehearsal](streaming-8x4-tt-rehearsal-20261104.md)

Audit the constraints, build the exact annotation/exception inventory,
and prepare the ECO binding for the software reader. The baseline
diagnostic used one inherited seven-layer nominal SPEF at three
Liberty corners. Its `ui_in[5]` to `engine.frontend._0230_/D` path
had hold slack of −24.696 ps fast and −7.519 ps typical. Reopen the
path and the full min-path census on the ECO under the admitted model
and integration constraints before sizing a hold repair. Evaluate
same-edge hold from the launch and capture relationship at that edge,
independently of the cycle-period target.
[Frozen endpoint and load audit](streaming-8x4-e982-timing-audit-20261104.md) ·
[Legacy model scope](streaming-tt-extraction-scope.md)

The baseline's sealed DEF and pinned standard-cell Liberty explain
five fanout violations. The route configuration targets ten, while
Liberty sets a maximum of eight and counts each antenna input as one
load.

| Net | Functional sinks | Antenna inputs | Total |
| --- | ---: | ---: | ---: |
| `net2157` | 8 | 4 | 12 |
| `net2298` | 8 | 2 | 10 |
| `net11223` | 4 | 5 | 9 |
| `net2333` | 8 | 1 | 9 |
| `net840` | 6 | 3 | 9 |

The ECO removed all five observed fanout violations while retaining
the two `net840` antenna bridges. Its 19 collateral signal-route
changes and five decap replacements remain part of the release review.
The geometric rail check and local decap inventory leave electrical
power qualification open. Any later physical change requires new
target identities, applicable extraction and STA, and refreshed
affected checks before a package is assembled.
[ECO scope and power evidence](streaming-8x4-e982-fanout-trial-20261104.md)

## Software preflight

Use `--target eco` to select the exact ECO ODB, GDS, logical Verilog
and exported inventory listed above. The default `--target baseline`
keeps the original rehearsal bindings. Each target requires matching
hashes in the request and the corresponding native analysis receipts.
[Local reader](../../scripts/streaming_8x4_e982_parasitics_preflight.py)

Use workspace-relative regular-file bindings with `path` and `sha256`
keys. The request has schema
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
  --target eco --request-sha256 "$reviewed_request_sha256"
```

The reader supports scalar detailed-net SPEF with explicit `PIN_CAP NONE`,
resolves name maps and OpenRCX escaped hierarchy, checks consumed-net and
terminal coverage, validates resistance connectivity and capacitor
references, and reconciles reported annotation gaps with the ODB inventory.
It rejects identical extracted graph digests presented as different RC
corners. A software pass applies to the supplied scenario matrix.
Physical model authority, completeness of the signoff scenario matrix,
and qualified timing remain separate decisions.
