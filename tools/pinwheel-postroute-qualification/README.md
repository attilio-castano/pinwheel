# Isolated qualification of a frozen routed checkpoint

These helpers stage and explicitly launch separate native verification jobs. No
CAD is launched by imports, `prepare.py`, `build_spec()` or `--prepare-only`.
Only the root campaign owner should launch `run.py`; it uses the campaign runner
and shared heavy lock. It never invokes Classic.start, fill insertion, routing,
placement, resizing, CTS, antenna repair or PG repair.

The available phases are `rcx-sta`, `streamout`, `lef-lvs`, `gds-lvs` and `drc`.
They are independent jobs with fresh State/metrics. `lef-lvs`, `gds-lvs` and `drc`
require a passed same-checkpoint `streamout` producer via `--prior`.

## Preparation

First bind a completed accepted control or selected candidate. `bind.py` checks
the producer's passed status, source custody, container absence, deadlines,
per-file after hashes and root's `stage_execution_and_scope_gate_passed`
adjudication. It records that receipt and adjudication as immutable inputs.
It does not require zero DRC and does not assert physical acceptance.

Replace `ACCEPTED_AFTER`, `ROUTE_REPORT` and `ADJUDICATION` below with completed
producer paths. This is host preparation only:

```sh
python3 -B tools/pinwheel-postroute-qualification/bind.py \
  --after ACCEPTED_AFTER --route-receipt ROUTE_REPORT --adjudication ADJUDICATION \
  --core-config build/physical/tt-buffered-locality-repair-02/core.json \
  --sdc build/physical/tt-p2-drt-onepass-route-01/core.sdc \
  --out build/physical/tt-overnight-qualification-plan-01/accepted-bindings-01.json
```

The JSON stdout supplies the full `prepare_flags` list for that completed
`after/` directory. Use them with the campaign arguments below. The source
binding cannot mix ODB/DEF from different producers. All campaign
protected/reference files and local PDK assets are also frozen. The original
core configuration SHA is
`5697ff68df9e82adec1572acb842e844d85c17868250df62e271bd4f42caeb06`;
its dependency root is `build/physical/tt-buffered-locality-repair-02/`, and its
SDC SHA is `860a5afd856cc92bbecc838b147a9f7c8259abd66bcd62c0f211cb7e8edc4db1`.
Its `dir::` files are staged from that root without running its physical flow.

```sh
python3 -B tools/pinwheel-postroute-qualification/prepare.py \
  --campaign build/physical/tt-overnight-campaign-20261015/manifest.json \
  --campaign-id tt-overnight-20261015-000717 \
  --heavy-lock build/physical/tt-overnight-campaign-20261015/heavy.lock \
  --source-bindings build/physical/tt-overnight-qualification-plan-01/accepted-bindings-01.json \
  --odb ACCEPTED_AFTER/checkpoint.odb \
  --def ACCEPTED_AFTER/checkpoint.def \
  --inventory ACCEPTED_AFTER/native-inventory.json \
  --master-obs ACCEPTED_AFTER/master-OBS-signature.json \
  --via-definitions ACCEPTED_AFTER/via-definitions.json \
  --core-config build/physical/tt-buffered-locality-repair-02/core.json \
  --sdc build/physical/tt-p2-drt-onepass-route-01/core.sdc \
  --native-binary-sha256 6ba87b45c762ee8c9670375c204cd03d801a6da98cd6e056a1c73027aad68a7c \
  --out build/physical/tt-overnight-qualification-plan-01/prepared-01
```

`prepared-01` is immutable after preparation. Actual copied helpers, native
capability/script capture and campaign runner are frozen in `staged_sha256`.
Origin tool paths/hashes are provenance metadata; repairing a live helper later
does not invalidate this package. Create a new package for a repair. Launch the
**copied** `prepared-01/run.py`, which loads the copied campaign runner, rather
than the live source entry point. The source and staged inputs are recustodied
by each job, including all 507 protected and seven reference campaign files.

## Root-owned bounded launch

```sh
python3 -B build/physical/tt-overnight-qualification-plan-01/prepared-01/run.py \
  --prepared build/physical/tt-overnight-qualification-plan-01/prepared-01/prepared.json \
  --phase rcx-sta --native-seconds 1200 --minimum-native-seconds 60 \
  --out build/physical/tt-overnight-qualification-plan-01/baseline-rcx-sta-01
```

Add `--prepare-only` to stage this job without Docker. Its output directory then
remains a staged artifact and must not be overwritten. Choose another fresh
output directory for an actual launch. The Python API is
`build_spec(prepared_path, phase=..., output_dir=..., native_seconds=...,
minimum_native_seconds=..., prior=...)`, followed by `run_owned_job(spec)` from
the copied runner. `build_spec` rejects helper versions differing from the
package. Root must honor the shared lock and `controller_must_stop` receipt.

Each job is at most 5,400 seconds **including** the 45-second cleanup/recustody
reserve. Native work is clipped to the campaign hard stop minus its configured
closeout hour. CPU4, 6 GiB, no network, no image pull. Absolute runtime limits
come from the current campaign manifest, never a hard-coded old timestamp.

## What the phases establish

`rcx-sta` first loads the ODB in the pinned native OpenROAD binary, verifies the
complete inventory/master geometry/vias and token-exact DEF including TAPER,
then exports unpowered and powered netlists without changing the design. Actual
OpenROAD.RCX reads the detailed DEF and writes SPEF. The parser requires every
consumed net and terminal, finite nonnegative parasitics, RC records and
resistor-network reachability. These are extracted-network checks, not an
independent geometric-connectivity or LVS proof. STAPostPNR then reads that
fresh SPEF/netlist for each of three Liberty corners, sequentially, with empty
metrics; it requires no consumed/partial/unresolved unannotated drivers and a
single propagated 20 ns clock. All setup/hold/DRV metrics and native reports
remain visible even if physical timing fails.

The RC model is one nominal SG13G2 seven-layer model at index0; used M1–M4 map to
their matching native indices. Physical CMOS5L-stack accuracy remains qualified
as unresolved, as do independent min/max RC corners. FAST uses -40 C logic and
-55 C SRAM. Neither qualification is silently converted into signoff accuracy.

`streamout` runs KLayout.StreamOut directly and exports the frozen unfilled
design. `lef-lvs` uses actual DEF/LEF extraction with cell abstractions;
`gds-lvs` extracts actual streamed GDS with an explicit 345-port SRAM boundary
model. Both use native Magic+Netgen and retain reports. An empty, exactly
declared SRAM boundary model is deliberate and does not prove internal SRAM
devices. Native reference/extraction port-order agreement, unreported blackbox
absence and meaningful removed-terminal/bridge native negative controls still
require qualification before any full-boundary connectivity pass. No automatic
LVS acceptance is emitted. Host tests prove the naming map rejects missing
ports, duplicate/aliased ports and rail merging.

`drc` runs the public CMOS5L KLayout deck with recommended rules enabled. DRC,
antenna, native layout connectivity, internal SRAM qualification, fill/density
and the exact official Tiny Tapeout precheck are separate gates. No phase
claims official precheck; its support commit, dependency versions and PDK must
be bound separately. Current image and official Python KLayout versions differ.
All process-success receipts explicitly leave physical acceptance false.

## Host checks

```sh
python3 -B -m unittest discover -s tools/pinwheel-postroute-qualification/tests -v
```

These use no CAD/Docker. Retained P2 SPEF was also parsed against the actual
native inventory: 28,948 consumed networks and 90,759 contacts, with no missing
network/connection/RC-graph issue. That input used estimated global-route RC;
the observation qualifies parser format support only, not post-DRT extraction.

## Check-only antenna diagnostic: maintained v3 flow

Use `antenna_host_v3.py`, `antenna_coordinator_v3.py` and
`antenna_results_v3.py` for new jobs. The older `antenna_host_v2.py` and
`antenna_coordinator_v2.py` are historical and unadmitted entrypoints: the native
checker does not emit the ANT metric keys that coordinator v2 required. Keep
those files and historical snapshots unchanged. `antenna_native_v2.py` remains
the unchanged, qualified check-only native body; the version suffix is not its
admission status.

Start with an already prepared, completed routed source whose actual route
receipt and root scope adjudication pass. This host-only command rehashes its
whole producer and original prepared inputs, then creates a new immutable
capsule; it never starts Docker or native CAD:

```sh
python3 -B tools/pinwheel-postroute-qualification/antenna_host_v3.py \
  --prepared ACCEPTED_PREPARED/prepared.json \
  --out NEW_ANTENNA_STAGE
```

Only the root campaign owner executes the copied staged command:

```sh
python3 -B NEW_ANTENNA_STAGE/antenna_host_v3.py \
  --staged-root NEW_ANTENNA_STAGE --run
```

Omit `--run` to validate an existing capsule without CAD. Native work is capped
at 300 seconds, all-in at 360 seconds, with CPU4/6 GiB, no network and the
campaign's shared lock and absolute native cutoff. All original prepared hashes
remain exact. The stager accepts only the checker/export/inventory/audit body
identities qualified by the retained C14 antenna02 run; changed native bodies
need separate qualification. A running or nonexistent future checkpoint is
rejected before output creation. The root's independent whole-custody and
physical-scope gate remains mandatory for every selected source.

For a repeat of the **same ODB**, optionally add `--reference PASSED_ANTENNA_JOB`.
The reference producer and all its inputs/artifacts are rehashed, and the fresh
native counts and complete violation-set signature must agree. A different ODB
is rejected. A new checkpoint uses no reference and must be measured fresh;
the stager does not inherit C14's violation counts.

The finite reconciler requires complete native final counters, detailed
violated-net/pin sections, every INPUT-load section on those nets and actual
nonempty route/model denominators. Missing optional ANT metrics are recorded as
absent, never zero; partial or contradictory telemetry is rejected. Native
checker, exporter, API/metadata query and route-preservation bodies remain
unchanged. No guide generation, antenna repair or diode insertion is invoked.

The pinned native counter increments once per INPUT ITerm after checking all
its layers, so a pin with several violating ratios contributes **one** to
`ANT-0001`. The reconciler compares that footer to distinct net/pin contacts and
reports ratio events separately; their counts may differ. Native `(VIOLATED)`
flags may accompany equal displayed ratio/limit values because the engine
checks full precision but prints two decimal places. See
[pinned native counter and reporter](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/ant/src/AntennaChecker.cc#L796-L824).

The retained C14 antenna02 producer passed after repairing this telemetry
wrapper, with **124 violated nets and 135 violated INPUT pins**, identical to
the native diagnostic recovered from failed-wrapper antenna01. This is a
negative antenna diagnostic; wrapper success is not an antenna or chip pass.
The generic stager and stricter host reconciliation are host-tested, while
each new source still requires actual native execution and readback.
`antenna_pass_qualified` and `physical_acceptance_claim` remain false, including
for a numeric zero count. Foundry/process-model accuracy, physical connectivity,
SRAM interior and official Tiny Tapeout precheck remain separate gates.

Run the maintained antenna controls alone with:

```sh
python3 -B -m unittest discover \
  -s tools/pinwheel-postroute-qualification/tests -p 'test_antenna_*_v3.py' -v
```

The controls include retained actual C14 output when available, summary/body
and telemetry corruption, missing model/rule coverage, source/receipt/artifact
changes, stopped-versus-running admission, immutable-copy preservation and
host-only staging. They never launch CAD.

## Additional v5 LVS and PDK gates

Both LVS phases now require `--fixture-semantic-gate PATH` and
`--fixture-semantic-sha256 SHA256`. The independently reviewed native fixture
must retain the SRAM as an active 345-port blackbox and detect the declared
standard-cell, macro-signal and macro-power attachment faults. The launcher
rehashes the review, its passed owner-absent producer and all bound case
artifacts before creating a job. Fixture03's standard-cell-only result is
insufficient: Netgen removed its empty SRAM from the active comparison.

The frozen v5 LVS adapter used positional reference macro syntax. Native
fixture04 demonstrated that Netgen1.5.320 drops positional Verilog instances;
that LVS branch is unadmitted. Its RCX, streamout and public DRC branches remain
valid, and all historical snapshots and measurements remain unchanged.

The maintained v6 LVS adapter uses 345 explicit named scalar aliases, with a
bijective mapping to the original SRAM pin identities on both copied model
headers. It audits all 690 original reference macro contacts against the native
inventory. Only the two copied reference macro statements and the empty
extracted macro header spellings change; every physical extracted node and all
other reference text remain exact. A VSS-to-VPWR collapse remains a mismatch.
No internal SRAM conductive model is added. Native comparison must retain the
complete 28,970-instance master inventory. Both LVS launch phases require a
successful named-alias fixture07 and the independent bound semantic gate;
positive unique match, standard-cell fault sensitivity, macro signal attachment
faults and macro VSS attachment sensitivity are separate required observations.
A prepared helper is not an admitted LVS result.

`prepare.py` optionally accepts `--pdk-root PATH --pdk-overlay-manifest PATH`.
The supported overlay preserves every installed file and symlink and adds only
two missing public-deck JSON dependencies from the same pinned upstream PDK
commit. Preparation and launch validate its complete manifest; it is mounted
read-only. Installed PDK files, deck options and rule values are unchanged.

Prepared helper snapshots and historical native results remain immutable.
The current helper includes stronger admission than older v3/v4 snapshots;
neither a prepared package nor passing host tests establish a native LVS or
public-deck DRC pass. Use the root campaign's current queue and actual receipts
for execution status.
