# Same-final-target geometric power-grid connectivity

This new diagnostic is prepared for a separately authorized Native leaf. No
power-grid result has executed. It consumes only a closed final 8x4 views receipt
and its same-ODB canonical terminal inventory; a partial route or probe cannot
enter. All rail names and required instance/block terminals come from that
inventory. The original physical producers and candidate remain unchanged.

`scripts/streaming_8x4_power_grid.py` offers HOST `prepare` and `verify`, plus a
Root-supervised `run`. Preparation must follow its producer commit. The CLI is:

```text
python3 -B scripts/streaming_8x4_power_grid.py prepare \
  --views-report <closed-final-views>/report.json \
  --source-root build/campaigns/8x4-20261022-01/intake/psm-source-01 \
  --output <fresh-power-grid-owner>
```

Root must separately approve `run --output <owner> --container-name pinwheel-...`
through the campaign resource guard. It has no budget override: one offline
container, one CPU, 2 GiB memory/swap ceiling, 180 seconds for the one OpenROAD
process, 240 seconds for the container supervisor, and owned-container cleanup.
The outer campaign guard remains mandatory.

## Source and exact contract

The source intake binds nine original files to OpenROAD commit
`dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`, with SHA-256, Git blob and byte-count
checks. Its immutable manifest SHA-256 is
`7e20a6c7a1075fb1605fb9a49ec7eb93f84a5c424bc9f56afeb40ae0a2afb012`.
The pinned image, observed OpenROAD revision, complete staged producer Git
closure, source intake, exact ODB and canonical inventory are independently
bound. Native SWIG/API compatibility remains unmeasured until the first run.
The selected physical run and final views must agree on Docker's observed image
ID; the pinned architecture, complete rootfs layers and runtime configuration
also remain exact. The OCI config descriptor is not substituted for that ID.

The audited Tcl procedure `src/psm/src/pdnsim.tcl:11` forwards
`check_power_grid -net <actual-name> -error_file <owned-report>` without
`-floorplanning` or `-dont_require_terminals`. The SWIG adapter at
`src/psm/src/pdnsim.i:72` negates the latter flag, so the omitted waiver really
requires a block terminal. `pdnsim.cpp:115` checks connectivity, writes its error
report and emits PSM-0040 only on success. Observation-only
`set_debug_level PSM stats 1` enables shape/node/connection totals.

The wrapper closes gaps in the native command's admission:

- `ir_solver.cpp:224` accepts one placed BPin. The new census requires every
  inventoried BTerm to have BPins, and every BPin to be placed with nonempty
  positive-area routing geometry.
- `ir_network.cpp:237` skips unplaced ITerms, inverted bounding boxes and pins
  without routing shapes. The census rejects those states for every actual PG
  ITerm, including physical-only instances, and reconciles exact instance,
  master, terminal and rail identity with a fresh canonical `export_block` call.
  Every MPin must have nonempty routing rectangles. Via/nonrouting PG **pin**
  geometry is explicitly unsupported and blocks; it is never silently skipped.
- Both actual supply types must exist. Every actual rail needs required instance
  and block terminals, nonempty special wires, positive routing shapes and vias.
  Special-wire vias are handled by PSM's actual layer/via network.
- Each rail requires catch status zero, Tcl result one, exactly one PSM-0040
  success message, positive unique graph statistics and its own empty error
  report. An empty report or process exit zero alone cannot pass. Warnings,
  errors, missing/extra rail calls, missing terminals or failed cleanup reject.
- The physical census and all input bytes must match again after the queries.
  The reopener checks complete output membership, commands, resource policy,
  error files, actual totals, source identity and target/candidate joins.

## Scope of a possible pass

The result is a geometric same-rail open-path check under OpenDB/LEF/via
semantics, covering every required inventoried PG terminal. PSM merges a cell's
MPin shapes through its terminal model; this does not inspect internal cell GDS
conductivity. Its `ir_solver.cpp:384` `checkShort` is a stub returning true, so
cross-rail shorts and signoff DRC remain separate gates. Package/pad delivery,
activity/current assumptions, voltage drop, EM and resistance accuracy also
remain separate. The receipt permanently leaves `shorts_checked`,
`ir_drop_qualified`, `qualified` and `physical_acceptance` false.

Eleven focused HOST tests pass normally and under `python3 -O`. They include real
source-intake mutation/membership controls and an independent small geometric
fixture exposing an unplaced second BPin even when the first is placed. They
do not substitute for the actual Native observation.

The unexecuted checker now queries and preserves both `ord::openroad_version`
and `ord::openroad_git_describe`. The actual pinned replay runtime returns the
complete source commit from the former and an empty string from the latter.
Admission requires the exact full version; an optional nonempty description
must agree. Prefixes, longer hexadecimal tokens and conflicting commits reject.
This HOST correction changes no producer used by the 37 executed resource
owners, and no PG Native run or acceptance result follows.
