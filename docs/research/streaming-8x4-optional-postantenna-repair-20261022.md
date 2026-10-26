# Optional post-antenna candidate dispatch

This is a HOST design proposal. Root has not selected or launched the repair.
The original prepared02 inputs, producer files, `P.verify` contract and full01
evidence remain immutable. Placement stays 85%, clock 20 ns, semantic state 6039,
DRT 64 iterations and all ordinary rules and checks stay unchanged.

The exact HOST observation is
`build/campaigns/8x4-20261022-01/fanout-host-observation-01.json`.
Actual stage 33 to stage 35 DEF connectivity adds nine antenna diode loads to
`fanout1772/X` (6 to 15) and three to `fanout1699/X` (8 to 11); no loads are
removed and driver/net/master identities stay exact. This explains the added
fanout counts in fresh typical STA, but does not yet establish final failure
or successful repair. The carried Verilog view is byte-identical before/after
antenna insertion and cannot represent the added diodes.

If final actual checks still fail on these loads, the narrow candidate is a
distinct canonical design-repair step after antenna insertion and before
detailed routing. It uses the unchanged pinned LibreLane RepairDesignPostGRT
implementation, inherited actual configuration and cell/Liberty rules. A
distinct step ID records the added invocation; there is no count override,
diode deletion, new rule waiver, density change or late pass assertion.

The actual original stage 33 `COMMANDS` pins
`/nix/store/9k9an9gig3wy8psajmpm2c6pzl9qkiv1-python3-3.13.13-env/lib/python3.13/site-packages/librelane/scripts/openroad/repair_design_postgrt.tcl`.
Its executed log runs `global_route` before `repair_design`, performs detailed
placement, then runs `global_route` again and writes `after_grt.guide`. The
fresh source intake at `intake/librelane-native-source/manifest.json` confirms
this body: repair Tcl SHA256
`b045dd15f1f695efaad2081cb161a0091f86085cb33ddc64e0fdd16725829e92`;
the final GRT is conditional on `GRT_DESIGN_REPAIR_RUN_GRT`, which is true in
the actual resolved configuration. Its unchanged common GRT body explicitly
writes a fresh guide. No additional standalone GlobalRouting step is required
under this exact inherited configuration. The bound HOST source assessment is
`build/campaigns/8x4-20261022-01/repair-source-review-01.json`.

The new typed preparation should bind the closed original report, original
prepared02 seal, exact chosen post-antenna ODB/state/view bytes, measured fanout
observation, new committed producer/plugin closure, pinned runtime and sole
campaign repair identity. It must use a new schema and output directory.
The exact permitted schedule delta is one canonical repair invocation after
RepairAntennas and before DetailedRouting, with the complete ordinary tail.
Disabled inherited EQY/XOR remain explicit.

A restart from the measured post-antenna state can avoid repeating the earlier
floorplan, global placement and CTS prefix; the added canonical repair still
runs its own detailed placement and routing:
mount original prepared02 inputs and parent flow read only; place the seed,
new plugin and dispatch metadata in a separate read-only repair input mount;
write all fresh states to a new owned run. Seed view paths must be translated
only by an explicit, hash-bound `/work/run/` to read-only parent mount mapping,
with containment and exact file checks. Never relabel an old ODB as repaired.
The pinned CLI source confirms the explicit flow override, checked State load,
and `--from` execution start while retaining the supplied state. The new
registered step schedule and actual native restart remain observation gates
before any repair result can be admitted.

The added step must preserve power connectivity, check actual post-repair
fanout and native metrics, and retain exact generated ODBs. The candidate
does not pass until a fresh completed DRT state and full ordinary terminal
evidence close. A new candidate-aware target authority must separately verify
its preparation, original baseline and schedule delta; existing consumers
must not weaken `P.verify` or accept the new schema as the old preparation.
The same exact final-ODB geometry, nine official prechecks, independent
antenna/LVS, qualified RC/timing and all-state M/public-wire gates still apply.

Root must decide after the terminal evidence, keep the sole-repair budget,
respect the 03:00:35 UTC new-native cutoff and reserve closeout/cleanup time. No
second candidate is implied if the controlled repair fails.

## Source-audit clarification — 2026-10-22 23:48 UTC

The original stage 35 uses LibreLane
[`_DiodeInsertion(GlobalRouting)`](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261022-01/intake/librelane-native-source/librelane/steps/openroad.py:1908),
whose [`antenna_repair.tcl`](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261022-01/intake/librelane-native-source/librelane/scripts/openroad/antenna_repair.tcl:27)
invokes native `repair_antennas`. The earlier investigation inspected the
separate `odbpy/diodes.py` path; attributing that implementation to stage 35
was incorrect. Any suggestion that original stage 35 omitted legalization or
guide refresh is retracted.

At pinned OpenROAD `dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`,
[`RepairAntennas.cpp`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/grt/src/RepairAntennas.cpp#L144)
legalizes the inserted diodes through `legalizePlacedCells` and detailed
placement. [`GlobalRouter.cpp`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/grt/src/GlobalRouter.cpp#L560)
updates dirty routes and saves guides. Their Git blob identities are
`07795543cf3877e1d8d4b842bb6a1d9d4a0734a8` and
`b57d47085e2bb7ee382520357bfb5e74e2799700`. The in-DRT antenna repair uses
this same native implementation, with detailed-route mode fixing other placed
instances while legalizing new diodes. It does not invoke fanout design repair.

The exact measured diode-load increases still justify the fanout diagnosis.
They do not prove the cause of the original Metal2 shorts. An older exported
stage-33 guide cannot establish the later stage-35 embedded guide contents;
actual completed DRC coordinates and shape/net ownership remain necessary.

## Terminal campaign result

The sole repaired candidate executed as `native-repair-02`. The preceding
`native-repair-01` failed its schedule validator before any CAD state and is
preserved separately. Repair02 adds four buffers on two nets, retaining their
15/11 recursive endpoints. Nominal pre-new-diode STA reports no fanout failures,
setup +9.87919 ns and hold +0.0771534 ns; this is not qualified extracted timing.

Its first internal route reaches zero violations. Subsequent antenna checking
finds 35 nets / 36 pins and inserts 39 diodes. The last completed reroute
iteration has 40 Metal2 violations: 36 shorts and four spacing. The resource
guard stops near 94.87% of the fixed 6 GiB limit, with no observed OOM. The whole
DetailedRouting step remains incomplete and no final target is eligible.

The independent terminal review rehashes all 53 retained artifacts:
`build/campaigns/8x4-20261022-01/host-routing-terminal-02/review.json`, SHA256
`7bb9fa5fed39c675ac18ba9f46d64bc9f1c4409e69d75058202e1c02d76402f0`.
The outer resource receipt SHA256 is
`237d48c6b349ab7de03f1e72143acf829eb70ff3060e5582c588d0ec5312e68a`;
it preserves stopped124, input continuity and confirmed cleanup. The physical
repair allowance is consumed. The later [diagnostic reconstruction](streaming-8x4-route-replay-20261023.md)
captures access geometry without promoting this failed whole-flow gate.
