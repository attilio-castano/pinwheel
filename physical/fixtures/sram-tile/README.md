# Supplied SRAM tile: dimensional discrepancy diagnostic

The supplied 32-bit tile is **not qualified**. Its 96 resistor markers measure
0.200 × 0.600 µm; its reference CDL declares 0.260 × 0.600 µm. The strict adapter
refuses that disagreement. This recipe creates an explicitly separate diagnostic
copy with three width tokens changed, affecting 96 instances, to test causality.
A successful process reproduces the diagnostic; it does not admit the source.

The [study](../../../docs/physical/sram-tile-results.md),
[frozen protocol](../../../docs/physical/sram-tile-experiment.md) and
[manifest](../../experiments/sram-tile-results.json) own the evidence and limits.
The supplied macro, installed PDK and chip remain unchanged. The original GDS
and source CDL are included here; see [NOTICE](NOTICE) for their license.

The GDS is the entire existing `RM_IHPSG13_1P_BITKIT_16x2_SRAM` hierarchy,
including 32 cells and four tap instances. Export preserves every polygon and
text on all 27 source layers. The source contains its two reachable definitions,
with only the boundary type renamed to match the GDS. `geometry.json` records
the original marker shapes and native resistor terminals. `check_inputs.py`
requires exact source nodes, models, dimensions and physical witnesses.

Only the diagnostic copy changes `w=2.6e-07` to `w=2e-07` in R0, R1 and R2.
It then translates R0/R1 to `res_metal2` and R2 to `res_metal3`, preserving nodes
and lengths. `policy.rb` reconciles device ownership inside this tile, binds
all 42 ports from their original top-owned metal labels, retains each resistor,
and compares width and length. Resistance value is outside this dimensional
LVS contract; resistor series/parallel combination is disabled. The private
deck copy changes only `sg13cmos5l.lvs`.

Inside the pinned offline CAD container, with this directory mounted read-only
at `/recipe`, the matching PDK at `/pdk`, and a writable fresh `/output`:

```sh
python3 -B /recipe/check_inputs.py
python3 -B /recipe/run.py \
  --pdk-deck=/pdk/ihp-sg13cmos5l/libs.tech/klayout/tech/lvs \
  --output=/output/tile --controls
python3 -B /recipe/audit_controls.py \
  --controls-output=/output/tile --output=/output/tile-audit.json
```

Use the image identity and outer time/memory/CPU limits in the manifest. The
runner caps each native process at 90 seconds and refuses changed fixture/deck
inputs or an existing output. It does not allocate execution budget or launch
Docker. The recorded launcher checks source hashes before/after execution and
records cleanup. `inputs.json` pins the physical/source inputs, interpretation
and all 183 deck files; the manifest also pins the exact executed scripts.

The counterfactual and unchanged physical carrier each pass deep and flat:
288 device pairs, 182 net pairs and 42 pin pairs match without ambiguity.
All 42 fault comparisons reject: 30 native mismatches and 12 explicit policy
refusals. Seven incomplete-evidence cases and 13 adapter faults also refuse.
Restoring the original widths fails in both modes. These results support the
discrepancy diagnosis, not automatic adoption of the edited schematic.

**Historical reporting correction:** the frozen runner's auxiliary local
`changed_area_dbu2` field reads zero after a live geometry view was modified.
It was not an acceptance input. Its independent `whole_tile_changed_area_dbu2`
checks are correct. `audit_controls.py` separately reloads the saved GDS and
records the correct local/whole-tile areas. Preserve both receipts; do not use
that historical local field to describe fault size.

Resolve the source/physical width contract before promoting this tile or
generalizing the model translation. This bundle does not qualify the other
array/control contexts, macro wiring, analog behavior or silicon.
