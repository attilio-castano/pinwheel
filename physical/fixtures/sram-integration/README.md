# Hierarchical SRAM integration diagnostic

This recipe reproduces a **failing** comparison of the unchanged supplied
512×64 SRAM. It preserves the array hierarchy and all 351 physical macro ports
while expanding only the previously qualified driver and delay families.
It is not a signoff policy. Process exit zero means the diagnostic completed;
read `report.json`, the native log, database and completed policy audit for the
actual circuit verdict.

The [study](../../../docs/physical/sram-integration-results.md),
[frozen protocol](../../../docs/physical/sram-integration-experiment.md) and
[manifest](../../experiments/sram-integration-results.json) own scope and results.

`inputs.json` pins the complete supplied GDS/CDL, the existing narrow dummy-model
adapter and all 183 LVS deck files. `contract.json` declares 351 ordered ports,
22 explicit circuit pairs, the limited flattening targets and four preserved
array levels. `policy.rb` reads 548 top-owned labels: 348 on metal2 (10/25) and
200 supply labels on metal4 (50/25). Repeated labels must probe the same extracted
net, and different declared ports must probe different nets. No conductor or
device terminal is reconnected.

Only the qualified dummy resistor is translated to `res_metal1`, preserving
nodes and dimensions. The remaining `LVSRES`, `res_metal2` and `res_metal3`
models are retained as unqualified diagnostics, without an invented mapping.
All resistor counts/parameters and array multiplicities survive alignment,
preparation and comparison. Scoped hierarchy expansion preserves all device
parameters. The private deck changes only `sg13cmos5l.lvs`.

Inside the pinned offline CAD container, with the supplied inputs mounted
read-only, use a fresh output directory:

```sh
python3 -B /recipe/run.py \
  --macro-gds=/macro/RM_IHPSG13_1P_512x64_c2_bm_bist.gds \
  --macro-cdl=/macro/RM_IHPSG13_1P_512x64_c2_bm_bist.cdl \
  --pdk-deck=/pdk/ihp-sg13cmos5l/libs.tech/klayout/tech/lvs \
  --fixtures=/fixtures/sram-context \
  --output=/output/hierarchical
```

Use the image identity and outer time/memory/CPU limits in the manifest. The
runner caps its native subprocess at 480 seconds and refuses changed inputs
or an existing output. It does not launch Docker, acquire a new execution
budget or authorize broader flattening. The recorded bounded launcher also
hashes inputs before/after execution and records container cleanup.

The retained result is 23 matching circuit types, eight nonmatching types and
19 skipped parents, including the macro top. Equal transistor counts and
physically bound ports do not establish cross-block wiring equivalence.
Connection-fault sensitivity is deferred until the positive comparison passes.
