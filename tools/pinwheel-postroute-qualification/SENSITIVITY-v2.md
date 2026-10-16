# Native LVS sensitivity and optional antenna diagnostic

These are new v2 helpers. Frozen v1 qualification packages remain unchanged.
Staging and host tests do not launch CAD/Docker. Root owns every native launch
through the copied campaign runner and shared heavy.lock.

## Small positive comparator fixture

The synthetic fixture uses actual CMOS5L `buf_1` and `dfrbpq_1` SPICE port
models, two independently constrained data paths, explicit VPWR/VGND and the
exact 345-port SRAM boundary model. It is not physical extraction or a chip.
Native Netgen must uniquely match its positive before running either fault.

```sh
python3 -B tools/pinwheel-postroute-qualification/lvs_fixture_host_v2.py \
  --prepared build/physical/tt-overnight-qualification-plan-01/p2-control01-prepared-01/prepared.json \
  --out build/physical/tt-overnight-qualification-plan-01/lvs-native-fixture-01
```

Only root, after the heavy lock is free:

```sh
python3 -B build/physical/tt-overnight-qualification-plan-01/lvs-native-fixture-01/lvs_execute_staged_v2.py \
  --staged-root build/physical/tt-overnight-qualification-plan-01/lvs-native-fixture-01 \
  --native-seconds 300
```

The first fault detaches `_30759_/D` from consumed `net8042` onto one fresh
isolated node. The second merges **all** `net8046` contacts into distinct
consumed `net8042`. Instances, masters and every other standard-cell terminal
connection stay identical. Each mutant is a copied reference; originals stay
untouched. Record exact changed terminals and reference/script/report/JSON/log
hashes. Process failure, missing verdict, ambiguous verdict or missing native
JSON cannot qualify a negative control. Merely failing both faults when the
positive fails never qualifies anything.

## Full actual comparison sensitivity

After a completed, uniquely matching actual `lef-lvs` or `gds-lvs` producer,
stage `lvs_controls_host_v2.py --positive-root ACTUAL_LVS_PHASE --out NEW_DIR`.
It verifies the positive producer/measurement/report, copies all reference and
extraction inputs, replays its exact native script with copied paths, and
requires positive replay before the same two faults. Root can launch the copied
`NEW_DIR/lvs_execute_staged_v2.py --staged-root NEW_DIR --native-seconds 600`.
The small fixture's pass does not replace an actual candidate positive or its
complete model/port/connectivity review. A failing actual LVS remains a raw
failed comparison. No helper automatically claims full physical connectivity
or internal SRAM qualification.

## Optional antenna check only

```sh
python3 -B tools/pinwheel-postroute-qualification/antenna_host_v2.py \
  --prepared build/physical/tt-overnight-qualification-plan-01/p2-control01-prepared-01/prepared.json \
  --out build/physical/tt-overnight-qualification-plan-01/control01-antenna-diagnostic-01
```

Only root, preferably after the actual RCX/STA pipeline:

```sh
python3 -B build/physical/tt-overnight-qualification-plan-01/control01-antenna-diagnostic-01/antenna_host_v2.py \
  --staged-root build/physical/tt-overnight-qualification-plan-01/control01-antenna-diagnostic-01 \
  --native-seconds 300 --run
```

The [pinned checker](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/ant/src/AntennaChecker.cc#L1088)
can create/destroy temporary wires when only global guides exist. This helper
requires actual ROUTED detailed wires for every consumed net, so that fallback
is forbidden. It captures the installed Tcl API and native model/gate-area
coverage before its sole `check_antennas -verbose` command. Full inventory,
master pins/OBS, vias and DEF geometry/TAPER must remain exact afterward.

Missing native API/model queries, zero gate-area coverage or empty rule
coverage prevent checker admission. Partial gate-area or used-layer rule
coverage keeps any result unqualified. Counts remain null if unavailable.
The gate denominator is connected INPUT ITerms on consumed nets; package
BTerms and internal SRAM transistor coverage remain separate. Native zero
counts never automatically become an antenna pass. No repair, insertion,
rerouting, fill or PG/clock changes are allowed. Native300/all345 seconds is
the default; the helper rejects native budgets above600 seconds.
