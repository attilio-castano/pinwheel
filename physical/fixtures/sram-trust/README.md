# SRAM provenance and boundary coverage

This bundle makes the [trust-boundary proposal](contract.json) reviewable.
It does not admit the SRAM or change production checks. The
[study](../../../docs/physical/sram-trust-results.md),
[manifest](../../experiments/sram-trust-results.json) and
[frozen protocol](../../../docs/physical/sram-trust-experiment.md) own the
measurements, source identities and execution limits.

`sources.json` lists public GET captures, timestamps and hashes. Raw source
bodies and native outputs live under ignored `build/validation/sram-trust-01/`.
They are not supplied by a fresh checkout. The manifest also pins the exact
launcher and both native extraction workers, including the failed first probe.
This is a recorded local experiment, not a completed clean-source replay.

From a checkout with the retained evidence, the read-only source audit is:

```sh
python3 -B physical/fixtures/sram-trust/audit_sources.py
```

It verifies the actual seven macro files and the shared simulation dependency
against the complete pinned PDK tree, the CMOS5L library alias, all successful
public captures, and the original/pinned bit-cell source dimensions. It fails
on missing or different inputs. It does not infer qualification from identity.

Inside the pinned offline CAD container, mount this bundle read-only at
`/recipe`, the matching PDK read-only at `/pdk`, and the retained macro files
read-only at `/macro`. Mount the unchanged native abstract extraction at
`/evidence/abstract.spice` and a fresh writable directory at `/output`:

```sh
python3 -B /recipe/boundary.py \
  --abstract-spice=/evidence/abstract.spice \
  --cdl=/macro/RM_IHPSG13_1P_512x64_c2_bm_bist.cdl \
  --lef=/macro/RM_IHPSG13_1P_512x64_c2_bm_bist.lef \
  --setup=/pdk/ihp-sg13cmos5l/libs.tech/netgen/ihp-sg13cmos5l_setup.tcl \
  --output=/output/boundary
```

Use the manifest's outer time/CPU/memory limits. The script limits each Netgen
call to 30 seconds and refuses an existing output. It does not authorize or
allocate another run. Source and extracted pin orders are obtained separately;
both must bijectively match the independent 351-pin LEF interface. The extracted
macro body must actually be empty. Only bus/power spelling is normalized.

The native one-instance fixture uniquely matches, rejects address-to-ground
and ground-to-power connection faults, and **still matches** after an internal
source width change is projected away. This last control documents missing
coverage. Actual chip power ties and wiring belong to the separately retained
chip-boundary experiment. Extraction diagnostics remain failures; the boundary
script neither consumes nor clears them.

The [unsent maintainer report](../../../docs/physical/sram-maintainer-report.md)
asks for the exact source/geometry convention and supported qualification route.
The contract separates digital behavior, wrapper obligations, provenance,
physical internals, corner compatibility and formal composition. It introduces
no global Lean axiom or automatic acceptance override.
