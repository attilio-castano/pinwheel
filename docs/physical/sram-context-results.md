# SRAM failures reduced to complete local fixtures

**September 27 correction:** the subsequent [comparison-policy study](sram-comparison-results.md)
audits the final native logs. Six earlier database matches, including the
isolated drivers, flat driver parent, adapted isolated dummies and discarded-output
control, actually failed the native port check. The tables below distinguish
database correspondence from a complete native pass. Original raw manifests and
receipts remain frozen. The new policy qualifies both modes of all four fixtures.

The September 27 continuation isolates both failing SRAM cells without changing
the chip or PDK. **The word-line driver failure is a hierarchy mismatch in the
small reproduction:** its NMOS devices are extracted into the parent circuit.
**The delay dummy has a resistor-model mismatch:** a narrowly checked model
translation passes in its complete hierarchical neighborhood. Full SRAM and GDS
signoff remain unqualified.

The [tracked fixtures](../../physical/fixtures/sram-context/README.md) retain
four GDS layouts, their supplied schematic subsets, two explicitly adapted
schematics and the exercised input guards. They are small enough to compare in
seconds. The [manifest](../../physical/experiments/sram-context-results.json)
binds their source identities, all native results, mutations and failed runs.
The [protocol](sram-context-experiment.md) was frozen before execution;
[status](../research/status.md) owns the current decision.

## Geometry and comparison boundary

The source is the same supplied `RM_IHPSG13_1P_512x64_c2_bm_bist` used in the
[preceding SRAM study](sram-extraction-results.md). The inventory locates 256
word-line drivers and 12 delay dummies. Their complete parent cell types are
`RM_IHPSG13_1P_WLDRV16X8` and `RM_IHPSG13_1P_DLY_2`, respectively. The fixture
exports preserve every layer, polygon, label and internal instance transform;
all per-layer XOR and text comparisons pass after writing and rereading GDS.
No clipped transistor is presented as a complete LVS fixture.

The driver parent contains sixteen drivers; the delay parent contains six dummy
cells and two active delay cells. These preserve the immediate physical
neighborhood. They do not include all surrounding macro geometry. The first
driver parent occurs at `(406.520, 46.500)` µm in the source macro; the first
delay parent occurs at `(384.590, 17.100)` µm. The inventory retains every actual
occurrence and transform.

The supplied parent schematic names differ from GDS. The fixture changes only
the `.SUBCKT` boundary name, from `RM_IHPSG13_512x64_c2_1P_WLDRV16X8` or
`RM_IHPSG13_512x64_c2_1P_DLY_pcell_2` to the corresponding GDS name. Every port,
child instance and device statement remains from the source. CDL continuation
lines are joined. The model translation below is a separate, labeled artifact.

## What the driver fixture establishes

| Scope / comparison | Layout extraction | Database result / final native verdict |
| --- | --- | --- |
| Isolated driver, deep or flat | Two NMOS and two PMOS | Database Match; native port check fails |
| Complete 16-driver parent, deep | 32 NMOS at parent level; two PMOS in each driver child | Child fails; parent comparison skipped |
| Same complete parent, flat | 32 NMOS and 32 PMOS | Database Match; native port check fails |

Thus the two apparently missing NMOS devices in the earlier child report are
not missing from this preserved neighborhood. Hierarchical ownership differs
between the extracted circuit and supplied schematic. The flat comparison
accounts for all 64 devices and their connectivity without editing geometry.
The pinned deck derives wells and device regions from contextual geometry, but
this experiment does not identify a single Boolean rule as the sole cause.

Deliberately shorting a driver output to ground, removing the schematic NMOS,
and breaking its internal drain connection each produce native `NoMatch`.
The internal-open and device-removal controls affect the shared child definition
and therefore all sixteen occurrences; the output short affects one instance.

One earlier open control exposes a separate **database-only false positive**: changing
the output connection of `XBUF<0>` to a new internal net leaves the declared
`Z<0>` port disconnected, but native simplification discards that unused port
and still records a database match. Its final native result fails because of the
unrecognized supply labels. The explicit parent pin-use guard rejects that
exact counterexample and passes both unmodified parents. The later policy study
recognizes the physical ports, then independently demonstrates a final-native
false positive when interface safeguards are removed.
The guard is fixture-specific, not a general solution to every possible pin error.

## What the delay fixture establishes

The original isolated dummy and complete parent fail in both modes. The dummy
contains one NMOS, one PMOS and a resistor in both circuits, but their models are
layout `res_metal1` and schematic `LVSRES`.

The source marker is a complete rectangle on GDS layer **8/29**, entirely covered
by metal1, with **0.600 µm length and 0.260 µm width**. Those dimensions exactly
match the supplied `R0 Z A lvsres w=2.6e-07 l=6e-07`. The experimental adapter
changes only `lvsres` to `res_metal1`, preserving the terminals and original
dimension tokens. The pinned layout class enables length/width comparison and
disables resistance-value comparison. This is a dimensional LVS interpretation,
not a characterized analog resistance model.

| Adapted comparison | Database result / final native verdict |
| --- | --- |
| Isolated dummy, deep | All three devices match; native port check fails |
| Isolated dummy, flat | All three devices match; native port check fails |
| Complete delay parent, deep | All three circuit pairs match, including parent connections; final native pass |
| Complete delay parent, flat | **NoMatch:** six layout resistors versus one combined schematic resistor; all 28 MOS devices match |

The flat failure remains a reduced test case for schematic device-class and
combination behavior. It prevents generalizing the model-name adapter to an
arbitrarily flattened SRAM. The installed PDK and default comparison options
remain unchanged.

The passing hierarchical parent rejects all six native negative controls:

- Double the resistor width, double its length, or double both while retaining
  the same length/width ratio: all three fail.
- Cut the physical resistor metal, bridge around it with metal, or remove NMOS
  gate geometry: all three fail.

The physical controls edit the shared dummy definition, affecting its six real
instances while retaining all neighboring geometry. Their exact unchanged
carrier also passes a native comparison, so the rejection is attributable to
the injected edit. Original-to-carrier geometry and text checks pass before
each edit. Mutation areas and native device cross-references are retained.
Seven adapter controls reject unknown models, absent or duplicate dimensions,
missing resistors, wrong dimensions and a changed terminal.

## Receipts and limits

Six bounded container invocations include **24 native LVS comparisons**. Three
container receipts complete successfully and three retain failed expectations:
an exporter check initially mishandles an absent layer, the adapted flat delay
comparison fails, and the discarded-output control is incorrectly accepted by
the database-based result reader. The absent-layer check is repaired in a new
frozen recipe; the raw results are not overwritten or relabeled as passes.

All invocations, including failed work and cleanup, cost **39.179 CAD seconds**.
Campaign total is **8,067.658 seconds / 134.46 minutes** of eight hours. Input
hashes remain unchanged and all receipted containers are absent. No chip edit,
PDK edit or additional full routing attempt occurred; three A attempts remain
used and two B attempts reserved.

The initial inventory's `Region.count()` fields count hierarchical occurrences
and must not be read as isolated-cell polygon counts. Qualification uses explicit
polygon iteration, XOR and transformed text inventories. Likewise, device objects
in the serialized LVS cross-reference do not supply usable terminal bindings in
the first readback; null entries are not evidence of disconnected devices.
Native comparison statuses, net/pin pair statuses and the extracted `.cir`
files carry connectivity evidence, but the final native log must also pass the
port guard. Process exit status and a database Match are each insufficient:
the native wrapper exits zero on both final pass and failure.

**Next gate:** qualify a consistent, geometry-preserving comparison policy on
these fixtures before expanding to a larger SRAM block. It must account for
driver hierarchy ownership, give both sides the same dimensional resistor
combination rules, and refuse disconnected declared ports. Then use complete
strict SRAM evidence or justified supplied-IP evidence to settle the blackbox
boundary. Another chip route does not address these checker failures.

The previous Magic overlaps and conversion diagnostics are not rerun or waived.
Compatible fast characterization, full SRAM/GDS signoff, complete timed Lean
refinement, accepted A/B, clean-source replay and competition admission remain
separate open gates.
