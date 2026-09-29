# Hierarchical SRAM integration remains unqualified

The September 27 integration reproduces a native SRAM comparison failure while
preserving **all 351 macro ports and four array hierarchy levels**. The full
layout and schematic contain the same **215,806 MOS devices** after native
finger combination. Eight circuit types still fail, so their parents—including
the macro top—are skipped. The qualified driver/delay fixtures have reached
macro context, but their cross-block connections are **not yet verified**.

The next useful experiment is a complete **32-bit array tile**, containing
192 MOS devices and 96 resistors. Its device ownership and metal2/metal3 resistor
interpretation need qualification before this macro comparison can pass. The
present evidence supports investigating the comparison representation first;
equal counts do not exclude real wiring or device-parameter defects.

The [tracked diagnostic](../../physical/fixtures/sram-integration/README.md),
[manifest](../../physical/experiments/sram-integration-results.json) and
[frozen protocol](sram-integration-experiment.md) retain implementation,
inputs, failed attempts and measured results. [Status](../research/status.md)
owns the active decision.

## What the experiment checks

The native extraction contains 140 layout circuit definitions. The source CDL
contains 145 definitions, of which 62 are reachable from this macro. The raw
extracted macro has no direct devices: the array and control circuits are still
hierarchical. The earlier large, nearly flat top circuit arose during comparison
alignment, where different layout and schematic names did not correspond.
KLayout documents that [alignment flattens unmatched circuits](https://www.klayout.de/doc/about/lvs_ref_netter.html).
This is a finding about this SRAM LVS flow, not RTL synthesis or Hardcaml.

The private deck changes only `sg13cmos5l.lvs`; its device extraction and
conductor-connectivity rules remain unchanged. The diagnostic:

1. Establishes **22 explicit circuit-name pairs**, without ignoring either side.
2. Expands the word-line-driver leaf/parent and delay-dummy/parent types into
   their macro context. It preserves every expanded device and parameter before
   normal device combination. The two separately named source delay parents
   are expanded independently; their definitions are not silently conflated.
3. Applies only the earlier qualified dummy `lvsres` → `res_metal1` translation.
   The source nodes and dimensions remain exact. Other resistor models stay
   present and explicitly unqualified; no general model alias is introduced.
4. Binds ports using **548 original top-owned physical labels**: 348 signals on
   metal2 (10/25), and 200 supply labels on metal4 (50/25). Every repeated supply
   label must probe the same physical net; every distinct port must probe a
   different connected net. All 351 declared schematic ports retain their
   identity/order and connectivity through preparation and comparison.
5. Checks array multiplicities after alignment, preparation and comparison.
   Both sides retain **two matrices, 128 columns, 1,024 tiles and 32,768 bit
   cells**. All resistor counts and native parameters remain intact. Native
   comparison, final log, database and completed policy audit are recorded
   separately from successful process execution.

Normal native alignment still handles unmatched helper definitions. The new
explicit hierarchy expansion is limited to the two admitted families; the
guarded array is never flattened into the macro. The macro receives 524 NMOS,
524 PMOS and 12 separate metal1 resistors from those expanded families on each
side, while their four active-delay instances remain hierarchical. These are
inventory observations: the skipped macro comparison does not match their nets.

## Measured comparison and failure locations

The final diagnostic and its packaged replay agree exactly on the circuit
readback and policy audit: **23 matching types, eight nonmatching types and
19 skipped parents**. The native final verdict is failure and the database does
not match, despite process exit code zero. No cross-block wiring fault is
claimed detected: the positive macro control already fails, so such a mismatch
would not establish sensitivity to the injected fault.

| Inventory after preparation | Layout | Schematic |
| --- | ---: | ---: |
| NMOS | 140,639 | 140,639 |
| PMOS | 75,167 | 75,167 |
| Qualified dummy metal1 resistors | 12 | 12 |
| Other resistors | 65,552 metal2 + 33,152 metal3 | 98,704 `LVSRES` |
| Declared macro ports | 351 | 351 |

The failure frontier is specific:

- `BITKIT_CELL`: layout owns two metal2 and one metal3 resistors, while the
  schematic also owns four NMOS and two PMOS. The extracted MOS devices occur
  higher in the tile hierarchy; the tile's complete MOS count agrees.
- `BITKIT_EDGE_LR`: the extracted leaf owns no MOS devices; its parent edge
  block owns all 32 NMOS represented by 16 two-device schematic leaves.
- `BLDRV`: layout owns nine NMOS and 13 PMOS directly. The source distributes
  the same expanded count between direct devices and five child instances.
- `CBUFX8`, `CINVX2`, `CINVX8`, `FILLCAP4` and `FILLCAP8`: extracted leaves have
  no devices while their source leaves have devices. Their parent control
  blocks retain the aggregate device counts. This resembles the earlier
  qualified driver ownership issue, but these new cases have not been repaired
  or locally qualified.

The manifest records every failed type's pins, devices, child references and
native mismatch counts. It also identifies bounded candidate neighborhoods:

| Candidate context | Expanded MOS on each side | Remaining interpretation |
| --- | ---: | --- |
| 32-bit `BITKIT_16x2_SRAM` tile | 128 NMOS + 64 PMOS | 64 metal2 + 32 metal3 resistors versus 96 `LVSRES`; ownership and boundary pins |
| `BITKIT_16x2_EDGE_LR` edge block | 32 NMOS | Parent/leaf ownership and boundary pins |
| `BLDRV` bit-line driver | 9 NMOS + 13 PMOS | Direct devices versus schematic child instances |
| `COLDRV13X8` column-driver block | 28 NMOS + 28 PMOS | Buffer and fill-cap ownership |
| `ROWREG7` row-register block | 134 NMOS + 134 PMOS | Inverter and fill-cap ownership |

These are inventories from the full preserved macro context, **not new passing
fixtures**. Matching their counts does not establish terminal, dimension or
port correspondence. Extra physical through-routing pins also remain visible;
they must not be deleted simply to equalize interface sizes.

## Reproduction, failure history and budget

Four bounded offline container invocations cost **38.143 CAD seconds** including
the failed recipe and cleanup. They comprise an extraction inventory, one
port-adapter refusal, the completed negative comparison, and its packaged
replay. Campaign total: **8,303.929 seconds / 138.40 minutes** of eight hours.
The source/artifact audit verifies **4,440 unique files**, exact packaged replay,
unchanged frozen inputs and absence of every receipted container.

The first adapter mistakenly treated layer 50/25 as topmetal1. It successfully
probed 348 signal labels, then refused the first supply label and performed no
comparison. The pinned deck defines that layer as metal4. The corrected recipe
uses `metal4_con`; the original failed receipt remains intact. No physical
label, wire, source schematic or installed PDK file was changed to make it pass.

The [recipe](../../physical/fixtures/sram-integration/README.md) pins the supplied
GDS/CDL, original narrow translation helper and all 183 deck files. Its output
directory is immutable after execution. The manifest links native logs,
database, complete physical witnesses, inventories, launcher, requests and
cleanup receipts under `build/validation/sram-integration-01/`. Those ignored
artifacts are local evidence; tracked hashes do not make them available in a
fresh checkout.

## Next gate and limits

First qualify the complete 32-bit tile with preserved neighboring geometry:
prove exact resistor marker/layer/dimension correspondence and reconcile MOS
ownership without discarding ports or devices. Require a positive comparison
and meaningful wiring/dimension/physical-fault controls before generalizing
that interpretation. Then address the recorded edge and control contexts and
repeat this hierarchical macro experiment. Cross-block fault sensitivity waits
for a passing macro positive control.

Keep the filled chip and its previous timing/electrical/DRC/package evidence.
There is no additional full route, chip edit or installed-PDK edit; three A
attempts remain used and two B attempts reserved. The earlier two Magic overlaps
and 438 conversion diagnostics were not rerun or waived. Full SRAM/GDS signoff,
compatible fast views, timed Lean refinement, accepted A/B and clean-source
replay remain open. This integration result does not establish analog or
silicon behavior.
