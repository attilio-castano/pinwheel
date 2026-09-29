# SRAM fixture comparison policy qualified

The September 27 continuation qualifies one comparison policy on all four
[unchanged SRAM fixtures](../../physical/fixtures/sram-context/README.md), in both
hierarchical and flat extraction. The complete driver block accounts for all
**64 MOS devices and 34 ports**; the complete delay block accounts for all
**28 MOS devices, six separate resistors and four ports**. All 42 injected-defect
comparisons reject. This settles the local checker gate; full SRAM and chip
signoff remain unqualified.

The [reviewable recipe](../../physical/fixtures/sram-comparison/README.md),
[manifest](../../physical/experiments/sram-comparison-results.json) and
[frozen protocol](sram-comparison-experiment.md) retain the implementation,
measurements and bounded experiment history. [Status](../research/status.md)
owns the next decision.

## Correction to the preceding report

The preceding study incorrectly used matching circuit pairs in `.lvsdb` as a
complete native pass. The pinned deck computes its final result from both
device comparison and `flag_missing_ports`; its wrapper can return exit code
zero even when that final result fails. The original isolated-driver,
flat driver-parent and adapted isolated-dummy database matches **failed the
native port check**. The adapted complete delay parent and its unchanged
physical carrier really passed. The original files and receipts are preserved;
the new manifest audits all 24 earlier invocations and records the correction.

Likewise, the original discarded-output control was a database match with a
failing native port verdict. A new controlled ablation, with physical port
recognition working but interface safeguards removed, now demonstrates a
**real final-native false positive** for that same disconnected output. These
are different observations and both remain recorded.

## What changed and why

The final recipe copies the pinned 183-file LVS deck and changes only the private
copy of `sg13cmos5l.lvs`. Device-recognition rules, conductor connectivity,
installed PDK, source GDS and all original fixture files remain unchanged.
The existing narrowly checked `lvsres` → `res_metal1` dummy-model translation
preserves its nodes and exact **0.600 × 0.260 µm** geometry.

1. **Physical boundary ownership.** Read only labels owned by the fixture's
   top cell. Probe the extracted metal net at each original label position,
   require one distinct connected net per declared port, and retain that binding
   through preparation. Existing `VDD!` and `VSS!` labels supply the corresponding
   `VDD` and `VSS` ports; no label or electrical connection is invented.
2. **Hierarchy correspondence.** Flatten the two small extracted/schematic
   netlists after extraction. Check expanded device counts and resistor
   dimensions before and after. This reconciles the driver's NMOS ownership
   without changing layout geometry or waiving a missing device.
3. **Dimensional resistors.** Enable length/width comparison on both sides,
   disable resistance-value comparison and series/parallel combination, and
   require every resistor to survive preparation with its dimensions intact.
   This is a dimensional LVS interpretation, not analog characterization.
4. **Preserved interface and complete verdict.** Check declared schematic ports
   before and after preparation, create layout pins from the physical witnesses,
   preserve pins during cleanup and require the named net correspondences.
   Acceptance requires a successful process, matching database, final native
   pass and complete policy audit. A crash is not a passing negative control.

The source investigation found genuine older labels on **8/2**, which the pinned
deck's metal1 text rule does not read. Simply reading all those labels is
insufficient: flat extraction combines parent and child names such as
`A,A<15>` or `VDD,VDD!`; delay-chain internal nets can carry `A,Z` from adjacent
children. Those internal labels are not external ports. The retained recipe
uses top-owned label positions and therefore needs **no change to the deck's
general label rules**. The protocol's initial description of anonymous supplies
was resolved by this source-label evidence.

KLayout documents [physical net probing](https://www.klayout.de/doc/code/class_LayoutToNetlist.html)
and the [netlist preparation operations](https://www.klayout.de/doc/code/class_Netlist.html).
The recipe probes immediately after extraction and replaces automatic pin
creation/purging with explicit boundary pins, device combination and cleanup
that preserves pins. The measured fixture controls, rather than API documentation
alone, qualify this use.

## Results and fault sensitivity

| Unchanged fixture | Devices after preparation | Ports | Deep | Flat |
| --- | --- | ---: | --- | --- |
| Isolated word-line driver | 2 NMOS + 2 PMOS | 4 | Native pass | Native pass |
| Complete 16-driver parent | 32 NMOS + 32 PMOS | 34 | Native pass | Native pass |
| Isolated delay dummy | 1 NMOS + 1 PMOS + 1 resistor | 4 | Native pass | Native pass |
| Complete delay parent | 14 NMOS + 14 PMOS + 6 resistors | 4 | Native pass | Native pass |

The final packaged replay contains **52 invocations**: eight fixture passes,
two passes for the exact unchanged physical-mutation carrier, and **42 defect
rejections**. Every device and declared pin in a passing fixture matches.
Each complete delay comparison retains six `MatchWithWarning` internal net
pairs: the six identical dummy transistor pairs admit ambiguous correspondence
for their internal `VSS_R`/`VDD_R` nets. The native circuit verdict passes;
the manifest preserves those warnings. This does not establish a unique mapping
of those internal dummy nets to instance names. The negative suite exercises
each of 21 fault types in both modes:

- Schematic output open/short, internal drain open and missing NMOS.
- Wrong resistor width, length and equal-ratio dimensions; untranslated model
  and missing width.
- Physical metal open, metal bridge and missing NMOS gate geometry, each
  affecting the six dummy occurrences with their neighborhood retained.
- Missing, extra or renamed declared ports, and swapped inputs or outputs.
- Missing, renamed, swapped or off-metal physical labels, with polygons unchanged.

**20** defect comparisons reach native `NoMatch`; **22** are refused earlier by
explicit interface/model/dimension guards. The physical open is caught before
native comparison: deep extraction loses the connected port during flattening,
while flat extraction already exposes a disconnected port. The original control
recipe expected a native mismatch and therefore retains a failed receipt; the
final recipe explicitly checks these attributable guard failures.

Eight additional evidence controls reject an absent or incomplete policy audit,
missing preparation stages or physical witnesses, a negative native verdict,
missing final-native pass text, nonzero process exit and a mismatching database.
The original fixture identity/model-translation/port-use checks also pass.

## Ablations and limits of the diagnosis

Keeping the unmatched driver hierarchy reproduces its child `NoMatch` and
skipped parent comparison. Removing reference-interface safeguards and restoring
native schematic simplification discards the disconnected output and permits
a final native pass. These support the hierarchy and interface corrections.

Removing the explicit resistor non-combination settings **does not reproduce
the original mismatch** once the dimensional classes agree. Both sides combine
six resistors into one with width 0.260 µm and length 3.600 µm, then pass. The
expectation of a native failure was wrong and remains a failed ablation receipt.
This separates class alignment from the deliberate stronger contract of
preserving each resistor individually. Do not claim the non-combination flags
alone caused the original failure.

The earlier global legacy-label patch is unnecessary: removing it retains all
eight positive fixture passes. Ruby net proxy identity initially caused false
name-collision refusals; the corrected guard uses the circuit and extracted
cluster identity, requires uniqueness and preserves terminal counts. Its failed
recipe remains frozen. A syntax error in the first resistor-ablation recipe is
also retained as a tool failure, not a circuit verdict.

## Budget and next gate

Ten bounded offline invocations cost **198.128 CAD seconds**, including failures
and cleanup. Campaign total is **8,265.786 seconds / 137.76 minutes** of eight
hours. They contain 133 native-tool invocations, including guard refusals and
one syntax failure; only the final 52-invocation replay is the packaged
qualification. All frozen source hashes match and receipted containers are
absent. Four receipts complete; six preserve failed expectations or recipes.
No chip edit, installed-PDK edit or additional full-routing A attempt occurred.

**Next gate: check these blocks' connections in the hierarchical SRAM macro.**
The inventory shows both complete fixture parents are direct children of the
macro, so there is no intervening supplied parent block to promote. Admit a
separately frozen, bounded integration experiment that reconciles only these
affected block types, retains the array hierarchy, accounts for every macro
port and repeats connection faults across the block boundaries. The present
fixture allowlist must refuse that broader input until its contract is extended
and checked. Do not apply the fixture's whole-netlist flattening to the full
macro or launch another full-flat chip extraction.

Passing local fixtures do not settle the earlier full-SRAM comparison, two
Magic overlaps or 438 conversion diagnostics. The supplied SRAM blackbox,
fast standard-cell/SRAM temperature pairing, timed Lean refinement, accepted
A/B, clean-source replay and complete design iteration remain open.
