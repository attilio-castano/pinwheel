# Native routing import preservation qualification

Measured on 2026-10-16 against OpenROAD
`dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`, actual ELF SHA-256
`6ba87b45c762ee8c9670375c204cd03d801a6da98cd6e056a1c73027aad68a7c`.
This qualifies the bounded import/serialization repair and a real-P2 no-edit
control. It does not establish routing closure, timing or tapeout readiness.

Two native defects were reproduced. The importer ignores per-path `RULE`
opcodes, loses default/TAPER exceptions on NDR nets, and derives widths and
implicit endpoint extensions from default layer widths. The writer also tests
the **begin** style when emitting a variable **end** extension, dropping that
endpoint when the begin is truncated. It compares implicit extensions against
the default layer width even when encoding an NDR path.

The versioned fix tracks rules while constructing native route objects,
preserves taper flags, widths and extensions before post-processing or GC,
and repairs those writer predicates. Exact native `initDesign` and `endFR`
copies bind the local importer/final writer through `-Wl,-Bsymbolic`. The
ordinary main and twenty-argument dispatch retain the normal scheduler;
additional guards require fresh state, pin access and admitted guides, and
forbid single-step/distributed execution, PG repair and guide updates. A
read-only pre-GC audit rejects unmatched or ambiguous geometry/rule objects.
Resident debug snapshots are disabled because they call the unmodified writer.

All **12 native fixture gates passed**: plain original/patched controls,
original same/wide-NDR counterexamples, patched mixed default/NDR branches,
different widths, vias, default RECT patches, explicit/truncated endpoints,
fixed wires, and expected pre-GC rejection of unsupported/ambiguous/unmatched
or empty routes. Supported cases preserve complete NETS/SPECIALNETS/NDR DEF
sections. Each worker verifies its actual ELF and adapter hash before import.
The original and patched binaries are respectively
`e4dc26d72e918ca25f01645194337999cf9720fa06fbd8d358dfca6440a32f2c` and
`93e1037e3ff63166f021580fd6826f66f92274f07e0051a80e9024ffb182e0b8`.

The real P2 ordinary `end_iter0` control passed in **207.232 seconds**. Its
pre-GC audit matched all **517,384 route objects on 28,948 nets**, including
42,147 patches, with zero mismatches or ambiguities. It retained default/TAPER
state on 29 segments and 30 vias across the ten NDR nets. Complete before/after
NETS and SPECIALNETS tokens, including per-path rules, matched exactly.
Independent inventory, netlist, master/OBS, technology/via, layer-use and PG
checks passed; protected/reference inputs remained unchanged and the owned
container was absent after completion. This is not byte identity of all ODB
metadata.

That geometry-preserving control still reports **22,115 native violations**:
15,494 metal shorts, 119 cut shorts, 6,497 metal-spacing and five cut-spacing
violations. Its changed marker count versus the broken-import control is not
a physical-routing improvement. Full-native counts take precedence over
category-capped marker reports. Independent all-terminal connectivity, fresh
detailed-route STA, DRC/LVS, GDS and official precheck remain separate gates.

| Retained evidence | SHA-256 |
|---|---|
| [Build05 owned receipt](../../build/physical/tt-overnight-taper-tools-01/jobs/build-05/report.json) | `f8cc502342d29f2b69048b013b7803d91014a5be7e1b95dbbcc353874880b7aa` |
| [Native build](../../build/physical/tt-overnight-taper-tools-01/jobs/build-05/native-05/build.json) | `698d986cb0a438d285529c6792b7c5127ca69607fbc934b1dc58f83fa9567f56` |
| [Fixture06 owned receipt](../../build/physical/tt-overnight-taper-tools-01/jobs/regression-06/report.json) | `dbb8e8b49c167130a9c53c3884eba02a64477827f0e0cd76053613b927537db7` |
| [Twelve native fixtures](../../build/physical/tt-overnight-taper-tools-01/jobs/regression-06/results/regression.json) | `692cd90fe06bff2f04b1cbeabe3b48d3e3d3d4dc4af947b84027f47493da5ba9` |
| [Real-P2 owned receipt](../../build/physical/tt-overnight-campaign-20261015/runs/p2-control-01/report.json) | `bd9e11c92acbb252a1d046decbdd26183e2a69358e5979f88e5f5489c05db423` |
| [Real-P2 adjudication](../../build/physical/tt-overnight-campaign-20261015/runs/p2-control-01/adjudication.json) | `ec10022831c73a073b7242a4ecdf1388f5bbfac8601eb175e9aa1554aca82e1f` |

Earlier missing-header, fixture setup and endpoint-serialization failures
remain in their original directories. The repaired code uses new tool and
generated-source versions; historical chip checkpoints and completed native
job receipts remain unchanged.
