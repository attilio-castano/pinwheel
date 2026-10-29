# Actual OpenRCX M1 capacitance diagnostic

This is a distinct four-call diagnostic, prepared on HOST and not executed.
It measures the exact owned TYP draft table through the pinned OpenRCX consumer.
It cannot qualify a full CMOS5L model, process corner, final layout or timing.
The older resistance consumer, its failed unit receipt and its unit-correct
adapter remain unchanged. Root alone admits Native after source review/commit.

The prepared owner is
`build/campaigns/8x4-20261022-01/rc-consumer-cap-preparation-01`; its plan SHA256 is
`abc8418dab6fe1b93873861078bfad540017be3436dc951bbc75a5da5a496bf2`.
All paths below are relative to that campaign unless otherwise stated.

## Source and capacitance semantics

The new `rc-cap-source-intake-01/manifest.json`, SHA256
`b1153b7d16122858298d562973b8ce49a8ccccdb7c7bfda17e452cfb641fcc7b`,
retains four primary files with byte lengths, SHA256, independently recomputed
Git blob identities and source URLs. Downloaded source was read as data.

At OpenROAD `dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`:

- [`extSpef.cpp`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/rcx/src/extSpef.cpp#L668),
  blob `f51d421ace60749dd72caf639c3e49772cad319b`, adds full incident coupling
  to the ground capacitance in each D_NET total. Lines 1199–1204 write both
  source and target coupling lists, so a coupling appears in both net blocks.
- [`extSpef.h`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/rcx/include/rcx/extSpef.h#L346),
  blob `41f94588edce5e0907013b8f24eb2b8a94f1e734`, defaults to multiplier 1
  and symmetric coupling. The writer defaults to FF, emits PIN_CAP NONE and
  uses six-significant-digit `%g` values; its optional PF path multiplies raw
  fF by .001. The parser reads the actual positive C_UNIT factor and FF/PF.
- [`dbNet.cpp`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/odb/src/db/dbNet.cpp#L1940),
  blob `872073f28514704245471c8836b1e1dec9de954c`, sums incident coupling
  values without halving them.

The retained consumer source intake pins OpenRCX.tcl/ext.i/extmain.cpp at that
same revision. OpenRCX.tcl passes the explicit coupling threshold to extraction;
extmain.cpp:687 grounds a signal coupling only when it is strictly less than
that threshold. The pinned OpenSTA
[`check_positive_float`](https://github.com/The-OpenROAD-Project/OpenSTA/blob/857316ff001b2a8dbbdc5996944d08a6d38c87ab/tcl/Util.tcl#L345)
accepts zero; its retained blob is `ad47cdce2ebeed4738cbbd2ceb4bdac2e115482c`.
The fixed new policy is therefore version 1.0, coupling_threshold 0, cc_model 10,
context_depth 5, no_merge_via_res, no lef_rc and no lef_res. Every positive
computed coupling survives the threshold operation. These flags do not revise
the canonical final-target timing diagnostic's policy.

Readback requires a unique complete set of expected nets, two ports per net,
connected physical resistor graphs and complete supported CAP rows. Grounded
rows contribute G_i. Each unordered coupling segment must have exactly one
equal copy in each endpoint net block; duplicate, missing or unequal mirrors
reject. After deduplication, K_ij is counted once globally but contributes its
full value to each incident D_NET. Reconstruct C_ii = G_i + sum_j K_ij and
C_ij = -K_ij. Check every D_NET against its ground plus full incident coupling,
using only an explicit sum of the writer's six-digit rounding intervals. This
format allowance is separate from the physical comparison tolerance.

## Physical geometry and four fixed calls

Bind unchanged reference04 SHA256
`185bac5e2f4346aeb03ebda83b827e7fb0336ffbc51c8a0a46f24b4b72aa910c`
and native06 SHA256
`6ea3613a03b2c29b8706da76d02e5a4f67ae2f5dc6ff55ddfe5cc1e27b418cc4`.
The exact reference cases are `TYP-w.16-self` and `TYP-w.16-s.18`, retaining
their complete TYP ITF dielectric stack and M1 z = 1.04–1.46um. The reference
transverse x coordinate maps to DEF y; extrusion maps to DEF x. The new plan
checks the exact rectangle bounds and complete material rows rather than
matching only a case label.

Each call contains three separated length groups at 50/100/150um. The self
case has one default-width .16um M1 wire per group. The pair has two such wires
with .18um edge spacing and .34um center spacing. All coordinates are exact
integers at the actual LEF's 1000 DBU/um. There are zero standard cells, ITerms,
routed vias or other metal contexts. Two ports terminate each wire; no Liberty
or cell pin loads are loaded. Native inventory and written DEF geometry must
confirm those facts and remain unchanged by extraction.

| Call | Physical case | Group separation | Outer padding |
| --- | --- | --- | --- |
| self-isolation512 | TYP M1 isolated wire | 512um | 32um |
| self-isolation1024 | same cross section | 1024um | 64um |
| pair-isolation512 | TYP M1 parallel pair | 512um | 32um |
| pair-isolation1024 | same cross section | 1024um | 64um |

No coupling outside an intended same-length pair is permitted. Separation and
padding changes form a **fixture spacing/isolation control**. They are not a
physical finite-ground or dielectric-boundary experiment. OpenRCX consumes an
implicit substrate/context model; its DEF outline does not supply the grounded
FVM box or finite BEM ground slab.

Compute complete Maxwell and ground slopes from 50→100 and 100→150um. Their
maximum cellwise relative difference must be at most 5%; the two spacing
fixtures' corresponding slopes must differ by at most 2%. The 150um group is
necessary because two lengths alone cannot support two successive slopes.
Each full slope matrix and its ground row sums must be physical; matching one
diagonal cannot hide incorrect coupling or ground capacitance.

## Independent accuracy and execution boundaries

The Native packet reports measured capacitance and consumer controls. Its
`passed` means only all four calls and those controls closed. It always records
accuracy as unmeasured and model_qualified false. The HOST reopener reports
physical accuracy separately. With no actual reference packet it explicitly
returns unmeasured, never a pass.

To assess accuracy, supply the actual complete layered Native directory,
reference directory, geometry/runtime owners and independent layered pass
receipt. Recompute the unchanged full H.analyze/read_reference results from
their raw files and require equality to that receipt. This preserves the
original 2% reference mesh/domain, two-successive BEM mesh, 5% BEM length,
2% BEM ground-extension and 10% BEM/reference gates. No successful prefix or
single conditioning point supplies those prerequisites. Compare each actual
OpenRCX Maxwell element and ground row sum against the matching fine .02um/E32
independent FVM reference, with maximum relative error at most 10%. Coupling is
an explicit off-diagonal comparison. Any failed prerequisite or physical
comparison remains visible; these nominal cases do not qualify wider wires,
other layers, corners or foundry process accuracy.

The fixed budget is four fresh 30-second OpenROAD calls, 150 seconds work and
180 seconds outer time, one CPU, 2GiB total memory including 128MiB scratch,
no extra swap, offline/read-only input and source mounts in pinned CAD image
`sha256:5825633bea1f9cbc705ece2de2bc31de6e4ec83d233739205a0f265ef9d92f92`.
The whole packet preserves numeric failures and proceeds only through its
fixed four calls after each process is reaped and copied inputs are checked.
No adaptive retry, model fitting or standard-cell timing occurs.

The HOST reopener reparses all raw outputs, copied sources, geometry and
numeric failures, then joins the exact Root command proposal to the resource
receipt's input seals, actual exit, empty process/container lists and cleanup.
Eight focused normal and optimized-Python controls currently pass. No Native
measurement exists for this preparation.
