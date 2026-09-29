# SRAM provenance and the component trust boundary

The supplied memory views belong together. All seven files used by the retained
chip, plus the simulation model's shared behavioral dependency, match the
**same pinned IHP release**. The 0.260 µm schematic / 0.200 µm physical marker
disagreement already exists in the original 2023 release. Mixing library
versions does not explain it.

**Decision:** prepare an explicit external-component contract so conditional
formal work can advance. Internal memory qualification remains an independently
named obligation. The [contract](../../physical/fixtures/sram-trust/contract.json)
is a reviewable proposal, not an implemented admission rule. A, B and full GDS
signoff retain their previous status. No chip, supplied view, installed PDK or
Lean proof changed.

The [manifest](../../physical/experiments/sram-trust-results.json) binds the
[protocol](sram-trust-experiment.md), source captures, native experiments and
[reproduction notes](../../physical/fixtures/sram-trust/README.md). The
[maintainer report](sram-maintainer-report.md) is prepared and **unsent**.

## Provenance and outside evidence

The seven views are GDS, CDL, LEF, macro Verilog and slow/typical/fast Liberty.
Their Git blob identities match the complete PDK tree at
`2bbec755dc67ca3db0261c3d6163e15735d66710`. The shared behavioral Verilog matches
too. The release's
[CMOS5L SRAM library is an explicit alias to the SG13G2 SRAM library](https://github.com/IHP-GmbH/IHP-Open-PDK/blob/2bbec755dc67ca3db0261c3d6163e15735d66710/ihp-sg13cmos5l/libs.ref/sg13cmos5l_sram).
This establishes intended library reuse; it is not a signoff certificate.

Independent KLayout measurement of the original December 2023 GDS finds the
same three 0.200 × 0.600 µm bit-cell markers. Both original and pinned CDL use
0.260 × 0.600 µm. The captured default-branch GDS/CDL also match our bytes;
that captured head predates our pin and is not called a newer release.

IHP's [issue 239](https://github.com/IHP-GmbH/IHP-Open-PDK/issues/239) provides
useful context. A maintainer
[reported commercial-tool SRAM LVS success in November 2024](https://github.com/IHP-GmbH/IHP-Open-PDK/issues/239#issuecomment-2451952732),
separately from open-tool problems. Another contributor later reported passing
setups for a 512×32 variant; the August 2026 discussion still concerned sharing
those scripts. None of the captured discussion gives the exact width rule or a
qualification report bound to our 512×64 CMOS5L inputs.

The linked Tiny Tapeout example's
[March 2026 configuration](https://github.com/urish/ttihp-sram-test/blob/efca7b356e5df69fc9caa6bacb7b6c224a7001b1/src/config.json)
uses `MAGIC_EXT_ABSTRACT_CELLS: ["RM_IHPSG13_.*"]`. That revision replaces an
LVS-error waiver with macro abstraction. It separately disables the Magic DRC
error gate, KLayout DRC and XOR. Its workflow uses SG13G2 and LibreLane
3.0.0.dev52, while our pin uses CMOS5L and 3.1.0.dev3. It specifies a 1024×8
macro, and does not request GDS extraction. The captured 2024 configuration
uses another flow; the 2026 policy must not be attributed to the earlier
[silicon example](https://www.tinytapeout.com/chips/ttihp0p2/tt_um_urish_sram_test).
We did not copy these error-gate settings into Pinwheel.

The separate [Magic discussion](https://github.com/IHP-GmbH/IHP-Open-PDK/issues/794)
describes hierarchy-sensitive import. An early explanation involving shorted
metal resistors was subsequently corrected by its author to a corner-cell
diffusion interpretation. It is not evidence for normalizing our widths.
The captured [lvsres proposal](https://github.com/IHP-GmbH/IHP-Open-PDK/pull/1121)
is still unmerged and explicitly lacks Magic updates. We applied none of it.

## What abstraction actually checks

The native extraction script sets `LEFview true` on matching cells. Our probe
uses the unchanged supplied **GDS**, which is stronger input fidelity than the
reference's default DEF/LEF route, but is not a replay of that reference flow.
It emits an empty 351-terminal macro definition. Forty-seven imported cell
names match the reference regex. Unreachable internal definitions remain in
the output file; their presence does not provide internal comparison coverage.

| Bounded diagnostic | Result | Meaning |
| --- | --- | --- |
| GDS abstraction | 351 macro terminals, no internal device lines | Interface retained; internal circuit omitted |
| Native boundary comparison against independent CDL/LEF interface | Unique match | All terminals can be compared after a checked spelling bijection |
| Address connected to ground | Native pin mismatch | Signal connection error detected |
| Ground connected to power | Native pin mismatch | Power connection error detected |
| One internal CDL width changed in a diagnostic copy | Same projected source; still matches | Demonstrated absence of internal coverage |

The comparison fixture contains one macro with independent external terminals.
It is not the whole chip. The earlier actual-chip boundary comparison and its
two fault controls are retained and their evidence hashes revalidated.

Native abstraction still reports **23 illegal overlaps and 518 conversion
diagnostics**. These remain failed internal evidence. Merely enabling the
reference option does not produce clean extraction. The initial probe stopped
before extraction because the native step requires a DEF input even in its
GDS branch. The second probe supplies the retained DEF, unused by that selected
Tcl branch; no native extraction script is changed.

## Formal and physical obligations

The proposed digital contract has 512 words of 64 bits, a rising-edge read,
full-word writes that hold Q when read-enable is off, and idle state retention.
Memory and Q begin arbitrary. It requires fixed normal mode, full write masks,
`A_DLY=1`, and correctly bound supplies. Concurrent read/write is excluded from
this restricted contract; the supplied model implements write-through in that
mode. Timing and safe observation after the edge remain explicit premises.

The existing [array proof](../../Pinwheel/Hardware/Memory/Sram.lean) is a model
proof, and its replicated hybrid composition must not be relabeled as the
complete paired-controller proof. The actual
[paired binding checker](../../scripts/paired_mapping.py) already checks the
normal-mode connections. The next formal deliverable is correspondence for the
paired controller, loader and package **under the memory contract**, including
mode exclusion and initialized reads. No new global Lean axiom is proposed.

Physical acceptance requires evidence for the exact component/version and
permitted environment: a supported vendor/organizer qualification route or
independent internal verification. Resolve the width convention before changing
the strict tile interpretation. Fast-library compatibility, package power
qualification, complete timed refinement and clean-source replay remain open.

## Accounting and validation

Three offline pinned invocations consume **21.779 CAD seconds**, including the
failed first probe and cleanup. Campaign total is **8,412.163 seconds / 140.20
minutes**, within the eight-hour allocation. No additional full route occurs;
three A attempts remain used and two B attempts reserved.

The provenance audit initially selected both one-port and two-port historical
bit cells and refused. Its retained correction selects the exact one-port
definition. One public fetch ended with a 404 for a guessed README path; a new
capture obtained the actual pinned macro documentation. These failures and all
successful capture bytes remain recorded. The manifest retains source/artifact
hashes, native results and cleanup. Raw ignored outputs are required to audit
these receipts; the tracked scripts alone do not make a clean-source replay.
