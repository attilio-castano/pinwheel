# Streaming Tiny Tapeout campaign morning report

**Campaign closeout, 2026-10-18. The mandatory milestone was not achieved.**
The final routing attempt timed out without a completed routed database, and
complete implemented-device correspondence remains open. Compiler work stopped
at the fixed 14:25 UTC cutoff. The results below preserve successful validation,
failed attempts and the remaining obligations; this design is not tapeout-ready.

The objective is a standard-cell-only Tiny Tapeout CMOS5L **6×4** implementation
of the programmable streaming device: its 64×64 program bank, two-word TX/RX
queues, long duplex SPI, JTAG, reactive I²C, autonomous single-frame UART and
host contract. The required comparison is **20 ns**, with max/min I/O delays
of **4.0 / 0.2 ns**, **0.2 ns** clock uncertainty, buffer-2 input drive and
**10 fF** output load. These requirements were retained throughout.

Campaign launch: **2026-10-18 02:32:27 UTC**. Last candidate launch cutoff:
**11:32:27 UTC**. Hard deadline: **14:32:27 UTC**. Baseline:
`787260b07c7dffc06799feeee6fd604e0b290fe7`. Branch:
`codex/streaming-tt-candidate`. Work and incremental commits are local.

## What the campaign has established

The optimized mapped implementation preserves all **6,039 state bits** while
sharing combinational work. Its mapped cell area fell from **717,340.9194**
to **606,637.1178 µm²**, a **15.43%** reduction. Combinational cells fell from
28,415 to 22,963; the longest unweighted combinational gate path fell from
127 to 114 gates. These are mapped implementation costs, before physical clock,
fanout and timing repair. They are not final routed area or timing results.

The optimization source is `f8018c5168d683ae0c11f4123a290ee5dc774e6c`.
Its raw native gate, full device correspondence, 392-module frozen replay and
unused-private-axiom rejection have separate retained receipts. The original
streaming source definitions remain unchanged; the new physical proof library
and generators extend their implementation correspondence.

A complete public-wire diagnostic passed on the exact closed **07 global-route
database**, SHA-256
`039d396596297963041ef641dcbf246fbcbe0bebd6cd4a6c5c506cb8e340e831`:
**35 positive cases plus one sampler mutant, 14 native bridge runs and two
compiles, and 513,297 total physical clock edges** (509,678 positive edges
and 3,619 mutant edges).
The corpus includes 4 KiB continuous-CS duplex SPI, 4,097-bit JTAG, 64-byte
reactive I²C and all 24 UART cases, including the actual sampler FF D-pin
mutation. All 41,239 actual instances and 6,039 FFs were retained;
the simulation did not contract the clock tree. This is finite zero-delay
Liberty-function simulation; it does not establish extracted timing or
universal state-transition correspondence.

The same closed database has freshly exported Verilog, powered Verilog, CDL,
LEF, DEF and diagnostic GDS views. Its GDS has the exact official
**1289.28 × 710.64 µm** outline, a four-corner `prBoundary` rectangle on
189/4 and all **43** public pin rectangles and labels at their exact official
template locations. GDS units and precision are 1 µm and 1 nm. These geometry
observations do not complete the official nine-check precheck or prove routed
connectivity.

## Physical progress and measured failures

The standard-cell PDN connects adjacent Metal1–Metal4 layers, with no
TopMetal1 drawing. Placement, CTS and global routing have actual native
receipts. Fresh three-Liberty-corner timing on the closed 07-equivalent
database, using nominal LEF RC estimates, measured:

| Liberty corner | Setup slack (ns) | Hold slack (ns) |
| --- | ---: | ---: |
| Fast, 1.32 V, −40 °C | +8.723964 | +0.030567 |
| Typical, 1.20 V, 25 °C | +5.137016 | +0.108997 |
| Slow, 1.08 V, 125 °C | **−1.533174** | +0.235785 |

The slow corner has **161 setup violations**. Capacitance, slew and hold
violations were zero in this measurement. Fanout violations remain:
**392 CLOCK and 18 SIGNAL**. Logical power-pin connectivity covers
**82,478 terminals**; it does not establish analog supply or IR-drop closure.

Detailed-route attempt **07r1** ran for 2,713.63 seconds including cleanup and
timed out with input hashes unchanged and its owned container absent. The
router was still reducing violations: the final partial iteration reported
119. It produced no completed detailed-route state. Partial log counts are
not accepted DRC results.

The native fanout transformation partitions loads with **650 positive,
equal-master clones**, preserves all 41,239 original instances and 6,039 FFs,
and verifies exact connectivity after native legalization and ODB write/read.
The preflight had no clock or signal load above eight. The placement cost was
material: 15,911 original cells moved, the maximum displacement was about
179 µm, and HPWL rose by about 20%. Subsequent native repair can reopen
fanout, so its final inventory must be measured independently.

The planner partitions loads by deterministic identity and initially places
clones at their source buffer's occupied location. Spatial grouping and legal
initial clone locations are concrete hypotheses for reducing this placement
and routing cost while preserving the same positive-buffer topology. Neither
has been physically validated in this campaign.

Attempt **08r2** passed the transformation but failed native post-CTS
legalization after setup repair and insertion of 162 hold buffers.
Attempt **09** explicitly expanded the legalizer search from 500/100 to
1500/800 µm in X/Y, keeping all physical and timing checks. Legalization then
passed. Global routing failed congestion after 50 overflow-removal iterations,
with final overflow 10,018. The last closed 09 state is post-CTS; its typical
timing result is a separate unrouted observation and does not replace the
three-corner or routed timing obligations.

A fresh native readback of that closed 09 post-CTS state, ODB
`32c8d12ca07502b39d9d2dde1d28a7c391dbef2d5c607ba2ccf05ef9b537a184`,
independently confirms all 6,039 original FF identities/functions, positive
FF clock polarity and inactive async reset. Every clock and signal load is
at most eight, including the 136 passive diode cells. Logical rail checks
cover 84,104 power terminals in 42,052 instances. There are 813 added cells
(650 clones, one setup buffer and 162 hold-delay cells), 13 resized cells and
no removed originals. These are source-bound host graph measurements, not
a kernel correspondence proof, routed electrical result or IR-drop result.

The last candidate, **07r2**, started actual native detailed routing at
**11:31:52.698 UTC**, before the cutoff. It uses the original 07 database,
unchanged constraints and full native tail, with a 4,200-second bound.
It timed out with exit 124 after **4,212.718 seconds**, including cleanup.
The last completed iteration reported **17 violations**; that is a partial
router observation, not a completed DRC result. No `state_out.json` or usable
final routed database was produced. All 50 frozen producer files and prepared
inputs remained unchanged, the runtime matched its pin, the owned container
was absent and the CAD lock was removed. No candidate was launched after the
cutoff. Final diagnostics therefore use the explicitly selected, closed 07
global-route database `039d3965…`.

The full finite public-wire corpus also passed on the repaired 09 post-CTS
database `32c8d12c…`: the same **35 positive cases plus one sampler mutant**,
**14 bridge runs and two compiles**, and **513,297 total physical clock edges**.
All 42,052 actual instances and 6,039 FFs were retained without clock-tree
contraction. Its source, input, generated-file and runtime identity checks
closed unchanged after 1,264.21 seconds. This is a second digital diagnostic
on an unrouted state; neither diagnostic supplies a final routed netlist.

## The timing uncertainty is now localized

This decomposition uses the slow-Liberty, nominal-LEF-RC diagnostic on ODB
`039d3965…`; it is not a routed/extracted delay measurement. Its worst path is
mapped exactly from `core-d2:r_tx_accepted:0`
(`engine.core._3359_`) to `frontend:r_export_data:15`
(`engine.frontend._1781_`). It contains **116 combinational cell arcs**.
Their delays total **20.406569 ns**, versus **0.251509 ns** of net delay,
excluding launch clock-to-Q. The path is predominantly logic depth.

Two ripple arithmetic cones account for **2.760779 + 4.067024 ns**.
A **64-gate serial AND guard** accounts for another **8.733741 ns**.
The source `tailCanonical` definition uses a left fold across 64 payload
conditions, matching this physical chain. A balanced implementation is a
concrete next optimization target with the same logical contract. Its actual
timing benefit and newly exposed worst paths require a new proof and physical
attempt; no predicted speedup is accepted as a measurement here.

The native clock inventory also contains **577 positive and 226 negative
internal clock-dependent nodes**. Every observed FF clock is positive. All
226 negative outputs and another 110 positive outputs are unused; these 336
branches remain in the full inventory. The proof obligation is complete
internal polarity accounting together with positive polarity at every FF
root. The native inventory observation alone is not its kernel certificate.

## What the native layout checks found

All measurements in this section use the selected **GRT-only diagnostic**;
they do not supply a completed routed artifact. Fresh native exports and
three-corner nominal-RC STA reproduce the earlier database and timing results.
Consumed timing nets are fully annotated; 468 unannotated drivers are unused.

The full antenna deck completed all **23 expected categories with zero
violations**. The final unchanged official Tiny Tapeout precheck executed all
**nine checks**, including three native KLayout processes: **seven passed and
two failed**. Inputs, PDK and runtime identities closed unchanged and every
owned native container was absent after cleanup.

The official DRC reports **2,496 violations**: **2,494 NW.b** minimum
same-net NWell spacing/notch items and **two M4.b** Metal4 spacing items.
The selected state precedes filler insertion; filler completion might change
the NWell result, but that is an unvalidated hypothesis, not an accepted repair.

Pincheck reports **399 actual errors**: 132 wrong-layer, 104 too-small-width,
80 too-far-from-top, 80 too-far-from-bottom and three overlap errors. These
largely concern the two exported power-port abstractions. The separate exact
GDS geometry observation covers the **43 public signal/control pins**, not
those two power ports. In particular, full-height Metal4 ground stripes
cover these entire public pin rectangles:

| Public signal | Pin rectangle, µm | Ground stripe X range, µm |
| --- | --- | --- |
| `ui_in[3]` | (167.85, 709.64)–(168.15, 710.64) | 167.45–169.55 |
| `uio_out[5]` | (68.01, 709.64)–(68.31, 710.64) | 67.45–69.55 |
| `uo_out[0]` | (117.93, 709.64)–(118.23, 710.64) | 117.45–119.55 |

Each ground stripe extends from Y=0 to Y=710.64 µm. Independent native LVS
extraction merges the same three signal names with `VGND`. Logical ODB power
net-name checks do not detect this geometric short. The next physical attempt
must make the PDN clear the fixed public pins and provide legal boundary power
ports; no candidate geometry was changed after the launch cutoff.

Two earlier official attempts exposed formatting incompatibilities in the
unchanged official LEF parser: it left-pads short decimal fractions and requires
one space after `RECT`. The native LEF already declares the correct official
size. A new committed adapter preserves **all 1,844 exact Decimal coordinates**,
all 45 pins, geometry tokens, types and layers, while canonicalizing numeric
and geometry-whitespace spelling. Nongeometry lines remain byte-identical.
The final nine-check result above has no parser exception. Original LEF,
checker and failed attempts remain immutable; no physical error was waived.

Transistor LVS now has a complete, nonvacuous used-cell reference. A checked
composition preserves the ODB-derived top and exact pinned standard-cell CDL
bytes, verifying **41,239 instances and 204,066 terminal bindings**, including
336 distinct isolated unconnected terminals. The used hierarchy closes over
39 masters. The earlier zero-device reference and unused-I/O-library parser
failure are retained separately and excluded from valid comparison claims.

The unchanged full deck and strict reader completed with **288 primitive
definitions on each side**, but **39 leaf circuit pairs report NoMatch** and
the top comparison is **Skipped**. All 39 used GDS masters preserve their exact
pinned geometry and labels. Their 125 named local signal nets survive
extraction but have no outgoing hierarchy pins. This is consistent with missing
intercell connectivity in the unrouted geometry: KLayout documents that
intercell connections form subcircuit pins and that `simplify` also creates
top-level pins and purges nets. This is a source-supported interpretation,
not a completed-route LVS verdict. See the
[hierarchical extraction description](https://github.com/KLayout/klayout/wiki/Deep-Verification-Base#netlist-extraction)
and [Netlist API](https://www.klayout.de/doc/code/class_Netlist.html#k_19).

## Remaining acceptance obligations

| Gate | Checkpoint status |
| --- | --- |
| Original and optimized source behavior | Closed kernel/source-replay receipts retained; no physical qualification inherited |
| Actual netlist digital next-state/output/clock correspondence | Open: full actual transport and device/pad roots have not closed |
| Complete detailed route and native DRC | Open: 07r1 and 07r2 timed out without completed routed states |
| Qualified extracted setup/hold/electrical timing at 20 ns | Open; nominal slow setup fails, model scope also open |
| Native antenna and transistor LVS | GRT antenna 23 categories/zero violations; complete-reference LVS fails, top skipped; final routed checks open |
| Official TT nine-check precheck | All nine executed on GRT: seven pass, DRC 2,496 items and Pincheck 399 errors fail |
| Final routed-netlist public-wire corpus | Open: no final routed netlist; closed 07 GRT and 09 post-CTS corpora passed |
| Fresh complete foundation/Python/provenance validation | Foundation, Python, portable hosts and preservation passed; generated-family audit and retained-library compatibility remain open |

The pinned CMOS5L `RCX_RULES` resolves to an inherited seven-layer SG13G2
model. The candidate uses Metal1–Metal4, but that restriction alone does not
qualify vertical extraction context or RC corners. The
[extraction-scope note](streaming-tt-extraction-scope.md) records the exact
model SHA, [IHP draft PR #1237](https://github.com/IHP-GmbH/IHP-Open-PDK/pull/1237)
and OpenRCX calibration requirements. No draft model was substituted and no
nominal result is called minimum/maximum RC signoff.

The TT block's TopMetal1 drawing restriction and foundry full-chip density
requirements are separate assembly obligations. No forbidden fill or rule
waiver was introduced to force a pass.

## Validation, provenance and operational limits

The fresh committed Python snapshot at `efccdb3` ran **1,937 tests** successfully with
**13 explicit environment/native-fixture skips**. Four portable physical-tool
host suites passed **115 tests, zero skips**, with their guard self-tests, in
that same fresh archive without build artifacts or CAD execution. These do
not count as native physical signoff. The preceding failed snapshot is retained:
it exposed an unguarded native embedding test's assumption that a prebuilt
library and `build/` directory existed. The missing fixture is now an explicit
skip; genuine kernel mutation controls remain separate native obligations.

The fresh foundation archive at `e32a9ff` passed **648 library modules, eight
kernel suites, 65 executable suites and two independent oracles**. Its audit
covers **44,174 declarations and 25,119 theorems**. Public and compiled unused
private forbidden-axiom controls were rejected for the expected reasons. All
**793** inputs, including the snapshot driver, match the current `efccdb3`
commit and workspace bytes. The complete **1,297-file** retained library is
sealed for subsequent imports. The before/after identity observation covers
**14,923** compiler/runtime files; it does not prove official compiler archive
membership, a reproducible compiler build or the host operating system.

The front-end committed replay has passed all **806 generated modules**,
including 693 word proofs, 6,208 gate realization and all next/output
endpoints. The Core's bounded aggregate and all endpoints have closed, covering
**16,742 primitive cells**; the earlier monolithic aggregate timeout remains
preserved. The 183 Original parent modules and state codec have also closed.
Against the fresh foundation, **360 leaf modules, 43 front-end embeddings and
109 Core embeddings** have fully closed, including source/import/output and
process checks. The **662-module actual transport**, complete typed device
roots and all-24-pad correspondence have not closed. A seven-module join
replay failed its public-mask graph at the 6 GiB kernel memory limit; six
development join modules had compiled, but their success does not close the
seven-module stage. Earlier missing-import, dependent-width and Boolean
precedence failures and their repairs remain retained separately.

The clock replay compiled **89 of 90 modules**. A separately checked prefix
receipt preserves those 89 successful commands and their exact sources,
outputs and logs. The final module first exceeded memory on a whole-`Fin 6039`
proof; bounded chunks then exposed an aggregation coercion error. The last
repair reached the hard cutoff and timed out with its process group closed.
The **full 90-module clock block remains open**. The signed clock-inventory
module and supplemental typed step module were not executed. No complete
implemented-device correspondence is claimed.

The final whole-family private-axiom audit has not run because its complete
4,308-module prerequisites have not closed. The fresh foundation's audit
does not establish that larger generated-family audit. Genuine native fixture
controls did close: **three positive groups and five semantic mutations,
21 native processes**, covering a forged primary-input image, single clock
inversion and wrong constant/output/static premise. These are independent
controls, excluded from the 4,308 intended production sources.

The **392-module** original source replay is explicitly reused; **2,641**
additional modules closed earlier against retained library imports. All 648
retained library OLE hashes differ from the fresh foundation. The full-tree
declaration probe timed out after 120.778 seconds with no completion footer.
A lossless DAG replacement passed host controls and static review but has not
run natively. Retained-library declaration compatibility remains open; those
**3,033** modules were not freshly rebuilt against the final foundation.
Intermediate prefix passes and prepared probes are not completion receipts.

Native Tcl failures require literal successful `catch` status, not Python exit
zero alone. Positive and deliberately failing placement, clock, connectivity,
antenna and LVS controls are retained independently. Earlier integration
failures remain immutable and excluded from acceptance.

A machine reboot occurred at **04:29:11 UTC** after severe memory pressure;
the campaign resumed near 09:59 UTC. Roughly 5.5 hours of campaign wall time
were lost, without extending the deadline. The earlier SPI worker's −9 result
predated the reboot and is not attributed to it without evidence. Recovery
uses one heavy native job at a time and one memory-bounded Lean process.

All **112** prior research files checked against baseline Git bytes match,
including **90** evidence files and four prior morning reports. Both
intake-dirty documents and their combined binary diff retain their exact
original hashes. They remain outside campaign commits. Shared PDK inputs,
failed attempts and historical reports are preserved.

## What happened to the initial uncertainty

The implementation now has a measured 15.43% mapped area improvement and two
complete actual-netlist public-wire test corpora. Those observations support
continuing with this design, while leaving final routed area and universal
implemented-device correspondence as separate obligations.

Physical uncertainty has become specific. The fixed public-pin geometry is
correct, but the power grid shorts three pins. Nominal slow-corner timing
misses by 1.533174 ns, with a measured long serial guard cone. Routing and
fanout repair compete for placement space and wiring capacity. These are
concrete design problems; the measured failures do not justify a tapeout-ready
claim.

The next physical campaign should first make the grid clear all public pins
and expose legal boundary power ports. It should then test balanced guard
logic and spatially grouped buffer clones, retaining exact functional and
state correspondence for each change. Qualified RC models, a completed
detailed route and the full routed signoff checks remain required. These
repairs and their physical effects have not been validated by this campaign.

## Closeout evidence

Validated code commit: `efccdb3f76ae745ad733b4af6106142516546961`.
The [evidence manifest](local-evidence/README.md#artifact-2d25b4fed8e3) indexes
**6,058** selected receipts, logs, views and supporting sources. Its archive
contains **4,308 intended positive Lean sources** with explicit execution
statuses: **3,545 closed-evidence modules** (3,033 retained and 512 fresh),
**95 individual successes in incomplete aggregate attempts**, **two failed
modules** and **666 unexecuted modules**. “Positive” describes intent, not
successful execution or qualification. The
[independent packet check](evidence/streaming-tt-20261018-postcheck.json)
verifies exact membership and compressed-byte/source-archive roundtrips;
it grants no proof or physical acceptance. The mandatory goal remains incomplete.

Failed and unexecuted preparation helpers are historical artifacts. In
particular, clock retry04's `prepare.py` stopped on an existing-directory
collision before modifying Lean sources; it is excluded as the producer of
that executed retry. Its actual source bytes are bound by the separate
source-repair and native-source seals.

For a source replay, use a separate checkout of validated code commit
`efccdb3f76ae745ad733b4af6106142516546961` and new output tags:

```sh
python3 -B scripts/check-python-snapshot.py --tag streaming-tt-python-replay
python3 -B scripts/check-foundation-snapshot.py --tag streaming-tt-foundation-replay --serial-build --retain-snapshot --timeout-seconds 6000
```

The receipts retain native commands, exact inputs, tool/model hashes and
individual stage boundaries. Repeating physical or generated-proof runs also
requires the referenced native databases, compiler libraries and pinned tools;
the curated packet does not supply those large binary dependencies. Successful
decompression or source replay alone does not reproduce physical acceptance.
