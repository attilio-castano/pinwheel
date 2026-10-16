# Tiny Tapeout buffered SRAM boundary

The `tt_um_pinwheel_buffered` top places the existing reloadable buffered SRAM
serial engine behind the standard Tiny Tapeout ports. The serial packet ABI,
controller, instruction format and two 64×64 instruction replicas are unchanged.
The same circuit accepts different uploaded SPI, JTAG and I²C programs.

**Latest physical result, 2026-10-16:** the [overnight campaign](../physical/tt-buffered-overnight-campaign.md)
retains C14 as a routing reference with **1,732 native DRC records versus 22,115**
in the matched control. The longer C17 run regresses to 2,511. RTL and serial
ABI remain unchanged; cells, placement, SRAM/PG geometry and clock topology were
frozen while route geometry could change. C14 still fails public GDS DRC
(4,053 records), boundary LVS, antenna (124 nets / 135 INPUT contacts), and
conditional extracted timing (−7.353613 ns slow setup / −23.768 ps fast hold).
Official TT precheck was not run. The [tracked manifest](../../physical/experiments/tt-buffered-overnight-campaign-results.json)
owns measurements and custody; the [next experiments](../research/tt-buffered-next-experiments.md)
separate proposed repairs from acceptance. Earlier coarse comparisons below
retain their original dates and are not C14 extracted signoff.

## Public pins and initialization

| Tiny Tapeout port | Meaning |
| --- | --- |
| `ui_in[0]` | Host CSn |
| `ui_in[1]` | Host SCK |
| `ui_in[2]` | Host MOSI |
| `ui_in[3]`, `ui_in[4]` | Raw protocol inputs 0 and 1 |
| `uo_out[0]` | Host MISO |
| `uo_out[1]`, `uo_out[2]` | Serial response READY and engine BUSY |
| `uio_out[2:0]`, `uio_oe[2:0]` | Protocol output levels and independent enables |
| Other outputs/enables | Constant zero |

`ena=0` or `rst_n=0` immediately masks all output levels and enables. The
underlying engine initializes synchronously on a rising `clk` while either
control is low. After selecting the design, hold reset low for at least one
rising clock, then upload a fresh image before START. The SRAM arrays are not
cleared by reset; their old contents do not establish a valid uploaded program.
Deselection without a clock masks outputs but cannot invalidate internal state.
Reselection therefore always requires this reset-and-upload sequence.

Host CSn/SCK/MOSI obey the existing sampled serial schedule relative to the
free-running core clock. Digital replay does not qualify arbitrary asynchronous
host timing, metastability, pad delay, pull-up strength or analog bus behavior.
I²C testing resolves open-drain levels with external links and ideal pull-ups.
For the tested I²C programs, connect `ui_in[3]` to `uio[0]` for SCL and
`ui_in[4]` to `uio[1]` for SDA, with external pull-ups on both lines. The
uploaded program determines the protocol output roles; these two links are
part of that I²C board wiring contract.

## Evidence and reproduction

The focused gate checks the exact wrapper ports with functional vendor SRAM
models and independent serial/SPI/JTAG/I²C peers. It verifies retained emitted
frontend/controller artifacts against the accepted predecessor receipts and
checks the current implementation inputs. This establishes a finite new
boundary check; it does not rerun the predecessor's Lean proof gates.

```sh
python3 -B scripts/check-tt-buffered.py --tag <fresh-tag> \
  --artifacts-root <checkout-with-accepted-buffered-artifacts> \
  --cad-dir <oss-cad-suite-bin>
```

The physical preparation consumes a passing focused report, freezes all design
inputs, and uses the pinned official 6×4 DEF pin template. The bounded runner
admits only those frozen inputs and the pinned PDK/container. It permits one
offline run with at most four CPUs, 6 GiB and 1,800 seconds, then retains logs,
metrics and its stop reason. Physical feasibility, extracted timing, foundry
checks and competition submission remain separate gates.

**Historical fanout2803-only comparison: candidate rejected.** The [study](../physical/tt-buffered-fanout2803.md) and [result manifest](../../physical/experiments/tt-buffered-fanout2803-results.json) retain one exact buffer move from original repaired R0; fanout2903 stays at its original MX placement and all other instances remain unchanged. Native coarse overflow changes 5,840 → 5,955 (+115); zero-capacity overflow changes 3,328 → 3,415. Timing gate: True. Fresh native movement/power and finite mapped checks pass. Reject the single-buffer candidate; retain the original repaired R0 checkpoint. Accepted routing and submission signoff remain open.

**Preceding two-buffer comparison: candidate rejected.** The [study](../physical/tt-buffered-two-buffer.md) and [result manifest](../../physical/experiments/tt-buffered-two-buffer-results.json) retain one exact two-buffer move from repaired R0, with zero neighboring movement. Matched coarse overflow rises 5,840 → 5,944 (+104, +1.781%) and zero-capacity overflow rises 3,328 → 3,472. All three setup/hold margins remain exactly unchanged, including slow +1.00825 ns; existing electrical counts remain unchanged. Fresh native movement/power checks and mapped upload-to-pins pass 21 peers, 400 pairs and 336,426 zero-delay edges. Target input blocked-edge incidences fall 100 → 0, but other routes increase pressure. All scheduled work and cleanup finish within the 25-minute wall cap. Retain repaired R0; accepted routing and submission signoff remain open.

## Result, 2026-10-12

The [incremental access-placement study](../physical/tt-buffered-access-incremental.md)
and [result manifest](../../physical/experiments/tt-buffered-access-incremental-results.json)
own the preceding bounded comparison. One local legalization starts from the exact
timing-repaired post-CTS checkpoint and moves 42 bank-exclusive address-shell
cells (23/19 per bank), with no neighboring cells moved. Both SRAMs retain their
original N / OpenDB R0 orientation and footprints. All 28,920 other instances,
masters, net connectivity, clock tree, placement statuses, rows, blockages,
routing rules, pins and complete power geometry remain unchanged. Core RTL and
the serial ABI are unchanged; synthesis, global placement, CTS and repair are
not rerun.

The incremental candidate is **rejected**. Matched five-iteration routing
overflow rises slightly from 5,840 to 5,888 (+48, +0.822%). Slow setup falls
from +1.008250 to +0.990530 ns: a 17.72 ps loss, 9.47 ps below the unchanged
+1 ns target. Typical/fast setup, all hold margins and electrical violation
counts remain unchanged. The movement scope passes, but congestion improvement
and full timing preservation fail. Submission readiness remains false.

| Gate | Preceding incremental result |
| --- | --- |
| Core RTL and serial ABI | Unchanged; the accepted 495 boundary sources and 494 broader RTL sources remain source-matched. |
| Local movement and native producer | Passed in 12.944 s including staging and cleanup. Exactly 42 selected cells move, all to their frozen seeds; no other placement, master, connectivity, clock, status, row, blockage, NDR, macro, pin or power geometry change passes the gate. One native legalization and placement check run, with original statuses restored before checking and export. |
| Fresh SRAM power and TT pins | Passed in 12.882 s including staging and cleanup: VPWR/VGND connectivity, R0 footprints/supply contacts, unchanged complete grid and all 43 TT signal-pin shapes/placements. Independent native readback also verifies all 42 movement windows/displacement bounds, clocks, block/technology NDR rules and positive address-driver placement proxies. |
| Fresh mapped upload-to-pins | Passed in 112.911 s (113.005 s including wrapper closeout): 21 independent protocol peers, 400 request/response pairs, 336,426 finite zero-delay edges and three parser rejection controls. The fresh logical export matches the exact incremental ODB; accepted 495/494 sources and 507 protected inputs remain current. |
| Fresh estimated timing | Control and candidate pass three-corner collection; zero setup/hold failures. Typical/slow/fast slew counts remain 0/2/0, fanout violations remain 254 per corner, and capacitance violations remain zero. Slow setup misses both frozen preservation and +1 ns gates. |
| Matched coarse routing | Fresh control: 5,840 native directional overflow units; incremental candidate: 5,888. Both use five iterations per native segment, identical capacity and eight automatic clock-NDR fallback events. Neither congestion-allowed diagnostic is accepted routing. |
| Congestion maps | Both saved-database exports complete with unchanged routing input inventories/netlists. Native directional counts of 5,840/5,888 and saved preferred-grid counts of 5,831/5,868 are distinct representations. |
| Original native flow | The retained source flow remains failed with exit 2 and 30,396 inherited pre-helper power-grid violations. The successful scratch producer is a separate local placement gate; it does not relabel that flow or close its bookkeeping gap. |

| Library corner | Fresh repaired control setup / hold | Incremental setup / hold |
| --- | ---: | ---: |
| Typical, 1.20 V / 25 °C | +6.361640 / +0.164109 ns | +6.361640 / +0.164109 ns |
| Slow, 1.08 V / 125 °C | +1.008250 / +0.278249 ns | +0.990530 / +0.278249 ns |
| Fast, conditional | +9.588290 / +0.096047 ns | +9.588290 / +0.096047 ns |

Fresh STA uses the exact control and incremental ODBs with the same nine
libraries and constraints; no candidate timing metrics are inherited. Fast
combines −40 °C logic/I/O and −55 °C SRAM. The slow worst path shifts from SRAM0
address bit 2 to bit 5. Shorter cell-center-to-address-pin proxies do not
establish shorter total wiring or delay: native diagnostic wirelength rises
from 2,516,270 to 2,520,064 µm. Native zero legalization displacement describes
the already seeded positions; all 42 move relative to the repaired source.
This isolates one cohort's placement response, without identifying one cell's
individual contribution. Historical full-routing counts of 2,255/6,724 remain
separate. Accepted routing, extracted timing, complete electrical qualification,
DRC/LVS and official TT precheck remain open.

All seven physical commands, including fresh logical export, settle in 212.971 s.
Including the conservative 60 s host allowance charges 272.971 s against the
frozen 1,500 s physical allocation. Mapped replay uses its separate 300 s host
cap. This is one completed bounded
comparison, with no second placement candidate or full-routing attempt.

### Previous address-driver fence result, 2026-10-12 (retained)

The [address-driver placement study](../physical/tt-buffered-access-placement.md)
and [result manifest](../../physical/experiments/tt-buffered-access-placement-results.json)
retain the preceding bounded comparison. Both SRAMs retain their original N / OpenDB
R0 orientation and fixed footprints. One metadata step reserves two narrow
three-row fences for the twelve bank-specific address drivers before the
existing capacity-aware placement and native setup-then-hold repair. Core RTL,
serial ABI, `DELAY 1` mapping, constraints and complete power geometry remain
unchanged.

The fenced candidate is **rejected**. Its matched five-iteration routing
overflow rises from 5,840 on the exact timing-repaired control to 16,698,
a factor of 2.859. Fresh setup/hold estimates remain positive, but slow setup
falls from +1.008250 to +0.523787 ns, loses 0.484463 ns and misses the unchanged
+1.0 ns repair target. Typical/fast setup margins also decline, and typical/slow
slew violations rise. Submission readiness remains false.

| Gate | Retained fenced result |
| --- | --- |
| Core RTL and serial ABI | Unchanged; the accepted 495 boundary sources and 494 broader RTL sources remain source-matched. |
| Address-driver placement | All twelve drivers survive in the two exact six-member fences, with their direct SRAM address connections intact. The 26 control cells overlapping the reservations move or are removed. Native placement/repair changes 25,171 retained cell bounding boxes and 615 retained masters across the design; this is a whole-placement response to one policy. |
| SRAM power and TT pins | Fresh native checks pass both VPWR and VGND in 8.739 s including staging and cleanup. Original R0 footprints, 342 south-facing signal rectangles per SRAM, supply contacts, complete grid geometry and all 43 TT signal-pin shapes/placements match the retained reference. |
| Fresh mapped upload-to-pins | Passed in 122.036 s: 21 independent protocol cases, 400 request/response pairs, 336,426 finite zero-delay edges and three parser rejection controls. Fresh logical export matches the exact completed candidate ODB. |
| Post-CTS timing | Zero setup/hold failures at every screened corner. Typical/slow/fast slew counts are 7/7/0; each corner has 254 fanout violations and zero capacitance violations. Full previous setup margins are not preserved. |
| Native placement/repair flow | Completed the pre-routing checkpoint in 193.474 s, then exited 2 for 30,396 inherited pre-helper power-grid violations. Fresh connectivity passes separately; the native producer remains failed and its metric/checker bookkeeping gap remains open. |
| Matched coarse routing | Exact repaired control: 5,840 overflow units in 47.433 s; fenced candidate: 16,698 in 64.424 s. Both use five iterations per native segment and retain automatic NDR fallback, with eight events each. Neither congestion-allowed route is accepted routing. |
| Congestion maps | Both diagnostics complete their saved-database maps with unchanged routing input inventories/netlists. Native directional counts of 5,840/16,698 and saved preferred-grid counts of 5,831/16,599 remain distinct representations. |

| Library corner | Prior repaired setup / hold | Fenced setup / hold |
| --- | ---: | ---: |
| Typical, 1.20 V / 25 °C | +6.361640 / +0.164109 ns | +6.051610 / +0.166310 ns |
| Slow, 1.08 V / 125 °C | +1.008250 / +0.278249 ns | +0.523787 / +0.294673 ns |
| Fast, conditional | +9.588290 / +0.096047 ns | +9.392180 / +0.091947 ns |

Fresh STA uses the exact completed post-CTS ODB, reproduces its nominal result
and loads the same nine libraries and constraints. These are placement
estimates; fast combines −40 °C logic/I/O and −55 °C SRAM. The paired coarse
comparison holds mapping/repair/routing settings fixed, but native global
placement, CTS and repair respond throughout the design. It does not isolate
one driver's contribution. Its five-iteration counts do not replace the
historical 2,255/6,724 full-routing references. Extracted timing, electrical
qualification, accepted global/detailed routing, DRC/LVS and official TT
precheck remain open.

### Previous SRAM mirror result, 2026-10-12 (retained)

The [SRAM placement/access study](../physical/tt-buffered-sram-access.md) and
[result manifest](../../physical/experiments/tt-buffered-sram-access-results.json)
retain the preceding bounded comparison. Both SRAMs are mirrored vertically at their
unchanged footprints. Their 342 signal rectangles per macro now face north;
the complete supply wire, via and boundary geometry remains unchanged. The
core RTL, serial ABI, delay-oriented mapping, placement settings and native
setup-then-hold repair remain fixed.

The mirrored candidate is **rejected**. Fresh mapped upload-to-pins and both-net
power connectivity pass, but the matched coarse routing comparison worsens from
2,199 to 8,592 overflow units, a factor of 3.907. Setup and hold estimates remain
positive, while the full previous setup margins do not survive: slow setup
falls from +1.008250 to +0.509791 ns and misses the unchanged +1.0 ns repair
target. Electrical limits also regress. Submission readiness remains false.

| Gate | Retained mirror result |
| --- | --- |
| Core RTL and serial ABI | Unchanged; all 495 accepted boundary sources and 494 broader RTL sources remain source-matched. |
| Mirrored SRAM power | Fresh native checks pass VPWR and VGND in 8.860 s including staging and cleanup; exact MX footprints, reflected supply contacts and unchanged complete grid geometry are verified. |
| Fresh mapped upload-to-pins | Passed in 124.874 s: 21 independent protocol cases, 400 request/response pairs, 336,426 finite zero-delay edges and three parser rejection controls. A fresh export matches the exact candidate ODB. |
| Post-CTS timing | Zero setup/hold violations at every screened corner. Slow/typical/fast slew counts are 11/6/0; each corner has 249 fanout violations and zero capacitance violations. |
| Native placement/repair flow | Completed the pre-routing checkpoint in 206.720 s, then exited 2 for 30,396 deferred power-grid violations measured before the supply helper. Fresh grid connectivity passes, but the native flow remains failed; the metric/checker bookkeeping gap remains open. |
| Full routing benchmark | Fresh timing-repaired control and mirror diagnostics timed out after 190.335 s and 910.376 s respectively, without completed final counts/maps. The retained 2,255 older result and 6,724 timing-repaired result remain historical full-routing references. |
| Matched coarse routing | At the same five-iteration setting, older layout: 2,199 overflow units in 17.094 s; mirror: 8,592 in 51.192 s. Native automatic NDR fallback remains enabled (three/eight fallback events). No accepted route or signoff claim. |
| Congestion maps | The mirror's original probe receipt remains failed on its read-only exporter. Corrected readback of the saved routed ODB passes without rerouting, preserves cells/placement/netlist, and completes both comparison maps. Native directional overflow (8,592) and saved preferred-grid overflow (8,539) are distinct representations. |

| Library corner | Setup slack | Hold slack |
| --- | ---: | ---: |
| Typical, 1.20 V / 25 °C | +6.053730 ns | +0.220380 ns |
| Slow, 1.08 V / 125 °C | +0.509791 ns | +0.378489 ns |
| Fast, conditional | +9.416870 ns | +0.091653 ns |

These are fresh placement-estimated measurements on the completed post-CTS
ODB, with the same nine libraries and constraints. The fast screen combines
−40 °C logic/I/O and −55 °C SRAM. Positive estimates and finite zero-delay
mapped acceptance do not establish extracted timing, electrical qualification
or a completed layout. The full diagnostics retain the native 50-iteration
setting and automatic NDR fallback. After they time out, matched five-iteration
probes measure the same older and mirror checkpoints inside the remaining
allocation. These coarse counts are a separate comparison and cannot be
substituted for the retained 2,255/6,724 full-routing results. The older layout
also uses an earlier mapping/placement recipe, so this comparison does not
isolate the mirror as the sole cause of the measured congestion change.

### Previous locality result, 2026-10-10 (retained)

The exact TT wrapper and fresh repaired mapped upload-to-pins check pass. Fresh
post-CTS estimates clear the earlier twelve slow setup failures, but submission
readiness remains false: the locality candidate regresses global-routing
overflow from 2,255 to 6,724 and is rejected for routing. The
[locality study](../physical/tt-buffered-locality.md) and
[locality result manifest](../../physical/experiments/tt-buffered-locality-results.json)
own this decision. The
[previous corrected-power continuation](../../physical/experiments/tt-buffered-power-route-results.json)
and [first milestone](../../physical/experiments/tt-buffered-results.json)
retain their original evidence. Large artifacts remain under ignored `build/`
in this checkout.

| Gate | Retained October 10 result |
| --- | --- |
| RTL upload and lifecycle | Prior acceptance remains source-matched: 21 protocol cases, 598,566 clocked edges, 765 complete receipts and 19,890 status-field checks. |
| Corrected SRAM power | Prior native replay/readback passes six supply terminals, 136 die-edge columns and 29,172 enclosed via landings. A fresh check on the exact repaired ODB passes both VPWR and VGND connectivity in 5.982 s, with unchanged inputs and confirmed owned cleanup. |
| Placement and clock tree | Completed with unchanged core RTL and serial ABI; native setup then hold repair remains active. |
| Fresh post-CTS timing | At 20 ns, setup/hold slack is positive at all three screened corners; zero setup/hold violations. The slow corner has two slew violations; each corner has 254 fanout violations. Fast is conditional on mismatched logic/SRAM temperatures. |
| Repaired mapped upload-to-pins | Passed in 111.329 s: 21 independent peers, 400 request/response pairs, 336,426 finite zero-delay edges and three parser rejection controls. All 510 input hashes remain unchanged; a verified export matches the exact repaired ODB. |
| Bounded physical attempt | Initial GPL assertion after 147.496 s; one checkpoint continuation takes 1,062.927 s. Cumulative 1,210.423 s is below the original 1,800 s allocation; inputs unchanged and owned containers absent. |
| Global routing | Failed with 6,724 overflow units: Metal2 1,628, Metal3 4,068, Metal4 1,028. No completed new congestion map, accepted routed ODB or extracted signoff was produced. |

No controller, frontend, instruction or serial ABI change was made. The full
RTL oracle/lifecycle acceptance and 1,111-test Python receipt belong to the
first milestone; they were not rerun at the mapped layer. The mapped check
reuses the independent public-pin peers and confirms exact result parity with
the accepted boundary. It does not establish universal sequential equivalence,
SDF timing, asynchronous/pad behavior or SRAM electrical qualification.

### Retained timing gain and routing rejection

The frozen physical recipe uses delay-oriented synthesis and native feedback
from actual routing capacity. The initial full attempt stops at the pinned GPL
legalization assertion during virtual resizing. Its single continuation starts
from the exact completed pre-placement checkpoint, with `PL_TIMING_DRIVEN=false` as the sole
configuration delta. Synthesis, floorplan, macro placement and power generation
are skipped. Native post-placement and post-CTS repair, the 20 ns clock, I/O
constraints, corner libraries and SRAM power geometry remain unchanged.

A separate fresh diagnostic imports the exact repaired ODB and accepted SDC
with nine hash-bound libraries and unchanged native corner scripts. Its typical
setup/hold values reproduce the direct checkpoint measurements exactly:

| Library corner | Setup slack | Hold slack |
| --- | ---: | ---: |
| Typical, 1.20 V / 25 °C | +6.361640 ns | +0.164109 ns |
| Slow, 1.08 V / 125 °C | +1.008250 ns | +0.278249 ns |
| Fast, conditional | +9.588290 ns | +0.096047 ns |

Every screened corner has zero setup and hold violations. The fast screen
combines −40 °C logic/I/O and −55 °C SRAM. Two slow slew violations and 254
fanout violations at each corner remain. These are post-CTS parasitic estimates;
no extracted routed timing pass follows.

The same repaired ODB supplies the fresh logical export used by
`build/tt-buffered/netlist/tt-buffered-netlist-recovery-postcts-01/report.json`.
The mapped check preserves the exact TT bridge, reset/reselection contract and
accepted protocol peers. Its source closeout rechecks all 495 accepted boundary
sources and 494 full-RTL sources. This finite zero-delay functional pass does
not transfer timing or electrical qualification to a completed layout.

Routing reports 69.40% aggregate resource usage and 6,724 local overflow units,
versus the preceding 2,255. The physical recipe improves the measured setup
failure while worsening routing. The retained earlier congestion map informed
the candidate; the failed new route did not produce a completed congestion map
or accepted routed ODB. Detailed routing, extracted timing, power analysis,
DRC/LVS and official Tiny Tapeout precheck remain open.

A separate 5.982 s native check imports a byte-identical copy of this repaired
ODB and reports all shapes connected on both VPWR and VGND. Its retained receipt
is `build/physical/tt-buffered-recovery-power-01/invocation.json`. This qualifies
bounded power-grid connectivity; IR drop, current capacity and routed geometric
signoff remain open.

### Previous corrected-power milestone (retained)

The following measurements belong to the preceding corrected-power run. They
remain useful comparison evidence; the latest result above owns active status.

The new native power replay fixes OpenDB proxy comparisons and removes old
corridor stripes by geometry. Replacement Metal4 columns now extend from die
bottom to top (0–710.64 µm), instead of core bounds (3.78–706.86 µm). Each SRAM
has 68 direct VDD! contacts, 64 VDDARRAY! contacts and 68 VSS! contacts. Written
ODB readback confirms removal of old corridor columns and enclosed rail/column
via landings. Minimum opposite-supply Metal4 gap is 2.695 µm against the declared
0.24 µm clearance. Both native `check_power_grid` calls report every shape
connected; unbound-supply and missing-column controls reject before output.
This is bounded geometry/connectivity evidence, with IR drop, current capacity
and geometric signoff still open.

The corrected actual CAD run is `tt-buffered-physical-04`, frozen stage
`tt-buffered-corrected-power-02`: pinned ARM64 LibreLane/PDK, four CPUs,
6 GiB, no network, 1,800 s cap. It failed at step 40 `OpenROAD.GlobalRouting`
after 256.173 s. Inputs remained unchanged and owned-container cleanup was
confirmed. This continuation ran one full CAD flow; the earlier CAD baseline,
short checkpoint diagnostics and logical export retain separate receipts.

The last completed repaired placement contains 29,234 standard cells and two
SRAMs, versus 21,618 standard cells at synthesis. Reported instance area is
527,974 µm² (426,995 standard cells and 100,978 SRAM), about 57.6% of the tile.
There are 7,124 timing-repair buffers and 492 clock buffers/inverters; the
resizer reports inserting 3,541 hold buffers and 71 setup buffers. These
measurements include clock-tree/repair growth, but exclude completed routing
and later fill or repair.

Ordinary physical repair preserves the immediate output mask and one-clock
initialization contract while improving nominal estimated setup slack from
−31.6058 ns before repair to +5.4254 ns afterward. The final worst nominal
setup path still starts at `ena`, now ending at SRAM0 address bit 1. No enable
or reset timing path was removed. Step 39 reports only nominal typical timing;
its inherited slow/fast metric fields are not new measurements. Placement
estimates do not establish extracted routed closure.

A separate 47.579 s checkpoint diagnostic uses the unchanged native corner
script and exact copied ODB, SDC and nine corner libraries, with no layout or
netlist mutation. Its nominal import control matches step 39 setup/hold values
exactly. These are fresh estimates, rather than the inherited state metrics:

| Library corner | Setup slack | Hold slack |
| --- | ---: | ---: |
| Typical, 1.20 V / 25 °C | +5.425400 ns | +0.249567 ns |
| Slow, 1.08 V / 125 °C | **−0.734781 ns** | +0.466705 ns |
| Fast, conditional | +9.021830 ns | +0.092325 ns |

The slow corner has twelve setup violations: eleven `ena`→SRAM address paths
and one frontend counter→MISO path. Register-to-register setup remains positive
(+12.7294 ns at slow). All corners have 254 fanout violations; slew counts are
three typical, ten slow and zero fast, with no capacitance violations. The fast
screen combines −40 °C logic/I/O and −55 °C SRAM. At that milestone the 20 ns
target remained unqualified, alongside routing congestion; reset/enable timing
paths remained real constraints. The latest fresh post-CTS diagnostic clears
those twelve setup failures without removing the paths.

### Previous routing rejection and mapped acceptance

| Layer | Final overflow units |
| --- | ---: |
| Metal2 | 1,108 |
| Metal3 | 581 |
| Metal4 | 566 |
| Total | 2,255 |

Global routing reports 29,209 routed nets and 57.16% aggregate resource usage,
but persistent local congestion after its allowed iterations. Aggregate spare
capacity does not resolve a local routing bottleneck. That failed flow retained
aggregate metrics/logs, without a spatial congestion map. At that milestone the
evidence did not isolate power-column density, macro access, placement or
repair-buffer clusters as the cause. It motivated the retained congestion map
and bounded repair in the [locality study](../physical/tt-buffered-locality.md).
The later [SRAM access comparison](../physical/tt-buffered-sram-access.md)
tests a fixed-footprint pin-access change while preserving the timing and reset
contract. The earlier [address-driver placement comparison](../physical/tt-buffered-access-placement.md)
keeps the original macro orientation and tests two narrow driver reservations
against the exact timing-repaired control.

The mapped acceptance uses a fresh logical netlist exported from the completed
post-CTS repaired ODB, with both hashes bound to the selected checkpoint. A
strict top-name-only copy and named-port adapter allow the unchanged TT bridge
to exercise public pins. The checker admits exactly the public TT ports, or
those ports plus both named supply ports, and rejects partial/extra ports.
The first mapped attempt rejected the logical export's eight-port presentation
before compilation; that setup failure is retained, followed by the passing
corrected checker. It performs no power-connectivity check.

No accepted global route, detailed route, extracted timing, DRC/LVS or official
Tiny Tapeout precheck pass is recorded. KLayout DRC and Magic DRC remain enabled;
KLayout XOR remains disabled. The current official precheck implementation and
submission packaging are not present locally. A historical SRAM workflow uses
a different PDK/toolchain and does not qualify this candidate.

## Competition and research gates

| Competition submission work | Stronger research work |
| --- | --- |
| Resolve routing and remaining slew/fanout violations while preserving setup/hold margins; repair the pre-helper power-metric bookkeeping before an accepted full flow. | Compose source, upload/serial, initialized execution and wrapper correspondence at the claimed universal scope. |
| Complete detailed routing, extracted timing/electrical checks, power analysis and DRC/LVS. | Qualify asynchronous input, pad and SRAM electrical assumptions. |
| Run the current official TT precheck and final-layout upload tests; finalize packaging and demonstrations. | Extend buffered-target capability, including UART, and measure capacity/performance tradeoffs on the same engine. |

Physical routing and electrical limits remain blockers. Both the mirrored
policy and the earlier address-driver fences lose the previous setup margins
and increase coarse congestion. The preceding two-buffer experiment preserves all
three setup/hold margins, but increases matched coarse overflow to 5,944.
Retain the repaired R0 checkpoint
as the timing reference. The unchanged shared
engine and reset semantics remain digitally validated; positive post-CTS
estimates require confirmation after a completed route. The pre-helper power
metric/checker bookkeeping also needs correction before an accepted full flow.
No additional full baseline is implied by this result.

For another explicitly authorized physical baseline, prepare a fresh tag from
a passing boundary report and verified macro views:

```sh
python3 -B scripts/prepare-buffered-tt-physical.py \
  --validation build/tt-buffered/tt-buffered-boundary-01/report.json \
  --design <fresh-design> \
  --macro-root build/physical/tt-buffered-baseline-01/macro
python3 -B scripts/run-buffered-tt-physical.py \
  --design <fresh-design> --tag <fresh-run> --timeout-seconds 1800
```

These commands require the pinned PDK installation and Docker image. Fresh tags
preserve prior evidence. The runner rejects altered inputs, an incorrect image,
disabled macro supply hooks, stale tags and a preexisting container name. Its
cleanup targets only container IDs carrying this attempt's unique ownership
label and fails if termination or input integrity cannot be confirmed.
