# Clean Tiny Tapeout CMOS5L hardening, November 15, 2026

The [clean build runner](../../scripts/streaming_8x4_tt_clean_harden.py)
stages the four byte-matched release RTL files, project metadata, and
the 8×4 stock CMOS5L template in a fresh directory. The frozen custom
GDS `d4cd48f0…` and its reviewed [rehearsal](streaming-8x4-hold-cap-rehearsal-20261107.md)
remain the release reference.

## Build inputs

| Input | Identity |
| --- | --- |
| Reviewed local release handoff | `c0eff2d9fbdd395bf120c3eba742a4784021c74e9fbf760f8936bd45a3e010ba` |
| Tiny Tapeout template, support and action | `4b1204a`, `9d13ff3`, `e7a50f8` |
| Ciel IHP open PDK | `89d42ee6d2fd9b50b86a1aada6fee6673c3e6008` |
| LibreLane 3.1.0.dev4 image ID | `sha256:af2405f5d48d8fe14d406ecce913811177a95e365e3b625859677307cace2469` |
| `clean-tt-04/stage.json` | `c746d4453fd232516b0fd31a3321738ce52f4e51e3d261232820c4d65d8f706b` |

Tiny Tapeout's `tt_tool.py --create-user-config` generated the merged
configuration and selected its 1724.16 × 710.64 µm DEF template. The runner
invoked the LibreLane command used by the Tiny Tapeout wrapper in the pinned
container. It used a read-only PDK mount, four CPU equivalents, a 6 GiB memory
cap and a six-hour timeout. The local receipt records provenance. The Tiny
Tapeout wrapper adds hosted provenance after a successful hardening run.

The stock 20 ns timing configuration uses 4 ns input and output delays,
0.25 ns of clock uncertainty, a 0.006 pF port load and a 5% derate.
Routing is limited to Metal2–Metal4 with 30% global-route capacity reserved.
The stock PDN creates 35 full-height 2.1 µm Metal4 stripes per rail. Its pin
centers match the geometry of [historical CMOS5L parent attachments](streaming-8x4-hold-cap-parent-attachment-20261115.md).

## Synthesized netlist evidence

Yosys mapped 43,098 cells with 621,721.2078 µm² of cell area. Icarus loaded
that exact output, SHA-256
`07eacfbf0fc0310774dfaab6622212defac41992cd78980e5cbb06d1ac91af6f`,
with the two pinned IHP simulation models. Its four protocol fixtures and
one-instance UART → I²C → SPI → JTAG succession matched the released RTL.
The succession contains 22,323 public-pin edges with trace SHA-256
`a4cacb076ff79221228d60c5ccda0a867a902944a64121c33a3a1c036ecd151c`.
The `clean-tt-04/wire-synthesis/receipt.json` SHA-256 is
`d61c3207a788c621f1012c84796ae0f0addf8719e7e21589de33246200ff2ccc`.

The same hash-bound synthesized model independently replayed all 13
positive public-pin traces for the 35 retained cases. All 509,678 edges
matched the exact release netlist's traces byte for byte. The local replay
took 105.57 seconds. Its `clean-tt-12-stock-synthesis-corpus/receipt.json`
SHA-256 is `68f41c1f5a6a65205e5059510be6635b5756c62212c81a1d14483be02c4f4656`.

Local stock equivalence attempts remain inconclusive. A Yosys induction
attempt reached its 120-second cap. EQY's Yosys partition pass segfaulted
with the default macOS stack size, then reached a 240-second cap with a
larger stack.

The stock pre-route typical-corner analysis, after CTS and timing repair,
reported +8.973 ns setup slack, +0.283 ns hold slack, and zero capacitance or
slew violations. It reported 389 fanout violations. These are placement-stage
estimates under the stock constraints.

## Stock global routing

The stock run finished global routing in 34 minutes 30 seconds. Its use of
the capacity reservation and the completed per-layer overflow were as follows.

| Signal layer | Modeled resources | Demand | Overflow |
| --- | ---: | ---: | ---: |
| Metal2 | 212,423 | 172,455 | 134 |
| Metal3 | 259,924 | 247,474 | 34,678 |
| Metal4 | 208,744 | 64,992 | 120 |
| Total | 681,091 | 484,921 | 34,932 |

OpenROAD reran congestion removal six times while temporarily dropping the
clock net spacing rules inside the global router. The saved DEF still has all
six clock NDR assignments. The current template permits global overflow and
passed its guides to antenna repair and detailed routing. A reserve trial
can use the same post-CTS database and change only the modeled global-route
capacity reservation from 30% to 19%. It leaves the technology rules and
route layers fixed. That trial produces a congestion comparison.
[OpenROAD global routing options](https://openroad.readthedocs.io/en/latest/main/src/grt/README.html)

The stock global-route log SHA-256 is
`931131af8ac9c6a292d404fd22e607e3ab22de61a0380c098a4c5837701b1315`.

The first complete detailed-routing iteration reported 94,859 markers in
25 minutes 54 seconds. Metal2 and Metal3 shorts accounted for 45,640 and
28,133 markers. This is the initial detailed route before iterative repair.
The next four completed passes found 87,429, 84,022, 49,229 and 41,042
markers. The fourth complete count included 25,628 Metal2 and 11,004
Metal3 shorts. The stock run was stopped after those five completed passes
to give the lower-overflow continuation the native worker. The stock run
was active for 2 hours 34 minutes 46 seconds and preserved its inputs and
reports. The container cleanup was confirmed.

| Stock stop receipt | SHA-256 |
| --- | --- |
| `execution.json` | `d0f9d016e73479c06ce954cfe13fc1161facd2e077e263f3618212e2068d11f6` |
| `stop-request.json` | `858f82902689ba9fb7894e958fb2071eba2a545465845e1c44a11108b88b62a8` |
| `harden.log` | `46fc0354e468c9aba73074a2a0203b28a326193c8eb3d076772c6b9a8763e037` |

## Capacity reserve trials

The separate `clean-tt-06-reserve19` run completed global routing after
34 minutes 52 seconds. It kept the stock post-CTS state, and the runner
verified that only `GRT_ADJUSTMENT` changed in the resolved configuration.
The local admission receipt binds the stock worker and the trial's two-CPU
and 1.25 GiB equal memory/swap caps. The trial worker was removed at exit.

| Signal layer | Modeled resources at 19% reserve | Demand | Overflow |
| --- | ---: | ---: | ---: |
| Metal2 | 253,450 | 195,092 | 44 |
| Metal3 | 303,221 | 247,665 | 14,387 |
| Metal4 | 248,902 | 68,470 | 61 |
| Total | 805,573 | 511,227 | 14,492 |

The reduction in overflow was 58.51%. Metal3 gained 43,297 modeled resource
units and retained most of the overflow. Estimated wirelength increased from
4,642,351 to 4,948,185 µm.

| 19% trial receipt | SHA-256 |
| --- | --- |
| `execution.json` | `3136758848d791366b5aac73d98ac9b77c5709bd51f26cdd608f77c887c12767` |
| `harden.log` | `90fc46749250aa68b22faf5ad51b2c5cea5b97c19cc757b8a3a7ddba4e49bc0b` |
| `concurrent-admission.json` | `1447e3c31862db2c051ea5107e1b6c9790604c8f573fc01920fec091a84b87a9` |

The `clean-tt-07-reserve08` follow-up completed in 18 minutes 25 seconds
with the same configuration and checkpoint controls. The measured global
overflow was 2,622 units, a 92.49% reduction from stock. Estimated wirelength
was 4,821,595 µm. Three clock nets temporarily lost their spacing rule
during the optimization. The trial uses the same routing layers and rules.

| Signal layer | Modeled resources at 8% reserve | Demand | Overflow |
| --- | ---: | ---: | ---: |
| Metal2 | 279,685 | 196,118 | 14 |
| Metal3 | 349,015 | 250,217 | 2,590 |
| Metal4 | 272,376 | 58,058 | 18 |
| Total | 901,076 | 504,393 | 2,622 |

| 8% trial receipt | SHA-256 |
| --- | --- |
| `execution.json` | `4235ef43387ec96d473814a882d4fe49583fe69d7720b197398fe675006c5edb` |
| `harden.log` | `0f3f27dae1c8e6993e41876865576c608cf24dae598cd47fcdb2204c3ef1c44c` |
| `concurrent-admission.json` | `bff01b34e413e476e46565cc663fbe59218ccc99254f678c96d6de164e00a464` |

## 8% detailed-routing continuation

`clean-tt-08-reserve08-tail` starts at `OpenROAD.CheckAntennas` with the
exact 8% global-route ODB, its guides and the checked stock ancestor views
mounted read-only. The pinned flow runs through its final manufacturing
checks under the same template with the 8% modeled reserve. The
continuation stage SHA-256 is
`cbb3fa4faeeae070f7c69b99126cd4f32ecab00a4c8850092db3f8d6b2efafcf`.
Its separate worker has four CPU equivalents, 6 GiB and a 4.5-hour cap.

The continuation's global-route antenna step found 235 violations, inserted
386 diodes and reported zero after repair. The stock comparison used 597
diodes. The first complete detailed-routing pass took 29 minutes 18 seconds
and reported 117,326 markers, including 56,462 Metal2 and 33,086 Metal3
shorts. The stock first pass reported 94,859 markers. The two global-route
reserves produced different guides and antenna repairs. Matching later
repair iterations is the direct check on detailed routing progress.

| Completed iteration | Stock markers | 8% reserve markers |
| --- | ---: | ---: |
| 0 | 94,859 | 117,326 |
| 1 | 87,429 | 105,879 |
| 2 | 84,022 | 102,399 |
| 3 | 49,229 | 73,632 |

The continuation was stopped after iteration 3 to give the worker to a
marker-enabled replay of the stronger stock route. It ran for 2 hours
2 minutes 46 seconds and confirmed container cleanup. Both attempts
stopped during detailed routing, leaving a new source-to-GDS candidate
and its post-route timing, LVS, and precheck open.

| 8% continuation stop receipt | SHA-256 |
| --- | --- |
| `execution.json` | `a79d11ae8ad41ccddf593f0e56a64643e4dac847218c91bd6ff9e1949cab1f5a` |
| `stop-request.json` | `cb4d4576cbf734bc312e0a79901fdfd47051b796911517b2837be40127d1c995` |
| `harden.log` | `779fcd33f5518a8f2342ad74dc7205acf1517edb2f4ad63a5e8262c02c071e73` |

## Placement density trial

The separate `clean-tt-09-density85` diagnostic started from the stock
preplacement template state and changed the placement density target from
60% to 85%. The resolved configuration retained the normal 30% reserve
and all other settings. Both initial placements had 43,098 cells and
621,731 µm² of cell area. Estimated placement HPWL fell 17.20% while the
placer weighted congestion score rose 3.05%.

| Metric | 60% density | 85% density |
| --- | ---: | ---: |
| Post-CTS hold buffers inserted | 6,235 | 6,258 |
| Typical setup estimate (ns) | +8.973 | +9.286 |
| Typical hold estimate (ns) | +0.283 | +0.288 |
| Global wirelength (µm) | 4,642,351 | 4,357,972 |
| Global route modeled total demand | 484,921 | 445,996 |
| Global route total overflow | 34,932 | 42,202 |
| Metal3 maximum local horizontal overflow | 8 | 13 |

The denser placement increased peak and total overflow as overall demand
fell. Its diagnostic stopped at global routing.
The worker completed in 39 minutes 36 seconds with exact config comparison,
unchanged inputs and confirmed cleanup. The `comparison.json` SHA-256 is
`cd1c7db935e94352da4f4c602c7c0e500fe62acfb4c7eceba6675d43ba6f2562`.

## Residual Metal3 congestion geometry

The read-only OpenDB probe reproduced the native Metal3 overflow totals and
maximum local overflow for all four specimens. Saved grid capacity, usage
and Metal2/Metal4 overflow differed from their native directed totals.
The Metal3 comparison uses only the calibrated overflow fields.

In the 8% route, the x-band from 1,036.8 to 1,382.4 µm contains 2,368
of the 2,590 Metal3 overflow units. Its busiest 86.4 µm square is
`(1152, 216)–(1238.4, 302.4)` µm and holds 159 units. The DEF instance
origin proxy counts 5.19 connected terminals per grid cell there and
6.27 across the chip. The corresponding stock window holds 722 units.

The exact 8% guide file has 52,634 unique net blocks matching ordinary
DEF nets and the native routed-net count. There are 6,112 nets with
positive-area Metal3 guide overlap in the band, of which 5,980 are signal
nets and 132 are clocks. Signals account for 97.76% of per-net union area.
Nets of degree eight or more account for 47.41% of that area. The top 100
names contribute 7.86%. These are guide overlap measurements. Connecting
them to individual detailed-route markers requires the completed detailed
route and its marker coordinates.

| `clean-tt-10-gcell-probe` receipt | SHA-256 |
| --- | --- |
| `comparison.json` | `12c4e46a84cebfe1bda9fe2f588d3ecd742d3a2357a6042484ad5209d08675ea` |
| `reserve08-band-guide-coverage.json` | `f2d914752a4404654c5adfa81ca4657132eb3f7c2134498b842bd24815ec94f4` |

Joining the exact stock logical Q pins to the placed DEF identifies all
4,096 program-word flip-flops and preserves the same positions in the 8%
trial. Every one of the 64 stock words has bits on both sides of the band.
The median horizontal word span is 1,025.52 µm. At 85% placement density
the median span falls to 772.80 µm, and 22 words span both sides. The
number of word bits placed in the band rises from 1,132 to 1,570.

The stock post-CTS repair adds 6,235 `sg13cmos5l_dlygate4sd3_1` cells. The
same-net DEF pin join verifies one added delay-cell A terminal connected
directly to the Q output of each of the 4,096 word flip-flops. Within the
band, nets with direct word flip-flop terminals account for 3.29% of the
guide area and nets with direct added delay-cell terminals account for
1.63%. Logic beyond those direct connections remains unclassified. The
`bank_placement.json` receipt reproduced byte for byte with SHA-256
`02d87f8f00291f1bda9e210eb084134e1b9909686569f8ebeae9fbfc60c96aaf`.

## Named stock detailed-routing markers

`clean-tt-11-stock-drt-markers` replays the checked stock antenna-repaired
checkpoint with a two-pass detailed-routing limit and per-iteration marker
reports. It reproduced 94,859 and 87,429 native markers exactly. The
first-run routed ODB and text report retained the same 20,010 records by
rule, layer and bounding box. The two ODB report categories repeat that
set. Another 67,419 native markers fall outside the saved report. The
internal antenna check found 158 net and 182 pin violations after the
first bounded route. The 60-minute wall limit stopped the next internal
antenna reroute with unchanged inputs and verified worker cleanup.

Of the 7,444 visible Metal2 shorts, 63 name a supply net and 1,236 name a
diode-loaded net. One record names both, `VGND` and `_10368_`. The
Metal2 sample spans 2,690 nets and 3,547 distinct named pairs. Its most
frequent pair accounts for 17 records. The figures describe the capped
sample and leave prevalence across the full native tally open.

The routed ODB reproduces actual signal centerline penetration of
same-layer supply via enclosures in all four selected Metal2 Short
windows. Three of four selected Metal3 signal-to-signal Short windows
show strict perpendicular centerline crossing. This identifies both
mechanisms in the stock checkpoint. Repair of a signal family or a local
antenna access pattern still requires a separately measured physical
trial.

| `clean-tt-11-stock-drt-markers` receipt | SHA-256 |
| --- | --- |
| `execution.json` | `694891352cd3edbd64404710520e3ddd9fa2ccd43bd120a00f32fb0aa653895e` |
| `marker-coverage.json` | `f7e49b88533b58491d5de09e7b8be6f626e54785a7f5471f1cdcfd8d9c4e9d9b` |
| `marker-pairs.json` | `cc4d9bf617550b61924a0bd506126b3638558fd92bc5d35fec0e0cab5a2a5976` |
| `post-route-readback/reconciliation.json` | `0ee451d1d4d2b9724d3e7cde57b08f4f7d102e2f62159c93eb2a172ad7b21e27` |

## Release decision

Keep the frozen custom GDS as the local rehearsal candidate. The clean
source run reproduced public-pin behavior through synthesis. Both physical
runs stopped during detailed routing. The 8% reserve and 85% density
experiments give comparison evidence for the next physical repair. A new
source-to-GDS candidate still needs detailed-route closure, stream-out,
fresh LVS and precheck, and a timing check on the resulting layout.
Fabrication of the frozen candidate remains NO-GO pending qualified timing
and power and the exact shuttle's acceptance.
[Active fabrication gates](status.md)

## Local reproduction

From this worktree, use a fresh, ignored output directory and the shared
native-tool lease. The runner reads the reviewed release handoff and pinned
Tiny Tapeout, Ciel and Python inputs described in the
[release rehearsal](streaming-8x4-jane-street-release-20261114.md).
On macOS, the staging Python process must be able to load the host Cairo
library. A Homebrew Cairo installation may need `DYLD_FALLBACK_LIBRARY_PATH`
set to its library directory for the `stage` command.

```sh
RUN=build/8x4-jane-street-entry-20261114/clean-tt-next
DRIVER=scripts/streaming_8x4_tt_clean_harden.py
python3 -B "$DRIVER" stage --out "$RUN"
python3 -B "$DRIVER" run --out "$RUN" --lease "$NATIVE_LEASE" --jobs 4 --memory 6g
python3 -B "$DRIVER" simulate --out "$RUN" --view synthesis --iverilog "$IVERILOG" --vvp "$VVP"
```

After the completed stock global-route step, a separate fresh staged
directory accepts `run --route-trial-from "$RUN" --route-reserve 0.19`.
It imports the checked post-CTS state and runs the `OpenROAD.GlobalRouting`
step. Use the completed per-layer congestion table to choose a candidate
for detailed routing.

To continue a checked trial through the standard downstream steps, stage
a new directory with `--continue-from "$TRIAL" --stock-from "$RUN"`.
Run that directory with the normal shared lease. The `review`, `simulate`
and `precheck` commands accept a completed, separately bound candidate.
