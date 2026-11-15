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
4,642,351 to 4,948,185 µm. The `clean-tt-07-reserve08` follow-up is testing
the same checkpoint at 8% to measure the remaining capacity sensitivity.

| 19% trial receipt | SHA-256 |
| --- | --- |
| `execution.json` | `3136758848d791366b5aac73d98ac9b77c5709bd51f26cdd608f77c887c12767` |
| `harden.log` | `90fc46749250aa68b22faf5ad51b2c5cea5b97c19cc757b8a3a7ddba4e49bc0b` |
| `concurrent-admission.json` | `1447e3c31862db2c051ea5107e1b6c9790604c8f573fc01920fec091a84b87a9` |

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
