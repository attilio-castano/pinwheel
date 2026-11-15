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

The stock pre-route typical-corner analysis, after CTS and timing repair,
reported +8.973 ns setup slack, +0.283 ns hold slack, and zero capacitance or
slew violations. It reported 389 fanout violations. These are placement-stage
estimates under the stock constraints.

## Local reproduction

From this worktree, use a fresh, ignored output directory and the shared
native-tool lease. The runner reads the reviewed release handoff and pinned
Tiny Tapeout, Ciel and Python inputs described in the
[release rehearsal](streaming-8x4-jane-street-release-20261114.md).

```sh
RUN=build/8x4-jane-street-entry-20261114/clean-tt-next
DRIVER=scripts/streaming_8x4_tt_clean_harden.py
python3 -B "$DRIVER" stage --out "$RUN"
python3 -B "$DRIVER" run --out "$RUN" --lease "$NATIVE_LEASE" --jobs 4 --memory 6g
python3 -B "$DRIVER" simulate --out "$RUN" --view synthesis --iverilog "$IVERILOG" --vvp "$VVP"
```
