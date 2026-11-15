# Exact 8×4 release-netlist behavior

The logical Verilog staged for Tiny Tapeout compiles directly against the
vendor CMOS5L functional models. The run used the checked release overlay on
a clean Git archive of `632de4c` and bound the GDS, logical netlist, four
generated RTL files, vendor cell models, and simulator binaries. The release
GDS is `d4cd48f0…`. Its logical netlist is `6b504119…`.
The logical Verilog contains 98,904 instances, including all 6,039 flops.
The vendor library declares every one of its 40 referenced cell masters.
[Release rehearsal](streaming-8x4-jane-street-release-20261114.md)

## Four programs on one instance

The host initialized once, uploaded and ran four different programs on the
same simulator instance, and released each result before the following
upload. Each COMMIT advanced the image generation. Each START allocated a
new owner. The board fixtures changed between programs. The host attached
the open-drain I²C lines while the UART program left all three output enables
off. This avoids connecting an open-drain link while a preceding program
still drives its idle pins.

| Generation | Program | Observed result | Cumulative edges |
| ---: | --- | --- | ---: |
| 1 | UART receive | `96` from one 8N1 frame | 3,619 |
| 2 | I²C read | 64 matching bytes at `0x52`, with 51 target-stretch edges | 13,972 |
| 3 | SPI duplex | TX `135ca5ee3780c912`, RX `a53cd36a00992ec7` | 16,921 |
| 4 | JTAG scan | 65 bits transferred, with RX `a53cd36a00992ec701` | 22,323 |

The independently compiled release RTL and the exact logical netlist produced
identical public stimulus and observation traces over 22,323 edges. Both
processes exited zero. Each trace has SHA-256
`a4cacb076ff79221228d60c5ccda0a867a902944a64121c33a3a1c036ecd151c`.
The fixture uses a cold reset and four START/RELEASE pairs with no warm reset.
All observations are digital and come from the public pin bridge.

## Regression and fault detection

All 35 unmodified cases passed, including 23 UART cases, a 32,768-bit SPI
exchange, a 4,097-bit JTAG scan, and ten I²C read and write cases. The I²C
cases cover clean and varying stretch, the final permitted poll, a timeout
and an address NACK. Each test drives the public host and protocol pins.
All 14 trace files covering 513,297 edges, including the negative control,
matched the earlier ODB-connectivity simulation byte for byte.
The clean RTL replay also matched every observation in the 13 unmodified
traces, covering 509,678 edges.

The negative control copies the submitted netlist and changes the D pin of
the second sampler flop for raw input 0 to read the first sampler's D net.
Only one byte in the netlist copy changed. The mutation compiled normally.
UART's public terminal edge advanced from
the expected edge 2,868 to 2,867, and the timing oracle flagged the
one-edge difference. Both the unchanged UART trace and the changed trace
matched their respective earlier ODB-connectivity traces byte for byte.
[Earlier implemented-netlist replay](streaming-8x4-hold-cap-digital-precheck-20261107.md)

The complete test ran in 638 seconds. Its local output is
`build/8x4-jane-street-entry-20261114/behavior-02/`. The final `receipt.json`
has SHA-256
`a6de4bc26ac3ebfe6c256377590019d8ac92ca2c4e58476a74819b33069ee365`.

## Run from a release checkout

The runner uses a Python 3.12 or newer interpreter, Icarus Verilog and the
two Verilog models in the official CMOS5L Ciel package at
`89d42ee6d2fd9b50b86a1aada6fee6673c3e6008`. Point `PINWHEEL_MODELS` to
`ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/verilog` within that installed
PDK. Use the four generated sources under `src/` and frozen views under
`release/` from the checked overlay. The archived replay opened those inputs,
the vendor models, and pinned Icarus without consuming the historical ODB
export, historical compiled simulation, or original `build/` traces.

```sh
python3 -B scripts/streaming_8x4_jane_street_behavior.py \
  --release . --models "$PINWHEEL_MODELS" \
  --iverilog "$PINWHEEL_IVERILOG" --vvp "$PINWHEEL_VVP" \
  --out build/8x4-release-demo --suite demo
```

Use `--suite all` for the complete UART, SPI, JTAG and I²C regression with
the sampler mutation and per-edge RTL comparison. It includes the short
succession demo. The runner writes commands, hashes, traces and the summary
receipt to a fresh path. It uses the Tiny Tapeout template's functional
compile defines and omits back-annotated timing. Board bring-up, qualified STA
and electrical qualification remain separate evidence.
[Behavior runner](../../scripts/streaming_8x4_jane_street_behavior.py) ·
[IHP template test command](https://github.com/TinyTapeout/ttihp-verilog-template/blob/4b1204ab387b5ab94db1d57067051d8d89a2f83c/test/Makefile)
