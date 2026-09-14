# Early CMOS5L technology mapping

The double-bank atomic loader works digitally, but its register-backed storage
is too expensive in this implementation. At the typical corner, mapped
standard cells occupy **1.055 mm²**, before placement/routing or external I/O.
The prior single-image indexed core occupies **0.550 mm²** under the same flow.
This is an early feasibility rejection of the current implementation, not of
the atomic-loading contract.

The [competition announcement](https://blog.janestreet.com/protocol-emulator-asic-competition/)
allocates nominally 1 mm² / 32 Tiny Tapeout tiles. Cell area alone already exceeds
that figure for the atomic reference. The exact usable core rectangle and
utilization must still be established with the competition template. Routing
space, clock distribution, and the external loading interface need additional
budget; the single-image result by itself does not establish a fit either.

## Reproducible inputs

`tools/technology-library.json` pins the official
[IHP CMOS5L PDK repository](https://github.com/IHP-GmbH/ihp-sg13cmos5l)
at commit `607e18d4bd9214a52575c194b4181ef449f9252f`, with SHA-256 hashes for:

- `sg13cmos5l_stdcell_typ_1p20V_25C.lib`: typical, 1.20 V, 25 °C.
- `sg13cmos5l_stdcell_slow_1p08V_125C.lib`: slow, 1.08 V, 125 °C.
- The repository license.

The installer fetches only those three files into ignored
`build/tools/ihp-cmos5l/` and verifies hashes before use. It does not install a
full PDK, adopt a Tiny Tapeout template, or change global tools. The existing
pinned Yosys/ABC and CIRCT binaries supply the mapping flow.

```sh
python3 scripts/install-technology-library.py
python3 scripts/check-technology.py
```

The measurement runner verifies library hashes without downloading, re-emits
the two designs, translates them with CIRCT, and maps each separately at both
corners. It records source/RTL/library hashes, tool versions, generated scripts,
logs, and netlists in `build/technology/`; the success receipt is `report.json`.
Run the [loader validation](atomic-loader.md) independently for functional evidence.

## Mapping assumptions and results

Yosys runs `synth -noabc`, then `dfflibmap` and ABC against the selected Liberty
file. ABC uses `sg13cmos5l_buf_2` as its driving cell, a 10 fF load, and an
illustrative **10,000 ps combinational target**. Sequential boundaries remain
outside ABC. These are mapping constraints, not a justified chip clock or a
complete set of external I/O timing constraints.

| Design | Corner | Standard-cell area, µm² | Sequential area, µm² | ABC combinational delay, ps |
|---|---|---:|---:|---:|
| Single-image indexed | Typical | 550,400.5080 | 278,991.2160 | 10,004.10 |
| Single-image indexed | Slow | 555,012.7128 | 278,991.2160 | 11,032.71 |
| Atomic indexed | Typical | 1,055,247.9336 | 556,169.8464 | 9,976.44 |
| Atomic indexed | Slow | 1,062,866.5992 | 556,169.8464 | 13,199.27 |

The baseline retains **5,695 flip-flops** and maps to 21,937 cells; the atomic
reference retains **11,353 flip-flops** and maps to 42,611 cells. Mapped cell
counts are not comparable one-for-one with generic Yosys cells: the library
contains different gate functions and drive strengths.

Each corner is mapped independently, so this is not multi-corner analysis of
one placed netlist. The quoted delay is the final ABC `stime` combinational
estimate. It omits flip-flop clock-to-Q/setup, a clock tree, actual routing
parasitics, and full timing constraints. A result near 10 ns **does not prove
100 MHz operation**. There is no placed/routed area, STA sign-off, physical-rule
check, or RTL-to-mapped-netlist equivalence result in this batch.

## Design consequence

The atomic implementation adds **504,847.4256 µm²** of typical-corner cells,
about 92% over the prior core. The extra image and loader add 5,658 register
bits; roughly half of the total cell area is sequential storage. Read selection
and writes also cost gates. Optimizing the twelve loader-control bits cannot
recover the required budget.

The next bounded study should:

1. Establish the exact usable tile area and whether the pinned CMOS5L flow
   provides a suitable small memory macro. Record port count, widths/depths,
   read latency, write rules, and area; do not assume SRAM is available.
2. Compare smaller allocated banks or a denser execution representation with
   the actual UART/SPI/I²C images. Separate capacity/flexibility losses from
   implementation savings; preserve the current image as the reference.
3. For a synchronous store, propose and prove a fetch/prefetch schedule that
   preserves timed pin updates and terminal-capture-dependent branching.
   Re-measure the complete machine, including staging and buffers.
4. Select storage before adopting the external serial loader and full physical
   wrapper, then run a constrained place-and-route flow on the identified design.

A cheaper in-place upload that invalidates the old program is a different
observable contract. It remains an explicit alternative for discussion, not an
unannounced optimization in this implementation. The current two-bank design
and its tests give that future comparison a precise baseline.

The official [CMOS5L flow template](https://github.com/IHP-GmbH/ihp-sg13cmos5l-librelane-template)
and [Tiny Tapeout CMOS5L template](https://github.com/TinyTapeout/ttihp-verilog-template/tree/cmos5l)
are references for the later physical-flow integration; neither is adopted here.
