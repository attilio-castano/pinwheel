# Physical validation of the general core

This milestone tests the 32-entry, dense, cached atomic core selected by the
[storage study](storage-study.md). Its pin/capture semantics and atomic loading
contract are unchanged. Physical implementation is separate evidence from the
Lean circuit proofs and independent RTL simulations.

## Target and upstream pins

`tools/physical-toolchain.json` records the inspected upstream identities:

- Tiny Tapeout CMOS5L template: `b86a2a781484bcab7ba522dc5de540086695a430`.
- GDS action: `3412659307918422f3f0727917cf9b499aaca588`.
- CMOS5L support tools: `da63c9927411e3aca350977d653d24bbf5bca972`.
- LibreLane: `3.1.0.dev3`, with the ARM64 container manifest digest pinned.
- IHP Open PDK: `2bbec755dc67ca3db0261c3d6163e15735d66710`, selected by the action.

The [competition](https://blog.janestreet.com/protocol-emulator-asic-competition/)
specifies 8×4 tiles. The pinned
[CMOS5L tile table](https://github.com/TinyTapeout/tt-support-tools/blob/da63c9927411e3aca350977d653d24bbf5bca972/tech/ihp-sg13cmos5l/tile_sizes.yaml)
and DEF inventory have no 8×4 entry. This is an actual support-file gap, beyond
the stale size comment previously recorded in the template. No 8×4 floorplan is
invented or represented as approved here.

The diagnostic uses the supported **6×4 dimensions, 1,289.28 × 710.64 µm**,
as a standalone core rectangle. It does not apply the Tiny Tapeout DEF pin
template: all internal word-loader and diagnostic ports remain exposed and
observable. No functional input is tied off and no output is discarded to shrink
the core. This is a conservative area experiment in a smaller rectangle, not a
Tiny Tapeout submission or a validation of the eventual external pin interface.

The external serial loader, asynchronous input conditioning, pin multiplexing,
and final wrapper still need space and timing budgets. This run does not validate
their behavior or cost. In particular, its synchronous input constraints do not
establish metastability safety or external UART/SPI/I²C electrical timing.

## Experiment constraints

`physical/core.json` starts from the template's 20 ns clock target (50 MHz), uses
the same Metal4 signal-routing ceiling and narrow floorplan margins, and sets a
70% placement-density target to leave room above the previous cell-area estimate.
The density target is not a measured final utilization. Power distribution and
clock-tree synthesis remain enabled. The template's KLayout DRC/XOR exclusions
remain explicit; a flow completion must not be called comprehensive sign-off.

`physical/core.sdc` constrains every nonclock input, including synchronous reset
and initialization, without false-path exceptions:

| Constraint | Experiment assumption |
|---|---|
| Clock period | 20 ns |
| Input delay | 0.2 ns minimum, 4 ns maximum |
| Output delay | 0.2 ns minimum, 4 ns maximum |
| Input driver | `sg13cmos5l_buf_2/X` |
| Output load | 10 fF |
| Clock uncertainty | 0.2 ns |
| Ideal clock transition | 0.15 ns; physical clock propagated after CTS |

These are explicit core integration budgets, not measured board characteristics.
The initial run tests one clock target; it is not a search for maximum frequency.
All configured PDK timing corners must be recorded in the result. Unlike the
earlier independent typical/slow mappings, physical STA must analyze the same
implemented netlist across its corners.

## Input provenance

With the pinned Lean toolchain on PATH:

```sh
python3 scripts/prepare-physical.py
```

The script regenerates the general candidate from Lean, exports SystemVerilog,
and requires its SHA-256 to match the successful storage-study RTL receipt. It
copies the physical configuration and SDC into `build/physical/core/`, and records
current source and input hashes in `inputs.json`. This prevents silently measuring
a different circuit. Large tools, PDK views, and flow artifacts stay in ignored
`build/physical/`.

## Acceptance boundary

Record actual core area/utilization, routing completion and violations, clock
tree cost, extracted-parasitic setup/hold results, constrained-path coverage,
antenna/physical checks, and the identity of the final netlist/layout. Preserve
failed runs and their causes. Verify functional behavior after implementation
where supported, and distinguish that check from a proof of the Lean-to-RTL
translator. A routed timing result remains conditional on the stated PDK and
boundary constraints; eventual silicon validation is separate.
