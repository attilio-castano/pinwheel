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
The configured corners are typical 1.20 V/25 °C, fast 1.32 V/−40 °C, and slow 1.08 V/125 °C. `TIMING_VIOLATION_CORNERS` is explicitly set to all corners; the PDK default checks only typical-corner violations. Unlike the
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

The digital PDK installer verifies 544 files and links against the pinned Git
blob inventory, including transitive symlink dependencies. It excludes unrelated
analog PyCell submodules and unused SRAM views. The typical and slow standard-cell
Liberty files match the earlier study byte for byte; the physical flow adds fast
corner, geometry, routing, and extraction views.

With Docker Desktop running, the normal container installation is:

```sh
docker pull ghcr.io/librelane/librelane@sha256:32244c826f512166840284332874bd9c26e5fd780b11cf23076c5dae8e2c3e04
docker tag ghcr.io/librelane/librelane@sha256:32244c826f512166840284332874bd9c26e5fd780b11cf23076c5dae8e2c3e04 ghcr.io/librelane/librelane:3.1.0.dev3
python3 scripts/install-physical-pdk.py
python3 scripts/prepare-physical.py
python3 scripts/run-physical.py --tag initial
```

The runner checks the ARM64 image's uncompressed layer identities and runtime
configuration. Docker's containerd store can assign a different manifest digest
when importing a verified archive; that alone is not a filesystem change. The
initial installation used verified host-side downloads and archive import after
Docker registry requests timed out.

Runs have unique tags, preserve inputs and logs, and execute with networking
disabled, four CPUs, a 6 GiB memory limit, and the PDK mounted read-only. A separate
input snapshot is retained for each run. The initial run was launched before
snapshot support was added; its matching inputs are archived under
`build/physical/core/experiments/initial/`.

The zero-delay functional check can be applied to a synthesized or routed netlist:

```sh
python3 scripts/check-physical-netlist.py path/to/netlist.v --label synthesis
```

It checks existing independent atomic/protocol vectors and compares every defined
source-RTL output bit before and after each edge. Reference-X bits from
uninitialized storage are excluded. A deliberately inverted output must fail.
This does not perform delay-annotated simulation or prove universal equivalence.
The default LibreLane EQY step does not support this PDK; it is not silently
counted as a passing formal check.

## Acceptance boundary

Record actual core area/utilization, routing completion and violations, clock
tree cost, extracted-parasitic setup/hold results, constrained-path coverage,
antenna/physical checks, and the identity of the final netlist/layout. Preserve
failed runs and their causes. Verify functional behavior after implementation
where supported, and distinguish that check from a proof of the Lean-to-RTL
translator. A routed timing result remains conditional on the stated PDK and
boundary constraints; eventual silicon validation is separate.
