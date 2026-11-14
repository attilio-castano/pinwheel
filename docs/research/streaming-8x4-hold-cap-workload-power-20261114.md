# Frozen 8×4 public-pin workload activity and parent power intake

The zero-delay model from the frozen candidate now has replayed activity for
UART receive, SPI duplex, I²C write and reset followed by a replacement upload.
The existing stretched I²C read is the comparator. All four new waveforms
declare the same 124,176 instance signal pins, including 24,156 flop pins.
Every sampled public observation matches the uninstrumented model. The
simulator models pinned Liberty logic at a 20 ns clock period. It uses the
full clock tree and all 42,210 functional instances. A separate replay
reproduces every trace and every VCD byte apart from the header's date.

| Scenario | Edges | Duration (µs) | Functional checks |
| --- | ---: | ---: | --- |
| I²C read comparator | 10,419 | 208.380 | 64 data bytes, six stretches, matching release |
| I²C write | 10,419 | 208.380 | 64 data bytes, target ACK and byte comparison, 51 stretch edges, matching release |
| SPI duplex | 16,205 | 324.100 | 1,024 bits, actual TX/RX peer checks, bounded stalls, matching release |
| UART receive | 3,864 | 77.280 | Cold and warm reset, 9-word image, one autonomous 8N1 frame returning `96`, matching release |
| Reset and replacement upload | 5,681 | 113.620 | Cold and warm reset, two accepted commits, 9 + 7 words and two 512-cycle idle windows |

The reset and upload checkpoints are cold release at edge 2, warm reset
receipt at 247, first commit at 2,697, replacement commit at 5,169 and
final idle at 5,681. Both upload commits advance the generation and the
second image differs from the first. SPI uses the existing protocol peer
and transaction checks on a 1,024-bit finite workload to keep the waveform
and native readback tractable.

## Power boundary intake

The resolver accepts a source record for these exact ODB and GDS hashes
with a classified contact map, guaranteed voltage range and reference point,
and independent VPWR and VGND per-source-node static feed resistances.
Use macro-local micrometre coordinates and the actual Metal4 contact
rectangles, with evidence and the supplying owner identified for reviewed
parent inputs. The runner's nominal 1.2 V setpoint must lie within the
declared source range. The lower end of a supplied range remains an input
to the voltage budget.

The input schema is
`pinwheel.streaming-8x4-hold-cap-parent-power-input.v1`.
Set `classification` to `reviewed_parent` or `illustrative`, and
`coordinate_frame` to `macro_local_um`. Include the two exact candidate
hashes. Declare `contact_map.ownership` and `contact_map.contacts`,
with `rail`, `layer`, `x_um`, `y_um`, `width_um`, and `height_um`
per contact. Declare `source_voltage.reference_point`, `minimum_v` and
`maximum_v`, and `external_impedance.interpretation` with the value
`ohm_per_resolved_source_node`, `vpwr_ohm`, `vgnd_ohm` and
`return_path`. For reviewed parent inputs, include hashes of the source
records under `evidence` as absolute `path` and `sha256` pairs.

The resolver checks each contact lies wholly inside a same-rail exported
LEF rectangle. It selects solver nodes within each contact from the
hash-bound full Metal4 node census and refuses empty or overlapping
assignments. The `vsrc` files enumerate exact selected nodes. The native
readback verifies that the expected nodes and solved nodes are identical.
An illustrative eight-contact request resolves back to the four known
nodes per rail from the earlier sparse sensitivity. Rectangular contacts
were exercised in a two-node control. Contacts with no node, overlap,
off-rail placement, or coordinates finer than the layout grid were refused.

Supply contact geometry, voltage tolerance and impedance from the actual
parent remain necessary. Source resistance here is independent for each
resolved grid node. A shared package impedance or transient RLC model
needs its own topology and evidence.

## Reproduction

Use fresh ignored output directories. `PINWHEEL_HISTORY` points to the
retained history checkout containing the pinned OpenROAD and PDK receipts.

```sh
TRIAL=build/8x4-hold-cap-20261107/trial-02
POWER=$TRIAL/power-dc
for scenario in i2c-write spi uart reset-upload
do
  python3 -B scripts/streaming_8x4_hold_cap_workloads.py \
    --case "$scenario" --out "$TRIAL/workload-$scenario-replay"
done
python3 -B scripts/streaming_8x4_hold_cap_parent_power.py \
  --input "$POWER/parent-illustrative-input-01.json" \
  --out "$POWER/resolved-parent-replay"
python3 -B scripts/streaming_8x4_hold_cap_ir.py \
  --history "$PINWHEEL_HISTORY" --out "$POWER/workload-spi-replay" \
  --vcd "$TRIAL/workload-spi-replay/activity.vcd" --scope streaming_quad_host_bridge/dut \
  --parent-contacts "$POWER/resolved-parent-replay/resolved.json" --sheet-temperature 105
python3 -B scripts/streaming_8x4_hold_cap_ir_readback.py \
  --history "$PINWHEEL_HISTORY" --out "$POWER/workload-spi-readback-replay.json" \
  --workload "$TRIAL/workload-spi-replay/receipt.json" "$POWER/workload-spi-replay"
```

| Ignored receipt | SHA-256 |
| --- | --- |
| `workload-i2c-write-02/receipt.json` | `fed19c5cf3428ad948926969bafc73e59d22ad8b0d56f966a88a7d1b13387686` |
| `workload-spi-02/receipt.json` | `f20b45bb7591e0c4e8b9bb5bef379ccafa61774056c2a165d14f750725a782e4` |
| `workload-uart-02/receipt.json` | `641eadd6e37e3beeb2e5fc4e11567ab318a4937e642d6dcb48076a5c6446eee3` |
| `workload-reset-upload-02/receipt.json` | `845f7bf586a79dedebab008c65415b786e5f150d40f212e32e59d84fb9c74087` |
| `power-dc/parent-illustrative-resolved-02/resolved.json` | `80c543a9a6cf3f2a7c2bcf2128b6f253f6ed5e309e0854d7b305437481f5acda` |

These waveforms cover finite observed workloads. A legal activity bound
still needs a declared clock, program space and input domain, with physical
glitch and mode-dependent energy effects. Qualified electrical power and
fabrication remain open.
