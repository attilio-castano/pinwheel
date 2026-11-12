# Frozen 8×4 static IR drop and electromigration screen, November 12, 2026

Six local OpenROAD PSM cases solved both rails of the frozen hold/capacitance
candidate. With I²C activity and distributed ideal contacts, the worst rail
losses sum to **1.004 mV**. The same activity with four contacts per rail and
1 Ω per contact gives **36.975 mV**. Raising sheet resistance to model 105 °C
in that case gives **42.117 mV**. Both the supply and return geometry matter.
The local rehearsal remains GO and fabrication remains NO-GO.

## Activity and supply assumptions

- The simulated I²C read uses the varying-payload, clock-stretched positive
  trace including reset. The exact frozen functional cell model reproduced
  all 10,419 sampled public observations over 208.380 µs at 50 MHz. OpenSTA
  matched all 124,176 instance signal pins and all 43 public bits to the
  waveform, including all 24,156 FF pins. The zero-delay replay omits physical
  glitch timing and covers one finite workload.
- The vectorless comparison applies 0.1 transitions per 20 ns period and
  0.5 duty at the nonclock inputs and propagates activity through the
  loaded design. Both cases use the 20 ns propagated clock, the pinned
  typical 1.20 V / 25 °C Liberty and the retained draft TYP signal SPEF.
  The power-run parasitic report matches all 282 unused drivers from the
  timing audit, with zero partially annotated drivers.
- The modeled sources are 1.20 V on VPWR and 0 V on VGND. The distributed
  case resolves 5,215 ideal Metal4 nodes per rail from the exported macro
  pins. The sparse case resolves one node in each of four 1 × 1 µm squares
  per rail. The coordinates below are the Cartesian products of X and Y,
  in µm. External resistance applies separately to each resolved node.
  These supply conditions are sensitivity cases for the macro boundary.
- Native PSM logs confirm the OpenDB technology values of 0.135 Ω/□ on
  Metal1, 0.103 Ω/□ on Metal2–4 and 20 Ω per Via1–3 cut. The 105 °C case
  applies only the published metal sheet-resistance temperature factors
  referenced to 300 K. It gives 0.17195244 Ω/□ on Metal1 and
  0.1320279625 Ω/□ on Metal2–4. Via resistance, typical Liberty, activity,
  source voltages and external resistance stay fixed.
  [IHP process specification, §§3.1–3.4](https://github.com/IHP-GmbH/IHP-Open-PDK/blob/2bbec755dc67ca3db0261c3d6163e15735d66710/ihp-sg13cmos5l/libs.doc/doc/SG13CMOS5L_os_process_spec.pdf#page=16)

| Rail | X | Y |
| --- | --- | --- |
| VPWR | 16.400, 1712.320 | 12.000, 663.780 |
| VGND | 24.080, 1720.000 | 19.400, 669.400 |

The readback checks each source against the exact exported Metal4 pin shape
and the resolved native coordinates. Two exploratory sparse runs requested
VPWR contacts at Y = 13.780 µm that the solver snapped to Y = 12.000 µm.
The reader rejected the displaced coordinates. The accepted runs explicitly
declare the latter position. An earlier launcher attempt also exited before
the solve when the pinned binary rejected its debug command. The corrected
launcher uses the binary's top-level command.

## Static IR drop

| Case | Activity | Sources | Ω/node | Sheet °C | Power (mW) | VPWR drop (mV) | VGND rise (mV) | Sum (mV) | Min. instance VDD−VSS (V) |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `ports-03` | Vectorless | Distributed | 0 | 25 | 23.504 | 0.517 | 0.493 | 1.010 | 1.198990 |
| `sparse-ideal-02` | Vectorless | Sparse | 0 | 25 | 23.504 | 13.970 | 13.724 | 27.694 | 1.172312 |
| `sparse-r1-01` | Vectorless | Sparse | 1 | 25 | 23.504 | 18.865 | 18.621 | 37.485 | 1.162515 |
| `i2c-ports-01` | I²C | Distributed | 0 | 25 | 23.167 | 0.514 | 0.490 | 1.004 | 1.198996 |
| `i2c-sparse-r1-02` | I²C | Sparse | 1 | 25 | 23.167 | 18.610 | 18.365 | 36.975 | 1.163031 |
| `i2c-sparse-r1-sheet105-01` | I²C | Sparse | 1 | 105 | 23.167 | 21.245 | 20.873 | 42.117 | 1.157912 |

The rounded columns come from the full-precision readback. The sum of the
two rail extrema bounds the loss within the modeled grid. The rightmost
column pairs both rail voltages at each of the 98,904 instances before
taking the minimum. The exported current loads sum to 19.5867 mA per rail
with vectorless activity and 19.3064 mA with the I²C waveform. They reproduce
the power-to-current conversion and remain fixed across source and
sheet-temperature changes. The analysis is static and leaves voltage-dependent
cell power, package dynamics and decap transients outside its model.

## Electromigration

The readback joins every reported current to its SPICE resistor by layer and
endpoint. It recovers effective modeled metal width from the solver's
sheet resistance and max-axis segment length, and verifies equivalent via
multiplicities of 2, 8 and 16 cuts from the per-cut resistance. The SPICE
export provides geometry and source-node evidence. Its source circuit omits
the solver's external resistors, so the native voltages and currents supply
the quantitative results for the 1 Ω cases.
[OpenROAD segment resistance](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/psm/src/connection.cpp)

The pinned CMOS5L table gives Metal1 0.36 mA at 0.16–0.36 µm and
1 mA/µm above that width. Metal2–4 use 0.6 mA at 0.20–0.30 µm and
2 mA/µm above. Via1–3 use 0.4 mA per individual cut. The published
reference is an estimated failure rate below 0.01% over 11 years at
105 °C. The table is the source of the per-cut values.
[IHP process specification, §3.5 and Appendix A.v](https://github.com/IHP-GmbH/IHP-Open-PDK/blob/2bbec755dc67ca3db0261c3d6163e15735d66710/ihp-sg13cmos5l/libs.doc/doc/SG13CMOS5L_os_process_spec.pdf#page=19)

| Case | Highest modeled utilization in covered geometry | Peak equal-share via current (mA/cut) |
| --- | ---: | ---: |
| `ports-03` | 6.8% | 0.00968 |
| `sparse-ideal-02` | 79.3% | 0.17681 |
| `sparse-r1-01` | 79.7% | 0.17544 |
| `i2c-ports-01` | 6.8% | 0.00965 |
| `i2c-sparse-r1-02` | 78.6% | 0.17281 |
| `i2c-sparse-r1-sheet105-01` | 85.1% | 0.19755 |

Each case has 728,818 reported wire/via edges. All 633,785 edges within the
published width range or with a modeled via comparison were below their
limits. In the 105 °C sheet case the highest ratio was 0.3065 mA against
0.36 mA on a modeled 0.36 µm VGND Metal1 segment from
(1230.195, 18.515) to (1230.555, 18.900) µm.

Another **95,033 Metal1 edges per case** have effective widths below the
published 0.16 µm range. The largest current among these was **0.3043 mA**
in the heated-sheet case, on a modeled 0.105 µm edge. Those are solver
geometry widths, including decomposition of overlapping shapes. Their
physical conductor widths and current crowding need separate review.
Equivalent via sharing leaves individual-cut crowding open. The current
CSV excludes 569,770 modeled instance and boundary terminal connections
per case, so their physical contacts also remain outside this screen.

## Readback and remaining qualification

The readback binds the exact ODB `dc654986…`, GDS `d4cd48f0…`, activity
receipt and all six native cases. The accepted runs took 265.236 native
seconds total, exited zero and verified container cleanup. The raw runs and
waveforms are ignored local evidence beside the unchanged rehearsal bundle.

| Artifact | SHA-256 |
| --- | --- |
| `power-dc/ir-em-readback.json` | `d1bb974807b3caf1e1daa85cbddd314e06dede45980074f6d8c932d03c8de7e9` |
| `power-dc/contacts-resolved/VPWR.vsrc` | `c5ae133249be1ce152eb55a565220568aaa00c6ab3188f156adc629d312199a7` |
| `power-dc/contacts-resolved/VGND.vsrc` | `548821b02cd65bd6f7fb97be9a30f7257fed2d54669fe5879a292d64d8be6b1b` |
| `workload-activity-01/receipt.json` | `ad31c8c7e9a592a4b428dd2472073b19e1a2a7982ef97bdbd88970afee2e1503` |
| `workload-activity-01/activity.vcd` | `edf88dd4c6859800aaa874d9835a4fee11f50f8f342b7ec63bd933b93b989f01` |

From the worktree root, set `PINWHEEL_HISTORY` to the retained history
checkout. The readback reopens the six cases without native execution.

```sh
POWER=build/8x4-hold-cap-20261107/trial-02/power-dc
python3 -B scripts/streaming_8x4_hold_cap_ir_readback.py \
  --history "$PINWHEEL_HISTORY" --out "$POWER/verify-01.json" \
  "$POWER/ports-03" "$POWER/sparse-ideal-02" "$POWER/sparse-r1-01" \
  "$POWER/i2c-ports-01" "$POWER/i2c-sparse-r1-02" "$POWER/i2c-sparse-r1-sheet105-01"
```

The [activity replay](../../scripts/streaming_8x4_hold_cap_activity.py)
accepts a fresh output directory and the
[solver runner](../../scripts/streaming_8x4_hold_cap_ir.py) accepts a fresh
case directory under `power-dc/`. Use `--input-activity 0.1` for the
vectorless cases or `--vcd <waveform> --scope streaming_quad_host_bridge/dut`
for the I²C cases. For sparse sources, pass `--contacts` with the two
retained four-row CSVs and set `--external-ohm` and `--sheet-temperature`
from the case table.

Qualification still needs the parent contact map and supply tolerance,
package/board impedance and transient allowance, an operating activity and
thermal envelope, supported minimum local voltage, and applicable EM
coverage for narrow physical conductors, cut crowding and terminal contacts.
The local results quantify the effect of plausible diagnostic boundaries
while the shuttle power boundary and acceptance remain open.
