# Frozen 8×4 Metal1, via and terminal current audit

On November 14, the frozen `dc654986…` ODB and `d4cd48f0…` GDS were
reopened against the six [static power cases](streaming-8x4-hold-cap-ir-em-20261112.md).
Every sub-range Metal1 solver edge has a wider drawn path. The via audit
identifies 48 arrays where the sparse-source results still depend on how
current splits across cuts. A fresh replay recovered terminal and source
currents from the solver matrix. Local rehearsal remains GO and fabrication
remains NO-GO.

## Narrow Metal1 edges

The audit joined each current row to its exact SPICE resistor, recovered the
effective width from the pinned sheet resistance, and checked that all six
cases use the same sub-160 DBU geometry. The DEF identifies 94 ground and 93
power Metal1 followpin rows. Each 440 DBU row rectangle is covered by the
direct top-level GDS drawing. KLayout 0.28.17-1 then reopened hierarchical
Metal1 drawing on layer 8/0 in a local window around each edge, including
transformed standard-cell metal. A certificate pairs both endpoints with one
connected piece of drawing via that rail's named row. It consists of
three positively overlapping rectangles fully contained in the drawing.

| Rail | Sub-range solver edges traced | Minimum certified path width | Highest sub-range current in any case | Solver width at peak | Certified path width at peak |
| --- | ---: | ---: | ---: | ---: | ---: |
| VGND | 60,481 | 0.160 µm | 0.3043 mA | 0.105 µm | 0.260 µm |
| VPWR | 34,552 | 0.170 µm | 0.2206 mA | 0.055 µm | 0.270 µm |

Both current peaks come from the I²C case with four 1 Ω sources per rail
and 105 °C sheet resistance. The ground edge from (1219.155, 18.630) to
(1219.260, 19.385) µm spans the staggered Metal1 fingers of
`engine.core._4920__9476` and `engine.core._3256_`. Their 0.105 µm X overlap
crosses the 0.440 µm VGND row at Y = 18.900 µm. The wider certificate
follows the 0.260 µm fingers through that row. The VPWR peak is in a
`FILLER_181_357` decap finger at the row centered on Y = 687.960 µm.

OpenROAD computes resistance from rectangle widths in its decomposition of
the rail shapes, using the larger X or Y separation for a branch length.
The GDS certificates show that these small effective widths do not force
sub-0.16 µm physical necks between the endpoints. Using the wider
certificate width to assign the original branch current would require an
electrical model of the conductor network and current sharing.
[Pinned PSM shape decomposition](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/psm/src/shape.cpp#L35-L75)

## Via arrays

All 8,505 modeled rail via edges map one-to-one to exact DEF locations and
their GDS references. The sequence and dimensions of the 36,610 cut
rectangles agree with the DEF via definitions. OpenROAD can move an
effective via node while assembling the network. Both endpoints uniquely
identify the same array, within 2.320 µm, and the resistance agrees with
the physical cut count.

| Cut | VPWR arrays | VGND arrays | Cuts per array | Worst modeled array current |
| --- | ---: | ---: | ---: | ---: |
| Via1 | 3,255 | 3,290 | 2 | 0.3951 mA |
| Via2 | 490 | 490 | 8 | 1.504 mA |
| Via3 | 490 | 490 | 16 | 2.898 mA |

All equal-sharing estimates stayed below the IHP 0.4 mA/cut reference.
Peak equal share was 0.19755 mA/cut. If cut currents flow in the same
direction and the modeled array total applies, every Via1 array and all
arrays in the two distributed cases fit the per-cut reference even with
all array current assigned to one cut. The same 48 arrays in each sparse
case exceed that one-cut total, comprising 23 Via2 and 25 Via3 arrays.
The peak Via2 case needs at least four cuts to share the current with
no cut carrying more than about 26.6%. Peak Via3 needs at least eight
cuts and a maximum share of about 13.8%. These are requirements on the
sharing, with the exact affected locations retained in the readback.
[IHP CMOS5L §3.5](https://github.com/IHP-GmbH/IHP-Open-PDK/blob/2bbec755dc67ca3db0261c3d6163e15735d66710/ihp-sg13cmos5l/libs.doc/doc/SG13CMOS5L_os_process_spec.pdf#page=19)

## Terminal and source currents

One fresh offline replay of the I²C, sparse 1 Ω, heated-sheet case enabled
the pinned OpenROAD solver's full dumps. Ten existing outputs, including
both rail voltage and grid current tables, reproduced byte for byte. The
replay took 53.261 seconds and finished with its container absent. The
reader joined the full conductance, load and voltage data by named solver
node and index, including 2,037 VPWR and 2,067 VGND ITerm coordinate-name
aliases in SPICE. It recovered signed currents for 569,560 grid-to-ITerm
connections, 210 grid-to-BPin connections, 728,818 ordinary grid edges and
eight 1 Ω source branches. The maximum physical-node KCL residual was
5.77 pA and the maximum source-total mismatch against the modeled load
was 1.04 nA.

The total modeled load was 19.306429 mA with 79,065 positive loads among
98,904 instance terminals per rail. The peak cell load was 18.912 µA at
`clkbuf_2_2_0_clk`. The eight source magnitudes are shown below. The return
flows toward the ideal ground sources. The macro BPin model nodes have no
material net current in this sparse case because the ideal sources reach
the selected grid nodes through the explicit 1 Ω branches.

| Rail | Source location (µm) | Magnitude (mA) |
| --- | --- | ---: |
| VPWR | (16.400, 12.000) | 4.800694 |
| VPWR | (16.400, 663.780) | 4.956886 |
| VPWR | (1712.320, 12.000) | 4.668162 |
| VPWR | (1712.320, 663.780) | 4.880689 |
| VGND | (24.080, 19.400) | 4.770932 |
| VGND | (24.080, 669.400) | 4.841378 |
| VGND | (1720.000, 19.400) | 4.757868 |
| VGND | (1720.000, 669.400) | 4.936251 |

The largest modeled terminal connector currents were 694.570 µA on
`FILLER_3_3251/VSS` and 306.498 µA on `FILLER_7_3350/VDD`.
Both are decaps with about 0.659 nA modeled net load. Opposing signed
connector currents balance at each terminal. The solver uses 1 mΩ
connectors without a conductor cross-section, so the branch currents are
redistribution through its terminal abstraction.

A targeted GDS audit matched the exact DEF placements, power assignments,
transformed pin labels and 0.160 × 0.160 µm contact shapes at these sites.

| Terminal | Contact cuts on labeled conductor | Solver point on that conductor |
| --- | ---: | --- |
| `FILLER_3_3251/VSS` | 12 | Yes |
| `FILLER_7_3350/VDD` | 18 | Yes |
| `clkbuf_2_2_0_clk/VSS` | 20 | No |
| `clkbuf_2_2_0_clk/VDD` | 26 | No |

The peak-load clock buffer's solver points are offset from its drawn supply
conductors. Its named terminal identities still match the ODB and its
labeled pin rectangles land on the correct followpin rows. The contact
count leaves individual contact currents unresolved, including lateral
Metal1 redistribution and device-side injection. From this evidence,
the IHP 0.3 mA/contact figure cannot be applied directly to the largest
1 mΩ branch. Physical EM closure still needs qualified current crowding
analysis for the identified vias and contact structures, and a parent
contact map and accepted supply and operating envelope.

## Local evidence and reproduction

All results are in the ignored candidate directory under `power-dc/`.
The archive and manifest of the verified rehearsal bundle retain their
original hashes. The current CSVs and geometry certificates are separate
local evidence.

| Artifact | SHA-256 |
| --- | --- |
| `metal1-trace-02.json` | `02d66114b1dfdea1fb5011169ad2ab7b8ce1c5ba28a0c4879c7bc988d666a672` |
| `metal1-trace-02.tsv` | `3adb7ae1a925f82ecb7c321a0c2900e27f23ddee05fd735040f418a1f16ba2c3` |
| `via-array-audit-01.json` | `a96eed9482c8ac0d2aeb12b5fe2ea4e5159900f99215741984638a4d7f4e7d97` |
| `terminal-contact-geometry-01.json` | `adee588f7eff95a4fdcc2bd668eba2a162fbe6fe87472ac3b9bbc97f31fea824` |
| `i2c-sparse-r1-sheet105-dump-01/dump-receipt.json` | `e73ce4cdf0e9ce8634f9a3aacddc5824bf35630921c450e66c84d8f349b5b45d` |
| `terminal-currents-03/readback.json` | `88acc8523eef86e47b3cc667b7b4987a02cbdef25218b34937bf1dbf48ac6008` |

From the worktree root, point `PINWHEEL_GEOMETRY_PYTHON` at the retained
precheck interpreter with KLayout 0.28.17-1 and gdstk 0.9.52.

```sh
POWER=build/8x4-hold-cap-20261107/trial-02/power-dc
"$PINWHEEL_GEOMETRY_PYTHON" -B scripts/streaming_8x4_hold_cap_metal1_trace.py \
  --out "$POWER/metal1-verify-01.json"
(set -C && "$PINWHEEL_GEOMETRY_PYTHON" -B scripts/streaming_8x4_hold_cap_via_audit.py \
  > "$POWER/via-verify-01.json")
python3 -B scripts/streaming_8x4_hold_cap_psm_currents.py \
  "$POWER/i2c-sparse-r1-sheet105-dump-01" --out "$POWER/terminal-verify-01"
"$PINWHEEL_GEOMETRY_PYTHON" -B scripts/streaming_8x4_hold_cap_terminal_geometry.py \
  --out "$POWER/contact-verify-01.json"
```

The [native dump runner](../../scripts/streaming_8x4_hold_cap_psm_dump.py)
takes the retained history checkout and a fresh case directory. The four
commands above reopen the evidence without another native solve.
