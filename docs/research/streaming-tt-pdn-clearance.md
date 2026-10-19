# Streaming TT power-grid/public-pin admission

The proposed grid has passed an isolated native geometry admission and the
unchanged official Tiny Tapeout Pincheck. This closes the reproduced public-pin
short and package power-port geometry defects in this pre-placement fixture.
It does not establish full-candidate power connectivity, DRC, LVS, extracted
timing, IR drop, or physical acceptance.

The previous 07 GRT export had three public Metal4 rectangles entirely covered
by VGND stripes: `ui_in[3]`, `uio_out[5]`, and `uo_out[0]`. The same export also
contained Metal2 automatic edge pins and Metal3 power ports. The official
CMOS5L checker requires every canonicalized power-port rectangle on Metal4,
at least 2.1 µm wide, and within 10 µm of both the top and bottom edges.

The correction retains the four-layer, standard-cell-only M1/M2/M3/M4 grid and
all three adjacent-layer connections. M2 and M3 stop at the core boundary;
only M4 is promoted to package ports. M4 retains a 2.1 µm width and 50 µm
power/ground pair pitch. Its first power-stripe center moves to x=16.16 µm,
and the pair-center separation becomes 7.68 µm, exactly two public-pin pitches.
This is an offset of 13.28 µm from the admitted core origin and an edge spacing
of 5.58 µm within the pair. The minimum public-pin gap is 640 nm, above the
conservative 240 nm spacing taken from the pinned Metal4 LEF table.

`scripts/streaming_tt_pdn_geometry.py` checks the exact frozen official DEF
template before preparing CAD inputs. Both physical preparation paths retain
its receipt and recompute it during verification. `physical/streaming_tt/pdn.tcl`
also rejects changed DBU scale, die/core origin, public-pin membership,
directions, placed rectangles, mixed placement, or pre-existing PG port boxes.
Classic applies the fixed DEF pins after PDN generation; fully unplaced public
pins are therefore admitted against their hash-bound future template positions.
This distinction is explicit rather than treating unplaced pins as measured
geometry. Host tests reproduce the exact three former shorts and exercise the
production Tcl against both placed and unplaced object stubs.

The native probe uses the closed 07 pre-placement ODB as a read-only source.
It creates a separate fixture that places all 43 public pins at the exact official
positions before generating the proposed grid. It runs only embedded OpenDB
fixture creation, PDN generation, actual OpenDB readback, and KLayout streamout.
It does not place cells, run CTS, route, repair timing, or modify the shared PDK.
Actual power-wire rectangles and conservative bounding boxes covering every
power via are checked against every public rectangle. Actual PG port geometry
must match all 52 proposed full-height stripes; redundant endcaps are accepted
only when contained in those stripes. The expected port set was not changed
to accommodate native output.

The closed receipt is
`build/streaming-physical-development/pdn-clearance-unqualified-02/report.json`,
SHA256 `3754a1f7bc2ff189d545b27de105fb5a8a4d0b42901ba2e09bad4c8a53057aeb`.
It retains 29,004 source instances, matches all 52 M4 power stripes exactly,
and measures at least 640 nm clearance across 6,370 actual power-wire/via-bound
shapes. The unchanged official Pincheck passes on its actual GDS/LEF exports.
The LEF derivative changes FP3 numeric and whitespace spelling only, using the
existing exact-Decimal identity adapter. Input, producer, PDK, and runtime
bindings are checked; `qualified`, `physical_acceptance`, and
`candidate_flow_completed` remain false.

The resource receipt is
`build/streaming-tt-resources/pdn-clearance-03/report.json`, SHA256
`6e7d4ebf1efe2e115c77664d7efea0c18aec170706aadadbba5eededd7f84866`.
It records exit 0, 6.318 seconds, confirmed cleanup, and no remaining owned
container or process. The container was offline, limited to 4 CPUs and 6 GiB RAM,
with swap disabled. Two earlier resource attempts remain preserved: the first
stopped before spawning because sandbox observations were unavailable, and the
second stopped on a container-stats exit race after its native geometry and
Pincheck phases had passed. Neither earlier resource attempt is called a closed
host success. The second native probe used the corrected observer and closed
normally.

The probe also captured the pinned image's actual CTS Tcl and step source under
`pinned-tool-source/`. Its Tcl forwards `CTS_SINK_CLUSTERING_SIZE` as
`-sink_clustering_size`. The retained 07 resolved settings enable sink clustering
but leave that size and maximum diameter null. This source capture supports
planning a separate bounded clustering trial; no CTS trial ran in this probe.

The next physical acceptance step must regenerate the complete candidate with
this grid, check power connectivity and the unchanged official precheck on its
actual final geometry, and close all routed connectivity and timing gaps.
