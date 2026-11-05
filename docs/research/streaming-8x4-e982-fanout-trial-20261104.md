# Pinwheel 8×4 scratch fanout trial

The five-net scratch ECO passed the fanout, detailed-router, antenna and
supplemental enclosure checks. The DRT writer also changed 19 additional
ordinary signal wire records. This is a routed experiment with a larger
wire delta than the declared topology edit. The frozen rehearsal ODB and
GDS remain the release reference. [Rehearsal report](streaming-8x4-tt-rehearsal-20261104.md)

The trial started from exact post-fill ODB
`b7e60eded5198fc53df7e5dd1e3ab0f5162720516ab0c1692a1cf7c7bb62602b`.
Five `sg13cmos5l_buf_1` instances replaced five same-footprint
`sg13cmos5l_decap_4` cells on sites clear of the pinned power-grid blockage
rule. All remaining instance records, all original antenna diode
connections, and the die, tracks, public pins and special-net DEF records
matched the source. The placement check passed.

| Original net | Operation | Original loads before → after | Loads on new branch |
| --- | --- | ---: | ---: |
| `net2157` | Equal-master clone | 12 → 8 | 4 |
| `net2298` | Equal-master clone | 10 → 8 | 2 |
| `net11223` | Equal-master clone | 9 → 8 | 1 |
| `net2333` | Serial buffer | 9 → 8 | 2 |
| `net840` | Equal-master clone, fixed leaf cut | 9 → 8 | 1 |

The `net840` operation moved `fanout833/A` to a new routed branch. The
native wire encoder removed exactly four FIXED path records for that
leaf and retained the other 121 path records, including both antenna
bridges. A fresh process reopened the final ODB and verified the exact
625-entry FIXED vector, the clone wiring and power bindings, and a
maximum load count of eight across 44,609 regular signal and clock nets.

The four-net control cleared router markers and OpenROAD antenna and kept
the whole `net840` DEF record byte-identical. It changed 15 additional
ordinary signal wire records and exposed a special-terminal annotation
gap in the initial partition runner. The five-net run marks every new
rail terminal special and verifies the complete DEF partition before
starting routing. Its initial router marker count was 200. The final
count was zero, with zero OpenROAD antenna violations across the block
and on each affected net. Independent KLayout checks on the streamed
scratch GDS had zero markers across 23 foundry antenna categories and
all 11 supplemental enclosure rules.

The 19 collateral wire records retained exact terminal sets, and all
collateral changes were on ordinary signal wires. The initial experiment
established fanout and antenna feasibility for the routed derivative.
The full main-deck, transistor LVS and geometric power checks are recorded
below.

## Retained trial evidence

The ignored directory `build/e982-fanout-20261104/five-01/` contains the
route and screen artifacts. The [local runner](../../scripts/streaming_8x4_e982_fanout_trial.py)
can repeat the experiment into a fresh output directory. The same parent
directory retains the native ODB reopen and independent deck launchers
as `reopen-odb.py` and `screen.py`.

| Artifact | SHA-256 |
| --- | --- |
| `trial.odb` | `e40e40804ddf5c4093f83710ec27b0a5b975f3a047e5c95810e175fbe6aa78f9` |
| `trial.def` | `fbccaa1f145b74050eb5ff257db80cbdd9a3a1b56a530ab27a2d6ba9ad6d23ff` |
| `stream/design.gds` | `dcc496d71202677f6d2fe3785dca6ff9bb225ef954953bf7925171174d4b7e82` |
| `review.json` | `34fe0a51cec73d9476887aefbdcfb8b118ff817fe848c09dfb063d9dd060c213` |
| `reopen/result.json` | `dd753e2ebaa0d0973977c6bb0aa8f45398512715fdbe9c64f67b737e7edb5625` |
| `screen.json` | `86eff28a562f4d51f3719f146e8529cb10db89c703bb8b87d8b992ab64e94170` |

## Physical qualification follow-up

**Carry the ECO forward for qualification.** The main-deck DRC,
strict-port transistor LVS, and geometric power-grid checks passed on
the exact ODB and GDS listed above. The frozen rehearsal remains the
reference for before-and-after review. Fabrication remains NO-GO.

| Gate | Exact ECO result |
| --- | --- |
| Main IHP SG13CMOS5L DRC | 332 categories, zero markers, including `NW.b`. The full native invocation took 1,977 seconds and the container exited. |
| Same-target views | The fresh DEF matched the trial bytes. The independently streamed GDS matched after timestamp normalization. The complete CDL was independently recomposed from the pinned master library and the new ODB inventory, covering 98,900 instances and 321,974 positional terminal bindings. |
| Transistor LVS | All 37 circuit pairs matched in strict port mode with `NET_ONLY=false`. The LVS reference was the exact ECO CDL. The fresh foundry antenna replay also had zero markers. |
| Power connectivity | VPWR and VGND each reached all 98,900 instance terminals and one top-level terminal, with empty error reports. The exact special-net DEF geometry and every retained instance’s rail assignments matched the baseline. |

The five substitutions reduced the `decap_4` inventory from 5,678 to 5,673
and kept 31,183 `decap_8` cells. The nearest remaining decap origin to
`eco_net840_buf` is 10.56 µm away by maximum axis distance. The
illustrative ±10 µm square around that buffer contains zero decap
origins. This placement observation gives a location for power review.
Quantitative supply droop and electromigration remain open. The checked
power result is geometric rail connectivity.

Release adoption requires review of the 19 collateral routes and the
decap change, qualified CMOS5L extraction and timing with the shuttle
I/O constraints, electrical power qualification, and shuttle admission.
[Timing intake](streaming-8x4-e982-timing-intake-20261104.md)

The [exact-target runner](../../scripts/streaming_8x4_e982_eco_signoff.py)
supports `drc`, `views`, `pg`, `lvs`, `official`, and `decision` phases. The main
deck's raw files live in `five-01/drc/`. The remaining readbacks below
are in `build/e982-fanout-20261104/signoff-01/`.

| Readback | SHA-256 |
| --- | --- |
| `decision.json` | `451f51bd3ca820d6d76ce4deb7bdfeae2a9d9e97ce4ad845c031e1320a3c317b` |
| `cdl-independent-readback.json` | `fcb297e6fa830a49d2790ae9efd825cff7836929033dea864211276fbc913316` |
| `views/rehearsal-view-readback.json` | `f3e019f5d4abf85e7d6f123c9d2f9d8282cca69e29b0e81e1db9ec34f048b045` |
| `pg/rehearsal-pg-readback.json` | `869a4052c8ddd40d7bcf2a037f84856d1d4a00215ee4ae00cd2f0ea3de6ac81e` |
| `layout/rehearsal-lvs-readback.json` | `2518207acf1c17b1dfeece9533d155dc736d1abd6bbb6085aed8e3b7cf2a1428` |

## Digital correspondence

The fresh check reopened the exact ECO connectivity and canonical
netlists, then checked the five buffers against the pinned three-corner
Liberty logic. Four clones share the input of their original driver.
The serial buffer forwards the original signal. Restoring the ten
rebound sink pins after substituting those Boolean identities recovers
the complete named graph of the frozen candidate, with 36,005 original
active gates, all 6,039 state bits, and all 24 public output bits. The
clock and reset cones and the terminals of the 160 antenna diodes
match. This transports the accepted zero-delay correspondence from
`b7e60…` to `e40e4…` using the existing Lean proof and a fresh ECO
graph check. [ECO digital runner](../../scripts/streaming_8x4_e982_eco_digital.py)

Fresh gate-level replay kept the buffers in the exact ECO design.
All 35 UART, SPI, I²C, and JTAG cases passed, and the oracle rejected
the injected stage-two sampler fault. All 14 traces matched the
frozen candidate byte for byte across 513,297 sampled edges, including
the negative run. The trace comparison establishes digital behavior
for this corpus under zero-delay simulation.

| Local readback under `build/e982-fanout-20261104/` | SHA-256 |
| --- | --- |
| `digital-02/transport.json` | `7b6aaef9a4970e9d3d64a56f7bebce04f30be8e55b407b4367b4ce99578276e1` |
| `digital-02/wire/report.json` | `eb1975a2b5bcb047d0453ef6b5086a4bec92d59ee511cecf790e6b311d92116c` |
| `digital-02/wire/worker/native.jsonl` | `cfa96790f07635b7c7e9c29b9b685eb2c9e15062a1a428b198ab4ad3d4959dad` |

## Local Tiny Tapeout precheck

All nine checks selected by Tiny Tapeout support revision
`d66cf179e7bc4d296362ab7e2e3b344dc3c4f665` passed for
`ihp-sg13cmos5l`. The local offline run used the exact ECO GDS and
the canonical LEF and powered Verilog. Pin-label overlap, full CMOS5L
DRC, and zero-area checks each returned zero markers. The main DRC
covered 332 categories including `NW.b`. The independent geometry
readback matched the 8×4 boundary and all 43 signal pin rectangles
and labels. The staged views and raw reports were reopened after the
run, and the three native processes exited. This result covers the
pinned local precheck. Run-specific acceptance remains with the shuttle.

| Local readback under `build/e982-fanout-20261104/signoff-01/` | SHA-256 |
| --- | --- |
| `official/rehearsal-tt-precheck-readback.json` | `dd3507c40f5e72f643c8f26a866f57e8d05fc83acb9f4bd5d911ff436bbce1ed` |
| `official/tt/precheck/reports/results.xml` | `73c4850706f26c71aa3a86d0437e7edb8861c1ad8defe7d49ab04df4be040430` |
| `official/tt/precheck/reports/drc_sg13cmos5l.xml` | `a31ee7a26146bf0912141c9407f13172156699c2003d495acf9235e2d736bdb5` |
| `eco-pin-geometry.json` | `96b0c0f93fabb2df392cb9dde400b23bf12fcd107d40603dd00b219d6faf7fb2` |

## Decap and buffer power comparison

The five-swap comparison uses the pinned Liberty corners and exact
placed-cell census. The leakage figures sum the five buffers and
subtract the five removed decaps. The input capacitance is the sum
of the five added buffer A pins.

| Corner | Change in nominal cell leakage | Added signal input capacitance |
| --- | ---: | ---: |
| Fast, 1.32 V, −40 °C | −6.326 nW | 12.232 fF |
| Typical, 1.20 V, 25 °C | −1.426 nW | 11.317 fF |
| Slow, 1.08 V, 125 °C | +2.165 nW | 10.576 fF |

The removed decaps' drawn gate areas and nominal PSP oxide parameters
give a parallel-plate scale of about 24 fF per decap and 120 fF across
the five. Effective rail capacitance depends on device bias, overlap
and fringe capacitance, and the rail admittance of each replacement
buffer. The retained geometric rail pass and this cell comparison
leave dynamic power, transient droop, and electromigration open.
Qualification needs the shuttle supply boundary, activity and current
waveforms, and acceptable rail-voltage and current-density limits.
[Power comparison runner](../../scripts/streaming_8x4_e982_eco_power.py)

The local report `signoff-01/eco-power-observation.json` has SHA-256
`c0133860e060ca4221048b9e5156efeb1a213421f7250bf2a763cdc47d0f470a`.
It binds the exact candidate ODB, DEF and GDS, the placement partition,
and the Liberty and SPICE inputs. Normal and optimized Python
produced byte-identical reports.

## Five-layer extraction and timing

The local diagnostic extracted a separate SPEF for each of the pinned
five-layer MIN, TYP and MAX draft models from the exact same-ODB DEF.
It ran each SPEF against the fast, typical and slow Liberty scenarios
with the 20 ns rehearsal SDC and a propagated `clk`. The same matrix
was run on the frozen candidate to isolate the ECO from the model
change. [Local timing runner](../../scripts/streaming_8x4_e982_eco_timing.py)

The draft copies vary capacitance and named via resistance. The
canonical extractor uses `-lef_res`, so ordinary wire resistance
and generated via resistance stay fixed by the original technology
LEF in every pass. The nine combinations are a sensitivity sweep.
The model still requires physical qualification, and the actual
shuttle clock and I/O constraints remain open.
[Draft model scope](streaming-8x4-draft-rc-timing-diagnostic-20261022.md) ·
[Shuttle timing intake](streaming-8x4-e982-timing-intake-20261104.md)

| Draft model | ECO worst hold, fast / typical / slow (ps) | ECO worst setup across PVT (ns) | Max-cap violations, baseline → ECO (fast / typical / slow) |
| --- | ---: | ---: | --- |
| MIN | −54.402 / −61.132 / −42.660 | +3.187 | 0 / 0 / 0 → 0 / 0 / 0 |
| TYP | −69.867 / −79.850 / −64.114 | +2.180 | 1 / 1 / 1 → 1 / 1 / 1 |
| MAX | −84.668 / −95.618 / −81.645 | +1.559 | 5 / 5 / 4 → 5 / 5 / 5 |

Every scenario had one hold violation on the falling `ui_in[5]` to
`engine.frontend._0230_/D` path on both layouts. ECO hold slack
changed by at most 0.226 ps in the paired runs. Worst setup stayed
positive, with a largest paired change of 3.917 ps. Fanout violations
fell from five to zero in every pair. Both layouts had zero slew
violations. With the other diagnostic quantities fixed and hold
uncertainty at 200 ps, the worst ECO hold path would reach zero slack
at a minimum input delay of about 296 ps. The shuttle I/O contract
determines the actual earliest arrival.

The ECO added one max-capacitance violation, at `fanout2425/X` in
MAX with slow cells. Its collateral reroute `net2425` reached
0.300726 pF against the 0.300000 pF limit. The other capacitance
violator pins were shared with the baseline in their respective
scenarios. These are local findings to reopen with the admitted RC
model and shuttle constraints.

The independent readback reconciled 41,786 consumed ECO nets in
each SPEF, with zero missing or partially annotated consumed nets.
The 282 raw unannotated drivers were individually accounted for as
unused. OpenSTA's setup diagnostics for clock and constraint
coverage printed no findings under the rehearsal SDC.

A supplemental replay loaded the same ECO netlist, SPEFs, Liberty
and SDC in the same OpenSTA binary and reproduced setup and hold
worst slack in every case. The worst minimum pulse-width margin
was +9.714 ns. The loaded constraints and libraries yielded no
applicable recovery, removal or minimum-period checks in this replay.
[Supplemental replay runner](../../scripts/streaming_8x4_e982_eco_electrical.py)

| Local readback under `build/e982-fanout-20261104/` | SHA-256 |
| --- | --- |
| `timing-eco-02/timing-readback.json` | `a42c09b64dc2721cbdf7e224b8b228caaa3cbcb82497ccba52972a78471a48ae` |
| `timing-baseline-01/timing-readback.json` | `ee429d766cefcc23683aa0497f620484fad627bf4f933db6ede49a65b781ef78` |
| `electrical-01/readback.json` | `cc452dd0c004af4b125cf47839e097893ca91d66245b5ed2cf57b57afefc4baf` |

## Exact ECO rehearsal package

**GO for local rehearsal. NO-GO for fabrication.** The separate ECO
bundle binds the `e40e4…` ODB and `dcc496…` GDS at the top of this
report. It contains seven handoff files and 204 evidence files. The
handoff includes GDS, canonical LEF, logical and powered Verilog,
metadata, the bring-up datasheet and the license. The evidence copy
contains the checked physical reports, the digital transport and
worker artifacts, and the retained timing and power diagnostics.

The fresh bring-up run used the unmodified ECO gate-level simulator
from the 35-case wire run. Warm reset, UART receive, SPI duplex and
64-byte I²C read and write passed across 27,407 sampled edges. The
I²C read exercised 51 clock-stretch edges. This was a public-pin
simulation. [Bring-up runner](../../scripts/streaming_8x4_e982_eco_bringup.py)

The bundle is retained locally. Its assembly source revision was
`a46a599aecfc69e7807e1b79524ddfd4faf455b2`. Given a separate copy,
the [ECO verifier](../../scripts/streaming_8x4_e982_eco_rehearsal.py)
checks the source file hashes against the sealed manifest before
reopening the evidence.

```sh
python3 -B scripts/streaming_8x4_e982_eco_rehearsal.py \
  verify /path/to/retained/eco-bundle \
  --manifest-sha256 1b7261201a8420890f4e9a00bd1652fb022c864feea40666897feaa226337f6b
```

An independent run reopened a physically separate copy using a clean
Git archive of the verifier, with reads from the original and
historical worktrees blocked. It rejected a substituted baseline GDS
even after the test manifest was resealed. The readback
`rehearsal-eco-01/independent-readback.json` has SHA-256
`b68422f2415e5923d715a1ab2f9f2ca5e62a2ba0ac548fd59d03290bbd912aa8`.

The package records qualified CMOS5L timing, electrical power and
shuttle acceptance as open. The metadata retains `clock_hz: 0`.
A fresh CAD replay uses the separately retained runtime, PDK and
historical proof inputs.
