# Pinwheel 8×4 frozen-candidate timing audit

The November 4 nominal-RC diagnostic found one hold endpoint violating in
the fast and typical Liberty scenarios and five driver outputs above the
Liberty fanout limit in all three scenarios. The endpoint arithmetic depends
on the external timing contract and RC model. The five load counts follow
directly from the frozen connectivity and pinned Liberty. This audit reopened
the retained outputs without running CAD or changing the candidate.
[Rehearsal record](streaming-8x4-tt-rehearsal-20261104.md)

## Hold endpoint and contract sensitivity

The path starts on falling data at `ui_in[5]` (Host MOSI 1 in the
handoff metadata) and ends at `engine.frontend._0230_/D`, the
`sg13cmos5l_dfrbpq_1` storing `frontend:r_request:1`. Both timing
references are the same rising edge of `clk`. The data traverses
`input8/A→X`, `engine.frontend._1954_._530_/A1→X`,
`engine.frontend._1955_._505_/B_N→Y`, and
`engine.frontend._1956_._505_/B_N→Y`. The capture clock traverses
`clkbuf_0_clk`, `clkbuf_2_0_0_clk`, `clkbuf_5_3_0_clk`, and
`clkbuf_7_12__f_clk`, then reaches the flop through
`clknet_7_12__leaf_clk`. The raw DEF, native ODB terminal inventory, and
G4 state map identify the same endpoint. [Pin map](../../info.yaml)

All time values below are ns except the hold-slack column. The signed
hold term is the Liberty-derived path contribution printed by STA.

| Cell PVT with nominal RC | Data arrival | Capture clock arrival | Uncertainty | Library hold term | Data required | Hold slack (ps) | Worst setup (ns) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Fast, 1.32 V, −40 °C | 0.595565 | 0.438009 | 0.200000 | −0.017748 | 0.620261 | −24.696 | +10.266 |
| Typical, 1.20 V, 25 °C | 0.792908 | 0.627234 | 0.200000 | −0.026807 | 0.800427 | −7.519 | +8.143 |
| Slow, 1.08 V, 125 °C | 1.157383 | 0.940868 | 0.200000 | −0.035258 | 1.105610 | +51.773 | +2.463 |

Clock reconvergence pessimism is zero on this path. The SDC declares a
20 ns clock, 0.200 ns uncertainty, 0.150 ns clock transition, 0.200/4.000
ns input and output min/max delays, an `sg13cmos5l_buf_2/X` nonclock
input driver, and 0.010 pF (10 fF) output load. The standalone STA
logs read the source `core.sdc` with `OPENLANE_SDC_IDEAL_CLOCKS=0`,
which selects `set_propagated_clock`. The written SDC agrees. The
capture arrivals above come from the expanded endpoint path.

For this edge and fixed data/clock delays, slew and library lookup,
`new slack = old slack + change in minimum input delay − change in hold uncertainty`.
With 200 ps uncertainty, this endpoint reaches zero at minimum input
delays of 224.696 ps fast, 207.519 ps typical and 148.227 ps slow.
With 200 ps minimum input delay, the corresponding uncertainty ceilings
are 175.304 ps, 192.481 ps and 251.773 ps. Adding 25 ps to the assumed
minimum leaves only 0.304 ps of fast diagnostic margin. A longer period
leaves the same-edge calculation unchanged at fixed relative I/O
budget. These thresholds are local sensitivities. The retained
`max.rpt` files each list 1,000 setup paths and give no
`ui_in[5]`-specific setup path.

Confirm the earliest and latest data arrival at the macro relative to its
clock, including the actual mux or host drive, board or harness phase,
loads and clock uncertainty, before changing the constraint or sizing a
hold fix. The diagnostic used one nominal SPEF across three cell PVT
scenarios. The SPEF declares ns, pF and ohms and comes from a legacy
seven-layer deck for this five-routing-layer design. Each scenario
reports 282 unannotated drivers and zero after the LibreLane filter.
The filter count and PVT sweep leave RC qualification open.
[Qualified timing intake](streaming-8x4-e982-timing-intake-20261104.md)

## Clock propagation readback

The `clock.rpt` header's `Virtual: yes` and `Propagated: no` come
from a LibreLane formatting defect. In the runtime's
`scripts/openroad/sta/corner.tcl`, lines 364–386 initialize both
labels to `no`, then set the variable for `Virtual:` when either
`is_virtual` or `is_propagated` is true. The variable printed as
`Propagated:` stays `no`. Lines 351–359 independently enumerate the
same clocks and print a name if its actual OpenSTA
`get_property $clock is_propagated` is false. Each original `sta.log`
contains a single empty, delimited `unpropagated.rpt` section
immediately followed by the `clock.rpt` section with one clock,
`clk`, sourced at the public `clk` input. Those retained same-process
queries establish `is_propagated = 1` at all three corners.

The frozen DEF, ODB terminal inventory and nominal SPEF `*CONN`
sets agree on all terminals of the five clock-path nets. The standalone
STA netlist has the same four buffer arcs and pin connections from the
public `clk` to `engine.frontend._0230_/CLK`. Resolving the SPEF
`*NAME_MAP` and traversing each `*RES` graph connects the driver to the
selected sink on each segment. All three raw `min.rpt` files show
nonzero delay through that same chain.

| Clock-path net | SPEF ID | Terminals including driver | Resistor records |
| --- | --- | ---: | ---: |
| `clk` | `*3` | 2 | 6 |
| `clknet_0_clk` | `*46` | 5 | 19 |
| `clknet_2_0_0_clk` | `*47` | 9 | 31 |
| `clknet_5_3_0_clk` | `*76` | 5 | 10 |
| `clknet_7_12__leaf_clk` | `*114` | 8 | 18 |

This readback required no additional native run. It establishes clock
propagation and connection on the original nominal-RC diagnostic.
Qualified STA still needs the admitted RC model and I/O contract.

## Fanout and antenna loads

Each driver is `sg13cmos5l_buf_1/X`. All three Liberty files set
`default_max_fanout = 8` and `default_fanout_load = 1`. The driver
pin and the connected sink pins have no per-pin overrides. Fanout is
a dimensionless sum of sink weights, distinct from capacitance. Neither
the source nor the written SDC contains `set_max_fanout`. The
`MAX_FANOUT_CONSTRAINT = 10` field in the resolved flow configuration
therefore does not explain the limit in the raw checks, which print 8
at every driver below.

| Driver / net | Functional sinks | Antenna inputs `ANTENNA_<ID>/A` | Total | Excess over 8 | Historical f516 total |
| --- | ---: | --- | ---: | ---: | ---: |
| `fanout2157/X` / `net2157` | 8 | 145, 146, 147, 148 | 12 | 4 | 8 |
| `fanout2298/X` / `net2298` | 8 | 157, 158 | 10 | 2 | 8 |
| `fanout11223/X` / `net11223` | 4 | 76, 79, 80, 82, 154 | 9 | 1 | 8 |
| `fanout2333/X` / `net2333` | 8 | 151 | 9 | 1 | 8 |
| `fanout840/X` / `net840` | 6 | 140, 156, 160 | 9 | 1 | 7 |

The f516 DEF and inventory have the same five functional sink sets.
Their respective diode counts are 0, 0, 4, 0 and 1. The pre-bridge DEF
has the same terminal sets as the frozen successor on all five nets,
including `net840`. The bridge changed routing geometry while the
load count was already nine. The raw diagnostics show zero setup,
slew and capacitance violations in all three scenarios. Any physical
fanout correction needs a new frozen candidate and fresh checks,
including antenna on every affected branch.

## Reopen the evidence

Paths below are relative to the repository unless prefixed by
`$H` or `$P`. Set `$H` to the retained campaign archive's
`build/campaigns` directory.
`$P` is
`$H/8x4-20261022-01/recovery/balanced-prepared/build/physical/streaming-tt-balanced-d2-01/pdk/ihp-sg13cmos5l`.
`$R` is `build/e982-whole-route-20261104/native`, `$T` is
`build/tt-rehearsal-20261104/timing-diagnostic`, and `$V` is
`build/tt-rehearsal-20261104/views/actual-signal`.

| Input or evidence path | SHA-256 |
| --- | --- |
| `$R/flow/09-openroad-fillinsertion/tt_um_pinwheel_streaming_ready_d2.odb` | `b7e60eded5198fc53df7e5dd1e3ab0f5162720516ab0c1692a1cf7c7bb62602b` |
| `$R/design.gds` | `041ff30708e46be33db330e2f1dcafab889824b689499e931ec9d180a11c1689` |
| `$R/design.def` | `8802555ed7800ac6bcf92680793380d4a0a4deee0f7e6cd584044c084fe86350` |
| `$R/flow/09-openroad-fillinsertion/tt_um_pinwheel_streaming_ready_d2.nl.v` | `6d3994230c8b56f99db0fce61ca1ebfddbd13de96d792b03605ee8107a05593c` |
| `$V/receipt.json` | `cafc5f3862c53daff61e71ac0586b502fa6b047092e0c8821dc2c444fa04f42b` |
| `$V/inventory.json` | `00d4790acec3550a6a176566fae6abaa6f150903aeb2a6d4b640cf75dc1afd10` |
| `build/e982-g4-20261104/semantic-state-map.json` | `22e31c36a0c485c0abcc16c95158211aa44e0896dd5a31ab9ff0860b28505c2a` |
| `$H/8x4-20261022-01/prepared-8x4-02/inputs/core.sdc` | `bcfd5a3ee86ccf13d6a8851e4b8d05b02584926862b922efa00204b3f628d0e5` |
| `$R/flow/09-openroad-fillinsertion/tt_um_pinwheel_streaming_ready_d2.sdc` | `73ce99876d64525e1d62c896f1ce8734edce2b49737898072f1772461c03cbe1` |
| `$P/libs.tech/librelane/IHP_rcx_patterns.rules` | `ffda02d57a6ecb39b02268be9511d89ef072911f17bd2dcd095f3f3cbeb5a905` |
| `$T/flow/01-openroad-rcx/nom/tt_um_pinwheel_streaming_ready_d2.nom.spef` | `fd589d6f00b03dc8507663c85bf081e4a9f8d5936b1e2b061f1a9d4cdbc1ebae` |
| `$T/diagnostic-readback.json` | `e865c863bcc6ab4038e415d1c35eedd45d77835cf23e75bf1eb5254bef02c764` |
| `$H/8x4-20261024-01/final24-views-01/design.def` | `7a55a065eda994064e24eed5349a792ce3059e2db17bbae57eac6b3d9df24565` |
| `$H/8x4-20261024-01/final24-views-01/actual-signal/inventory.json` | `3b610a70a368ff55daa7bebc8c06fd11e6e37e830fc9fbfd9a8e00e7a26b2e26` |
| `$H/8x4-20261025-01/antenna48-policy2-cheap-01/apply/native/before/design.def` | `daf6a5ac430ff4dec07243d3de2a31d0816fbd9ad5c5f56b7f6c388496c289e2` |

PDK revision `2bbec755dc67ca3db0261c3d6163e15735d66710`.
The Liberty files are under `$P/libs.ref/sg13cmos5l_stdcell/lib`.
`$T/execution.json` records the exact native invocation and runtime
image digest `sha256:5825633bea1f9cbc705ece2de2bc31de6e4ec83d233739205a0f265ef9d92f92`.

For the clock readback, `$L` is
`$H/8x4-20261022-01/intake/librelane-native-source`.
The `$L/manifest.json` source-copy receipt binds the source file
below to the same image digest and installed script path recorded in
the retained STA `COMMANDS`. The three raw logs retain the property
query's delimiters, so an empty extracted report alone is insufficient.

| Clock evidence path | SHA-256 |
| --- | --- |
| `$L/manifest.json` | `b623539e6046f1c06766c860a6f959e558fc9586b2d15e7bffa4ee177bcab8f9` |
| `$L/librelane/scripts/openroad/sta/corner.tcl` | `e0096884c1929ed80506366ecc3e809c78c8493180e366fc095e2b09f5c36f53` |
| `$T/flow/02-openroad-stapostpnr/COMMANDS` | `489b026de87a4a48fd4b303bc1cd296e0d4bc2e00adefafe3f2753f595c20055` |
| `$T/flow/02-openroad-stapostpnr/nom_fast_1p32V_m40C/sta.log` | `59c8c38fb45e5a62eb23e8dc7ea78eaec319c4a79f80d3bd1b9f16798c4855c8` |
| `$T/flow/02-openroad-stapostpnr/nom_typ_1p20V_25C/sta.log` | `96d2677eb62d81efff5d275824e43abe835c69bbed6745ffdf6055a256cd3091` |
| `$T/flow/02-openroad-stapostpnr/nom_slow_1p08V_125C/sta.log` | `4007524b5c6902f981dddf25587adcc9e51a070212c20c9fd2a62b5ed8895879` |

| Liberty file | SHA-256 |
| --- | --- |
| `sg13cmos5l_stdcell_fast_1p32V_m40C.lib` | `af12d75a72d19648fa690027d29843fbae550aa91f4e40dd3339c7116d6e425d` |
| `sg13cmos5l_stdcell_typ_1p20V_25C.lib` | `34163f3e7de9f854afac57332ba06f1739b78e7ac35660a8a5ddd39c570124ad` |
| `sg13cmos5l_stdcell_slow_1p08V_125C.lib` | `3ee222c580ba33acb2131ac2bf224ff8ee9700751835b73aaec72b670bb31d3c` |

1. Verify the hashes with `shasum -a 256`. The readback lists the
   scenario-specific raw hashes. Under
   `$T/flow/02-openroad-stapostpnr/nom_{fast_1p32V_m40C,typ_1p20V_25C,slow_1p08V_125C}/`,
   read the first path in `min.rpt` through the required-time and
   slack lines, then compare `ws.min.rpt`, `ws.max.rpt`, and the
   fanout table in `checks.rpt`. Use `sta.log` and
   `filter_unannotated_metrics.json` for the two annotation counts.
2. Find each named net in the DEF `NETS` section. Compare the
   `( instance pin )` pairs before the first route property `+` with
   `instances[*].terminals[*].net` in the ODB inventory. Treat public
   `( PIN name )` pairs as `public_bterms`. The DEF declares 1,000
   database units per micron. For the five fanout nets count only
   input terminals, grouping `CORE_ANTENNACELL` separately. Compare
   functional terminal sets with f516 and the full sets with the
   pre-bridge DEF. The native inventory receipt binds the frozen ODB.
3. For each Liberty file read the library-level fanout defaults, then
   check `sg13cmos5l_buf_1/X` for a `max_fanout` override and each
   distinct input master/pin for a `fanout_load` override. The
   [repository Liberty parser](../../scripts/streaming_mapped_liberty.py)
   can reopen those groups. Compare the resulting limit and sums with
   the raw fanout table and check the emitted SDC for an override.
