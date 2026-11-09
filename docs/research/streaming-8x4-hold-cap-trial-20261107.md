# 8×4 hold and capacitance trial, November 7, 2026

Carry this derivative forward for physical requalification. Fresh extraction
and the nine local STA cases pass setup, hold, signal capacitance, slew and
fanout under the retained draft models and unchanged integration assumptions.
Qualified CMOS5L extraction, the accepted host I/O budget and electrical power
qualification remain open. At completion of this timing trial, the new GDS also required its own
full physical signoff replay before adoption.

The [physical follow-up](streaming-8x4-hold-cap-physical-20261107.md)
subsequently passed main-deck DRC, transistor LVS, supplemental enclosure
and foundry antenna on this exact candidate.

The [digital follow-up](streaming-8x4-hold-cap-digital-precheck-20261107.md)
subsequently passed fresh complete-state correspondence, public-pin replay
and all nine pinned Tiny Tapeout prechecks on the same candidate.

## Changes and physical scope

The starting point was the previously checked five-net fanout ECO, ODB
`e40e40804ddf5c4093f83710ec27b0a5b975f3a047e5c95810e175fbe6aa78f9`
and GDS `dcc496d71202677f6d2fe3785dca6ff9bb225ef954953bf7925171174d4b7e82`.
The derivative adds one non-inverting `sg13cmos5l_dlygate4sd2_1` between
`engine.frontend._1956_.Y[1]` and `engine.frontend._0230_/D`. It replaces
`fanout2219`, `fanout1798`, `fanout2439`, `fanout875`, and `fanout2425`
with `sg13cmos5l_buf_2`. Their characterized output capacitance limit is
0.600 pF across all three pinned cell corners, compared with 0.300 pF for
the original `buf_1` cells. All three masters implement A→X without inversion.

No suitable ordinary-filler footprint existed for the larger cells under
the retained power-grid blockage mask. The trial reclaimed nearby decap
footprints, restored a `decap_4` in each old buffer footprint, and filled
remaining sites. Relative to the starting ECO the census changes are
`buf_1 -5`, `buf_2 +5`, `dlygate4sd2_1 +1`, `decap_4 +3`, `decap_8 -4`,
`fill_1 +5`, and `fill_2 -1`. The new inventory contains 98,904 instances.
The power result verifies terminal connectivity. Supply droop and effective
rail capacitance need the supply model and activity described in the
[timing intake](streaming-8x4-e982-timing-intake-20261104.md).

Placement passed before and after routing. DRT finished with zero markers,
and OpenROAD antenna reported zero net and pin violations. These are the
router and OpenROAD antenna checks. Full foundry DRC, enclosure, foundry
antenna, transistor LVS, digital correspondence and Tiny Tapeout precheck
must be replayed on this derivative before release promotion.

DRT changed 43 existing wire records, comprising 11 declared existing nets
and 32 collateral nets, and added the delayed-data net. Of the collateral
changes, 31 are signal routes and one is `clknet_leaf_721_clk`. The first
scope check rejected the clock-route change. The follow-up explicitly
admits this named leaf for the experiment and extracts its new geometry
with propagated clocks in every timing case. Its terminals are unchanged.
All other clock records and every FIXED record, including `net840`, match
the starting DEF. Every regular-net terminal set matches the source except
the exact declared hold split. Fresh independent ODB-to-DEF export matches
the routed DEF bytes, and every instance has VDD→VPWR and VSS→VGND.

## Extracted timing results

The retained five-layer MIN, TYP and MAX rules each produced a distinct,
structurally validated SPEF graph. All nine cases passed the relevant
annotation checks. The unchanged SDC uses a 20 ns clock, 0.2 ns minimum
input/output delay, 4 ns maximum input/output delay, 0.2 ns uncertainty,
`buf_2` input drive and 0.010 pF output load. Every case uses propagated
clock latency. These are provisional integration assumptions.

| Draft RC | Liberty PVT | Global setup slack, ns | Global hold slack, ps | Repaired path hold slack, ps | Cap/slew/fanout violations |
| --- | --- | ---: | ---: | ---: | ---: |
| MIN | fast | 10.385129 | 36.872 | 75.455 | 0 |
| MIN | typ | 8.712947 | 120.822 | 133.135 | 0 |
| MIN | slow | 3.186560 | 264.114 | 264.114 | 0 |
| TYP | fast | 10.219832 | 38.047 | 60.480 | 0 |
| TYP | typ | 7.829629 | 114.591 | 115.319 | 0 |
| TYP | slow | 2.179736 | 244.387 | 244.387 | 0 |
| MAX | fast | 10.138214 | 31.572 | 45.780 | 0 |
| MAX | typ | 7.347639 | 99.621 | 99.783 | 0 |
| MAX | slow | 1.554538 | 227.389 | 227.389 | 0 |

All setup and hold violation counts and total negative slack are zero.
Worst global hold is +31.572 ps at MAX/fast. The repaired falling-input
path has at least +45.780 ps across the matrix, compared with an original
worst deficit of −95.618 ps. Worst setup is +1.554538 ns at MAX/slow,
about 4.8 ps below the original ECO's +1.559338 ns.

All previous capacitance violations clear, including the loads upstream
of the resized buffers. The complete native electrical-check counts are
zero in each case. This sweep remains draft-model evidence because the
canonical extractor uses `-lef_res` for ordinary wire/generated-via
resistance and the RC-to-Liberty pairing has no foundry admission.
Dedicated recovery/removal/pulse-width coverage and a complete inventory
of unconstrained endpoints remain open in this diagnostic flow.

## Reproduction and custody

The [runner](../../scripts/streaming_8x4_hold_cap_trial.py) supports `route`,
`review`, and `timing`. Use a fresh output directory for a new route and
retain the local history input used by the original rehearsal. For example,
with `PINWHEEL_HISTORY` pointing to that checkout, run the following.

```sh
python3 -B scripts/streaming_8x4_hold_cap_trial.py route \
  --history "$PINWHEEL_HISTORY" --out build/8x4-hold-cap-20261107/new-trial
python3 -B scripts/streaming_8x4_hold_cap_trial.py timing \
  --history "$PINWHEEL_HISTORY" --out build/8x4-hold-cap-20261107/new-trial
python3 -B scripts/streaming_8x4_e982_eco_timing_readback.py \
  build/8x4-hold-cap-20261107/new-trial/timing \
  --trial-layout build/8x4-hold-cap-20261107/new-trial/layout.json
```

Raw evidence stays local in the ignored directory
`build/8x4-hold-cap-20261107/trial-02/`. The native routing worker was
committed source `1058913`, preserved as `native-producer-1058913.py`
with the same digest as the request. The host checks and timing launch
used `74f743f`. During routing, later commits added the host verifier and
future worker snapshotting. The already-loaded native worker remained
at the preserved source version. The initial `trial-01` stopped before
routing because ordinary fillers could not hold the enlarged buffer.

The independent readback binds the exact ODB, GDS, views, SDC, models,
Liberty libraries, native image, calls and raw results. A mismatched
explicit layout manifest was also tested and rejected. Source baseline
custody checks passed before and after the native jobs. All work and
commits stay on `codex/8x4-timing-closure` in the existing worktree.

| Local artifact | SHA-256 |
| --- | --- |
| `trial.odb` | `dc654986c54512095c243407ea481ad3675a0269870ee4715dcbd1bd632c6a73` |
| `trial.def` | `0ebc4418da924037d2c9cb5beeff5a7d9c830b5ca8091a5cdf1616b790475962` |
| `stream/design.gds` | `d4cd48f0919ac47ec4b2ceb061bc5dc6a217ce730b02b819a6b7e09d9e73c832` |
| `request.json` | `fc3eddf6a4cf4e1cc38ff11938eff3c2d6987a75476aeb0c486a968d8e8c8137` |
| `native-producer-1058913.py` | `d5fe5f66fa35c7995c2e449b5ed2f99c1e10c9b7f3f6a303a4c103c207aa49f1` |
| `edits.json` | `a64e9d30e4a9e2216cde560d0d57978e98671cacdc1df560e8704ebe90c32f9b` |
| `route-readback.json` | `fba82f60d4c312e2a90c42476b61b02861faf5b25893c9e8d43a5a235d108457` |
| `connectivity-readback.json` | `53f9d54453053d7d7f69cda953f012e24c2c062d29d2207915703ab19cc72b7f` |
| `rail-readback.json` | `fc07bcf4132faa8eac7f4928559cea9b0fae9916612de3d2539435793fb830d5` |
| `views/rehearsal-view-readback.json` | `1ffd35b51c7367380745356b78aaaeb9ec8b774cdd6723ab51f613b0c7c26729` |
| `timing/native-readback.json` | `62b5ef3e7735ec4e73c248792fd0476371461adaf9f93f5e7442c3bda2e751e8` |
| `timing/timing-readback.json` | `aaf351d84af3ae653a05999f8d5a402940596e0408abda69089f0e066cdba45c` |
