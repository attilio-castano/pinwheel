# Physical correlation study

This record asks why three proved microarchitecture candidates left slow-corner
setup essentially unchanged, using only retained evidence from the completed
`command-split-closure` run. It starts no place-and-route run and changes no Lean
definition, emitted RTL or timing contract. [Research status](research/status.md)
owns the allocation; this document owns the measurements and proposed
discriminators below.

## Question

The [matched command-split comparison](successor-fetch-study.md#matched-command-split-physical-comparison)
misses 20 ns by 5.049 ns after F2 missed by 5.055 ns. Its worst path contains
13.704 ns of logic-cell delay and 9.813 ns of buffer delay. Logic alone would fit
the period. Is the limit the circuit's logic structure, or what the
implementation flow does with it?

## Finding 1: the optimizer believes timing is met

The resizer loads every STA corner (`RSZ_CORNERS` is unset, so LibreLane passes
`STA_CORNERS`), including slow 1.08 V / 125 °C. Its own worst-slack view of the
retained run is:

| Step | Parasitics | Resizer WNS before | Resizer WNS after |
| --- | --- | ---: | ---: |
| 37, post-CTS repair | placement estimate | −5.935 ns | +0.119 ns |
| 44, post-global-route repair | global-route estimate | −2.963 ns | +0.055 ns |
| 57, final STA | extracted (RCX) | — | **−5.049 ns** |

Post-CTS repair needed only 123 upsizes and 24 buffers to reach its goal, then
stopped. Post-global-route repair similarly needed 124 upsizes and 15 buffers.
The optimizer is not exhausted; it stops because its estimate says the design
passes. The 5 ns miss appears between the last repair and extraction.

## Finding 2: estimated wire capacitance is about half the extracted value

`scripts/fit-wire-rc.py` regresses extracted per-net wire capacitance and
resistance on routed per-layer length (and via count for resistance) over the
10,410 signal nets with at least 20 µm of routing (1.65 m total):

| Layer | Routed length | LEF cap used for estimates | Fitted extracted cap | Ratio |
| --- | ---: | ---: | ---: | ---: |
| Metal2 | 522 mm | 0.0930 fF/µm | 0.1611 fF/µm | 1.73 |
| Metal3 | 908 mm | 0.0920 fF/µm | 0.1924 fF/µm | 2.09 |
| Metal4 | 223 mm | 0.0918 fF/µm | 0.1393 fF/µm | 1.52 |

The capacitance fit has R² = 0.986; overall extracted capacitance is
0.178 fF/µm. The original resistance fit reported 0.70 / 0.58 / 0.48 Ω/µm,
15.9 Ω per via and R² = 0.993; those coefficients are affected by the parser
defect documented below and should not be reused as calibration. The
technology-LEF values are 0.515 Ω/µm and 20 Ω per cut. With no `LAYERS_RC` or
`SIGNAL_WIRE_RC_LAYERS` set, placement-stage capacitance estimates also average
in Metal1's lower 0.069 fF/µm.

The worst path shows the consequence. Net `_07298_` has two pins placed 581 µm
apart, 946 µm of routing and 0.179 pF of extracted wire load, driven by a
`nand3_1`: 1.88 ns for one stage with a 2.45 ns output slew. Net `_13207_`
(773 µm, 0.161 pF, `a22oi_1` driver) costs 1.61 ns. An optimizer that saw these
loads would upsize or buffer them; one that sees roughly a third of the load
(half the capacitance per µm, before detours) does not.

Inputs: routed DEF `e668da67…5db6a04` and nominal SPEF `6d4df224…2b2b536` from
`build/physical/core/runs/command-split-closure/` in the hardware-closure
worktree. Extraction used the PDK's nominal ruleset only; separate best/worst
RC corners remain unmeasured.

### Parser correction (2026-09-19)

Review found that the DEF parser treated physical lines as route segments and
counted patch `RECT` records as vias. It now follows logical `ROUTED`/`NEW`
segments across whitespace, with tests for known lengths, independent point
chains, wildcard coordinates, extensions and formatting-invariant fits.

The original `command-split-closure` DEF/SPEF pair is absent from this checkout,
so its historical coefficients above have not been recomputed. Reanalysis of
the retained `rc-calibrated-01` and `clock-gated-03` pairs found no change to any
net's layer lengths or to either capacitance fit. Correcting the patch counts
changed total vias from 338,188 to 282,102 and from 238,554 to 201,197,
respectively. For `rc-calibrated-01`, the fitted resistance becomes
0.5190 / 0.5174 / 0.5097 Ω/µm and 20.0928 Ω per via, with R² = 0.999980.
These are coefficients for that retained run, not replacements for the missing
original input pair.

The [comparison receipt](../physical/experiments/wire-rc-parser-review-results.json)
records the parser and input hashes. The original physical
configurations, receipts and extracted timing results are unchanged; this
correction involved parsing retained files, with no CAD execution.

## Finding 3: hold repair is a fifth of functional cell area

| Final cell class | Count | Area (µm²) | Share of functional area |
| --- | ---: | ---: | ---: |
| Sequential | 6,232 | 305,298 | 41.1% |
| Multi-input combinational | 25,034 | 272,436 | 36.7% |
| Timing-repair buffers | 10,886 | 138,085 | 18.6% |
| Clock buffers/inverters | 1,098 | 24,825 | 3.3% |
| Other (antenna, inverters, buffers) | 405 | 2,243 | 0.3% |

Post-CTS hold repair found 6,217 violating endpoints — essentially every
flip-flop — and the final netlist contains 6,423 `dlygate4sd3_1` hold cells
(16.3 µm² each, about 105,000 µm²). Storage bits hold their value through a
recirculating multiplexer, so each has a one-gate Q→D path that cannot meet
0.2 ns clock uncertainty plus the 0.1 ns repair margin at the fast corner.
Hold repair raised utilization from 70.4% to 82.1%. The resulting density is a
plausible contributor to the 1.6× route detours above, but this study does not
separate that effect.

Per stored bit the implemented cost is roughly flip-flop 49.0 + hold delay 16.3
+ recirculation multiplexer 18.1 µm² (where not absorbed into other logic) plus a
7.3 µm² tie cell on the unused asynchronous reset pin (6,232 tie cells were
inserted). The library has an integrated clock gate (`lgcp_1`, 27.2 µm²) and the
pinned LibreLane exposes Yosys `clockgate` through `SYNTH_CLOCKGATE_MIN_WIDTH` /
`SYNTH_CLOCKGATE_POSEDGE_ICG`. Gating a word's clock removes the recirculation
path, and with it that word's hold cells. This is a synthesis mapping choice:
the Lean netlist, emitted RTL and their proofs are unchanged, while
RTL-to-gate equivalence and the implemented-netlist regression must cover the
gated result.

### Synthesis-only clock-gating screen

One exploratory pair of synthesis-only runs (pinned container and PDK, the
command-split RTL and `core.json` from the retained experiment snapshot, stopped
after `Yosys.Synthesis`; about 38 seconds each on this host) differs only by
`SYNTH_CLOCKGATE_MIN_WIDTH = 8` and
`SYNTH_CLOCKGATE_POSEDGE_ICG = "sg13cmos5l_lgcp_1/GATE/CLK/GCLK"`:

| Synthesis result | Ungated | Clock-gated | Change |
| --- | ---: | ---: | ---: |
| Mapped cell area (µm²) | 578,449 | 505,878 | −12.5% |
| Cells | 31,431 | 24,090 | −23.4% |
| Flip-flops | 6,232 | 6,232 | 0 |
| Integrated clock gates | 0 | 67 | +67 |
| `mux2_1` | 3,834 | 2,493 | −35.0% |
| Tie-high cells | 6,232 | 6,232 | 0 |

This is a scratch screen without a retained receipt, gate equivalence or
regression; it justifies a properly recorded run, nothing more. The hold-cell
saving would appear only after clock-tree synthesis and is unmeasured. Both
netlists carry one tie cell per flip-flop (about 45,000 µm², 7.8% of ungated
mapped area) for the unused asynchronous reset pin; sharing those ties is a
further flow-level question, not examined here.

## What this does and does not establish

- The three logic-depth candidates were measured through a flow whose optimizer
  could not see the dominant delay term. Their near-identical routed slack is
  weak evidence about the architecture.
- The 20 ns miss has not been shown to be a flow artifact. Calibrated estimates
  make the optimizer work on the real problem; they may still not close it, and
  added upsizing/buffering needs area that an 82%-utilized core lacks.
- No frequency, fit or closure claim follows. Final timing remains extracted STA
  at all corners with the unchanged 20 ns / I/O contract.

## Proposed discriminators

Each is a flow control on byte-identical RTL, so no new Lean proof is needed and
existing read-back results carry over.

1. **Calibrated estimates.** `physical/experiments/rc-calibrated.json` is F2 plus
   the fitted `LAYERS_RC` for all corners and Metal2/Metal3 as the signal
   estimation layers. `scripts/run-physical.py` accepts those two additional
   override keys. Compare extracted slow setup, violation counts, repair-buffer
   area and final utilization against the retained command-split run. Success is a
   material fall in the estimate-to-extraction gap (resizer final WNS versus
   step-57 slow WNS), not merely a better headline slack.
2. **Clock-gated storage (synthesis screen first).** Compare mapped area,
   flip-flop/ICG counts and hold-endpoint counts with and without
   `SYNTH_CLOCKGATE_*`. Route only if the screen removes most recirculation
   multiplexers. Gated clocks add clock-tree skew and an enable-setup path per
   gate; both must appear in the comparison.
3. **Density.** Only after 1–2: if utilization still exceeds about 70%, repeat at
   a lower placement density within the official 8×4 outline rather than the
   diagnostic 6×4 rectangle.

Run 1 and 2 separately before combining them; otherwise an improvement cannot
be attributed.

## Result: calibrated estimates (`rc-calibrated-01`)

Authorized 2026-09-17 as one bounded run: four CPUs, 6 GiB, one-hour cap, no
network, pinned container/PDK, stop after `OpenROAD.STAPostPNR`. Inputs are the
hash-verified command-split RTL (`1a1fd62b…04cc5a42`), the unchanged 20 ns clock,
I/O constraints and 6×4 diagnostic floorplan, and
`physical/experiments/rc-calibrated.json`. It exited 0 after about 35 minutes of
step time. Magic DRC, LVS and later layout checks were deliberately not run, so
this is extracted timing on a routed design, not a layout sign-off.

| Extracted metric | Command split (F2) | Calibrated estimates |
| --- | ---: | ---: |
| Slow setup worst slack | −5.049 ns | **−0.153 ns** |
| Slow setup total negative slack | −1,564.1 ns | −5.4 ns |
| Slow setup-violating endpoints | 1,426 | 56 |
| Typical / fast setup worst slack | +3.157 / +7.516 ns | +5.707 / +8.361 ns |
| Worst hold slack, fast corner | +0.0029 ns | +0.0862 ns |
| Slew / capacitance violations | 49 / 3 | 0 / 0 |
| Fanout violations | 21 | 25 |
| Resizer final view, post-CTS / post-GRT | +0.119 / +0.055 ns | +0.088 / +0.012 ns |
| Timing-repair buffer area | 138,085 µm² | 142,902 µm² |
| Utilization after detailed routing | 82.3% | 82.9% |
| Routed wirelength | 1.914 m | 1.927 m |

The estimate-to-extraction gap falls from about 5.1 ns to about 0.17 ns for 0.6
points of utilization. This confirms Findings 1–2: the earlier miss was mostly
an optimizer working from under-estimated wire load. It does not close timing:
56 slow-corner endpoints still fail, fanout violations remain, and layout checks
are outstanding.

The remaining worst path starts at the `incoming[1]` **input port** and ends in
the current-word cache, so it includes the 4 ns external input-delay budget. The
proposed [two-register input pipeline](external-interface.md) would launch that
path from a register instead; whether that closes the family must be measured on
a design that contains the pipeline, with its latency composed into the protocol
bounds.

Receipts: `build/physical/rc-calibrated-01-invocation.json` (config SHA-256
`7ffe348d…9c2fc0cc`), `build/physical/rc-calibrated-01.log`, and the run directory
`build/physical/core/runs/rc-calibrated-01/`; final STA summary SHA-256
`2d195b98…3f2cd10`. One run on one host; no repeat or seed variation was measured.

## Result: clock-gated storage on the calibrated control (`clock-gated-01`, failed)

Same authorization, limits, RTL, constraints and floorplan as `rc-calibrated-01`;
`physical/experiments/clock-gated.json` adds only `SYNTH_CLOCKGATE_MIN_WIDTH = 8`
and the `lgcp_1` gate. The run **failed at global routing** (exit 2, `GRT-0116`)
after about 13 minutes. There is no routed design and no extracted timing.

| Mid-flow measurement | Calibrated control | Clock-gated |
| --- | ---: | ---: |
| Instances / utilization after detailed placement | 35,888 / 67.7% | 27,319 / 58.9% |
| Cell area after post-CTS timing repair | 742,324 µm² | 604,627 µm² (−18.5%) |
| Utilization after post-CTS timing repair | 82.3% | 67.0% |
| Clock roots / clock buffers | 1 / 1,033 | 69 / 1,127 |
| Hold-violating endpoints before post-CTS repair | 6,208 | 4,581 |
| Global-route wirelength | — (1.927 m detailed) | 2.312 m |
| Global-route overflow | 0 | 526 (515 on Metal3) |

The area hypothesis holds: gating removes about 138,000 µm² after clock-tree
synthesis and hold repair. The routing result does not: with a quarter fewer
cells the global route is about 20% longer and Metal3 overflows. One untested
explanation is that the unchanged 70% placement-density target packs a 59%-utilized
design into pin-dense clusters, where the control's hold-delay cells previously
diluted pin density. Mid-flow timing numbers are estimates and are not compared.
The failed run is retained under `build/physical/core/runs/clock-gated-01/` with
`build/physical/clock-gated-01-invocation.json` and its log. The gated netlist has
had no functional regression or gate equivalence; none is claimed.

### Retry at lower placement density (`clock-gated-02`, failed later)

Authorized as one retry with one change: `PL_TARGET_DENSITY_PCT` 70 → 62
(`physical/experiments/clock-gated-spread.json`). Spreading removes the first
failure: three global routes complete with zero overflow at about 2.23 m and
Metal3 at 67% of its derated capacity. The run then **fails at step 44**
(`OpenROAD.ResizerTimingPostGRT`, exit 2, `GRT-0116`): after post-route design
repair and antenna repair (56 jumpers, 118 diodes), the next global route is
2.384 m with Metal3 at 70.0% and a total overflow of **3**. No detailed route,
extraction or final timing exists. Post-CTS-repair area and utilization repeat
the first attempt (604,163 µm², 67.0%).

Metal3 is the only horizontal signal layer under the template's Metal4 routing
ceiling, and the diagnostic rectangle is 1.8 times wider than tall. The calibrated
control also runs Metal3 at 72.7% of derated capacity, without overflow. The
official 8×4 outline is wider still, so horizontal routing capacity, not cell
area, may be the binding fit constraint; that is a hypothesis for the wrapper
floorplan, not a measurement. A third attempt would need its own allocation and
one stated change, such as allowing the detailed router to resolve marginal
global overflow while keeping the final routing-DRC gate.

### Third attempt: `clock-gated-03` routes

Authorized 2026-09-17 with one change from `clock-gated-02`:
`GRT_ALLOW_CONGESTION` (`physical/experiments/clock-gated-tolerant.json`) leaves
remaining global overflow to the detailed router, while the detailed-routing DRC
gate still fails the run on any violation. The run exits 0. Its global routes
report total overflow of 0, 0, 0, 3 and finally 0; detailed routing and the
antenna check finish with zero violations.

| Extracted metric | Calibrated control (`rc-calibrated-01`) | Clock-gated (`clock-gated-03`) |
| --- | ---: | ---: |
| Functional cell area | 748,353 µm² | **608,454 µm² (−18.7%)** |
| Utilization after detailed routing | 82.9% | **67.4%** |
| Timing-repair buffers | 10,952 / 142,902 µm² | 6,112 / 73,175 µm² |
| Multi-input combinational cells | 25,034 / 272,770 µm² | 17,678 / 200,388 µm² |
| Clock buffers + inverters / clock gates | 1,098 / 0 | 1,171 / 67 |
| Routed wirelength | 1.927 m | 1.670 m |
| Slow setup worst slack / violating endpoints | −0.153 ns / 56 | −0.617 ns / 16 |
| Slow setup total negative slack | −5.4 ns | −3.4 ns |
| Typical / fast setup worst slack | +5.707 / +8.361 ns | +5.230 / +7.530 ns |
| Worst hold slack (fast corner) | +0.086 ns | **+0.003 ns** |
| Setup / hold violations outside the slow corner | 0 / 0 | 0 / 0 |
| Slew / capacitance / fanout violations | 0 / 0 / 25 | 11 / 0 / 18 |

The 67 gates cover the 64 dictionary words (55 flip-flops each), the two
last-address registers and the cached word. The 512 five-bit index registers
stay ungated at a minimum width of eight. As in the control, every violating
slow-corner path launches from the `incoming` ports (worst −0.617 ns); the loader
`data` family is at +0.997 ns. That is the family the
[pin sampler](pin-sampler-study.md) removes, so the two changes are
complementary, but their combination is unmeasured. Hold is met with only
3.4 ps at the fast corner: gated clock branches add skew, and a submission flow
would need explicit hold margin.

**Functional evidence.** The routed gated netlist passes the implemented-netlist
regression against the oracle vectors and the source RTL (28,165 edges,
4,618,982 defined output-bit comparisons; output-corruption mutant rejected).
`scripts/check-clock-gates.py` then ties each gate's enable to 0 and to 1 in turn.
With the existing vectors only **84 of 134** such mutants are rejected: all 50
survivors are the gates of bank-0 words 25–31 and bank-1 words 14–31, which no
earlier trace ever executes. That is a coverage gap in the shared regression,
not specific to gating. `scripts/measure-storage-variant.py` now also fills and
executes all 32 dictionary words of each bank (29,062 edges). With those vectors
the routed netlist still passes (4,766,090 comparisons) and **134 of 134**
stuck-enable mutants are rejected. This is zero-delay gate simulation and trace
sensitivity; it is not an equivalence proof. Equivalence across clock gating and
technology mapping remains open.

A further scratch synthesis-only screen gates registers down to five bits: mapped
area 455,658 µm² with 582 gates, against 505,878 µm² (67 gates) and 578,449 µm²
ungated. It has not been placed, routed or checked; 582 gated branches would
stress clock-tree synthesis and hold.

Per-family extracted STA (`check-targeted-timing.py`) for this run, slow corner:
`incoming` −0.617 ns, `init`/`reset` −0.545, `command` −0.327, registers −0.058
(one path), `data` +0.997. Every worst path ends at the clock gate of
`r_cached_word`, where the clock arrives 0.68 ns before it reaches the launching
flip-flops. The [combined run](pin-sampler-study.md#combined-with-clock-gating)
with the pin sampler shows the same endpoint missing by 2 ns.

[Physical manifest](../physical/experiments/clock-gated-physical-results.json)
pins the receipts for the control, both failed attempts and this run.

## Reproduction

```sh
python3 -B -m unittest discover -s test -p 'test_fit_wire_rc.py'
python3 scripts/check-physical-netlist.py NETLIST --design core --label NAME --vectors VECTORS
python3 scripts/check-clock-gates.py NETLIST --label NAME
python3 scripts/fit-wire-rc.py \
  --def  build/physical/core/runs/command-split-closure/54-openroad-fillinsertion/pinwheel_atomic_small_dense_cached.def \
  --spef build/physical/core/runs/command-split-closure/56-openroad-rcx/nom/pinwheel_atomic_small_dense_cached.nom.spef
```

The unit test recovers known per-layer capacitance, resistance and via values
from a synthetic routed design and rejects thin or unrouted inputs.
