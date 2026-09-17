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
0.178 fF/µm. Fitted resistance (0.70 / 0.58 / 0.48 Ω/µm, 15.9 Ω per via,
R² = 0.993) is close to the technology-LEF values (0.515 Ω/µm, 20 Ω per cut).
Resistance is not the discrepancy; capacitance is. With no `LAYERS_RC` or
`SIGNAL_WIRE_RC_LAYERS` set, placement-stage estimates also average in Metal1's
lower 0.069 fF/µm.

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

## Reproduction

```sh
python3 -B -m unittest discover -s test -p 'test_fit_wire_rc.py'
python3 scripts/fit-wire-rc.py \
  --def  build/physical/core/runs/command-split-closure/54-openroad-fillinsertion/pinwheel_atomic_small_dense_cached.def \
  --spef build/physical/core/runs/command-split-closure/56-openroad-rcx/nom/pinwheel_atomic_small_dense_cached.nom.spef
```

The unit test recovers known per-layer capacitance, resistance and via values
from a synthetic routed design and rejects thin or unrouted inputs.
