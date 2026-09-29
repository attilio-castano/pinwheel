# Balanced signal distribution

**Follow-up:** [seven-net electrical repair](balanced-electrical-experiment.md)
clears this experiment's remaining electrical nets. The
[second detailed layout](balanced-detailed-experiment.md) now owns the measured
extracted result and remaining gates. The results below retain this earlier
experiment's original stage and verdict.

**Retain the balanced mapping as the next physical candidate.** The September
26 experiment reduces initial coarse-route overflow from **8,911 to zero** and
improves slow setup from **−9.286980 to −0.982379 ns** at the same flow stage.
Completed post-route repair then reaches **+0.820730 ns** slow setup with zero
overflow. Four capacitance and 23 slow slew violations remain, so the candidate
is not admitted to the remaining detailed-route attempt.

The [manifest](../../physical/experiments/buffer-balance-results.json) binds the
mapping, both actual physical circuits, checks and resource ledger.
[Research status](../research/status.md) owns the current decision; the
[complete-iteration plan](../research/complete-design-iteration.md) retains the
larger A/B outcome and its acceptance gates.

## Hypothesis and implementation

The [validation-isolation layout](validation-isolation-experiment.md) removed
the intended SRAM-to-rejection dependency, but its new worst path traversed
nine minimum-strength buffers. Those cells already existed in the mapped
circuit. Its 983 positive buffers form trees as deep as eight levels; the
active-bank tree reaches 74 consumer pins through as many as seven levels.

`scripts/mapped_buffer_balance.py` contracts only known positive buffers and
rebuilds their trees with the existing distribution helper. It orders leaves
using a deterministic spatial ordering of coordinates from the preceding saved
layout. Every retained gate, register, macro and connection must match after
buffer contraction. Clock trees are excluded. This is an opt-in policy applied
to the same verified `PairedValidation` RTL, with the same buffer master and
eight-load limit.

The new mapping contains 1,088 buffers: **105 more**, with a maximum of **two
levels per transport tree**. That does not mean every complete logic path has
only two buffers. Mapped cell/SRAM area increases **762.0480 µm² / 0.2376%** to
**321,504.0840 µm²**. Slow cell-only setup improves **+7.99 → +9.34 ns**. The
one new mapped circuit is checked against the corresponding original mapping
at both typical and slow corners; it is not two independently optimized maps.

Both mapped SAT checks, an inverted-buffer rejection control and the independent
331,401-edge / 1,517-frame package-pin replay pass. Five new balancing tests
cover connectivity, aliases, malformed trees, clocks and coordinate guidance;
the twelve existing distribution tests also pass. No Lean source or default
backend changes. Earlier local Lean and complete RTL evidence are reused with
their source hashes, not presented as new proofs.

## Physical comparison

The candidate starts from its own mapped circuit and fresh placement/CTS. The
20 ns clock, pin and I/O constraints, one SRAM, 1,572 flip-flops, 290-word image,
6×4 outline, macro position and reserved corridor stay fixed. Wire capacitance
uses the preceding extraction-derived calibration. No cycles or timing
exceptions are added.

After CTS, the same independently checked clock-width control used in the prior
experiment clears ten NDR bindings. Before/after exports require identical
cells, connections, placement, package and power geometry. This preserves the
new candidate's clock tree during preparation; it does not hold the old and new
candidates' clock trees identical across fresh CTS runs.

| Measure | Previous initial route | Balanced initial route | Balanced after repair |
| --- | ---: | ---: | ---: |
| Coarse overflow | 8,911 | **0** | **0** |
| Slow setup, ns | −9.286980 | −0.982379 | **+0.820730** |
| Slow hold, ns | −0.293061 | +0.215503 | +0.326675 |
| Slow cap / slew / fanout violations | 217 / 1,103 / 0 | 23 / 90 / 0 | **4 / 23 / 0** |
| Fast-screen hold, ns | −0.409959 | −0.020228 | +0.040186 |
| Cell/SRAM area, µm² | 376,176.6432 | 372,366.4032 | 374,556.3840 |

The first two columns compare completed initial-routing checkpoints. Balanced
trees and spatial leaf grouping change together, followed by fresh placement,
clock synthesis and routing. This supports the combined mapping policy; it does
not isolate depth from leaf grouping. The prior post-route repair was stopped.
The last column measures the new candidate's **completed** electrical and timing
repair separately.

Repair adds 92 buffers and eleven hold-delay cells, resizes one combinational
gate and moves 145 original cells by at most **7.68 µm horizontally / 11.34 µm
vertically**. Independent all-corner cell-function checks, actual-netlist buffer
contraction and row/site/overlap checks pass. Package/macro/power geometry,
clock topology and the reserved SRAM corridor remain intact. Both saved grids
independently reconcile to zero overflow; this is not an empty routing grid or
an inherited metric. Routing demand is 133,823 initially and 134,634 after
repair, versus 276,928 for the preceding initial layout.

Fresh timing for the completed repaired database uses propagated clocks and
coarse-route parasitics, with an empty metrics state for each corner:

| Corner | Setup, ns | Hold, ns | Cap / slew / fanout violations |
| --- | ---: | ---: | ---: |
| Typical | +6.381760 | +0.135776 | 4 / 1 / 0 |
| Slow | +0.820730 | +0.326675 | 4 / 23 / 0 |
| Fast screen | +9.638520 | +0.040186 | 4 / 0 / 0 |

Every consumed net has wire estimates. The 128 unannotated drivers per corner
are reconciled unused terminals; no drivers are partially annotated. The fast
standard cells are characterized at −40 °C and SRAM at −55 °C: this remains an
unqualified screen, despite its positive slack. No detailed routing, final
extraction, DRC/LVS or antenna-closure result is claimed for this circuit.

Both actual physical exports pass SAT over all package outputs and all original
FF/SRAM input pins, including clocks and resets: 1,636 exposed state outputs
and 5,000 observed state inputs. Each independently passes 331,401 package-pin
edges and rejects hidden-state and inverted-control mutations. SRAM response
still cannot reach rejection. The repaired worst slow path is now serial-shift
bit 53 to the rejection output; its slack is positive. Closed paired
memory/controller/package refinement remains a separate open obligation.

## Remaining discriminator and costs

The remaining electrical failures cover **seven actual signal nets**:

- `paired_balanced_31_2_out`, `_05584_`, `_05122_` and
  `controller.r_cursor[3]` exceed capacitance limits.
- `_02466_`, `_04528_` and `net1918` add slew failures; `net1918` feeds SRAM
  write bit 54 through `hold1918` and therefore needs an explicit hold check.

The next bounded repair should address these complete nets while preserving
clock topology and SRAM write timing, then repeat the whole-chip screen. The
pinned resizer already loads the requested timing corners. A default-corner
label change is not an established solution. Zero overflow and positive
screening timing do not waive the remaining electrical or characterization
requirements.

The final cell/SRAM area exceeds the historical **359,372.4382368 µm²** comparison
allowance by **15,183.9457632 µm² / 4.2251%**. That allowance is not a competition
die limit. The outline remains **1,289.28 × 710.64 µm**. Final area is 1,620.2592
µm² below the prior *unrepaired* layout; the stage-matched initial-area reduction
is 3,810.2400 µm². Keep those two comparisons distinct.

This phase charges **276.538 CAD seconds**, including a refused intake option,
checks and read-only tool inspection. Cumulative campaign charge is
**4,357.451 seconds** against 28,800 seconds. One A full-flow attempt remains;
none is used here. A, B and the complete design-iteration outcome remain open.

## Evidence and replay

The initial intake refused `CTS_APPLY_NDR` because the shared runner does not
allow that override. Its failed receipt is preserved. The corrected intake uses
the standard runner, then performs the checked rule-only change on a fresh
post-CTS copy. The shared runner and prior receipts are unchanged.

The mapping check is reproducible with retained, hash-matching source and
guidance artifacts and a fresh output tag:

```sh
python3 scripts/check-paired-distribution.py \
  --tag paired-buffer-balance-replay \
  --selection physical/experiments/paired-validation-mapping.json \
  --physical-receipt build/validation/paired-validation-isolation-01/routed-screen-receipt.json \
  --guidance-context build/validation/paired-validation-isolation-01/routed-screen-timing/context.json
```

The [frozen mapping selection](../../physical/experiments/paired-buffer-balance-mapping.json)
and [physical target](../../physical/targets/paired-buffer-balance.json) identify
the measured implementation. Retained recipes under
`build/validation/paired-buffer-balance-01/` cover intake, placement, clock-width
preparation, routing, repair, independent timing, physical SAT/pins and geometry
reconciliation. The result manifest hashes those recipes and their outputs.
They require fresh output identities to replay; replacing a receipt is refused.
Ignored guidance and physical artifacts must be retained or regenerated before
replay. This is a recorded local experiment, not yet the plan's fresh-checkout
A/B demonstration.
