# Timing and communication organization

Study dated **2026-09-23**. The saved-chip screen finds no complete candidate
under the current exchange policy. It retains regional decoding as a structural
alternative: the extra gates are small, but they need a different allocation of
the existing area allowance or an explicitly separate comparison budget.
Physical qualification remains open; no circuit, timing constraint or backend
default changes in this study.

The [specification](../physical/experiments/paired-organization-study.json) binds
the [matched diagnosis](physical-targets.md#matched-clock-control-and-capacity-diagnosis),
semantic sources and original exchange policy. The
[result manifest](../physical/experiments/paired-organization-study-results.json)
binds the selected report and checks. [Research status](research/status.md)
owns the active next step.

## Requirements before physical choices

| Boundary | Current requirement and authority | Consequence |
| --- | --- | --- |
| Protocol execution | Paired controller state updates, pin levels, branch/capture and atomic replacement; `PairedController.next` and `body` | Preserve edge behavior. A new execution pipeline needs a schedule/refinement argument. |
| Rejection on status page zero | `PairedController.rejectedExpr` feeds `Chip.outputs`; `HostResult.observer` selects this current view on page zero | An additional status register changes the existing observation contract. The retained rejection bit on page three is a different view. |
| Host clear input | `ui_in[6]` enters `HostResult.controlFirst`, mapped to `_12281_/D` | This measured hold path belongs to host control. It is not a long execution computation that benefits from an extra pipeline stage. |
| Parameter feedback | `_11166_` is bit 8 of `r_parameter_b1_w20` | Preserve parameter state and hold protection. Launch and capture use the same physical clock pin. |
| Physical I/O assumptions | The measured `core.sdc` is byte-identical to `physical/chip.sdc`: 20 ns clock, 4.0/0.2 ns maximum/minimum I/O delays, 0.2 ns uncertainty | These are the current comparison assumptions. The behavioral model itself does not derive these nanosecond values. No timing exception is introduced. |
| Area | Original reference 358,297.5456 µm²; cumulative increment capped at 0.3% | This experiment leaves 0.767837 µm². It is distinct from the physical die outline. |

The organizer's [announcement](https://blog.janestreet.com/protocol-emulator-asic-competition/),
rechecked on this study date, still specifies the 6×4 allocation and asks for
programmable, precise protocol timing. It does not specify our 0.3% increment
or these I/O-delay values. Changing a comparison assumption requires an explicit
new comparison and cannot retroactively qualify the rejected chip.

The source definitions establish the intended observations; the paired backend's
complete compiler/admission/package refinement remains an independent open task.
This study adds no Lean theorem and makes no new behavioral-equivalence claim
about a physical implementation.

## A timing obligation has a direction and a clock identity

For a selected setup path, holding its other timing terms fixed:

```
new slack = saved slack + capture-clock shift - launch-clock shift - data-delay shift
```

The signs reverse for hold. Consequently, speeding a data path can hurt hold;
moving a capture clock later can help setup while hurting hold. A common shift
at the same launch/capture clock pin cancels in this model. Saved uncertainty,
cell timing and clock reconvergence corrections remain assumptions, not quantities
we can assume invariant after a physical edit.

`physical_organization_study.timing_budget` checks the matched data/clock pin
identities and the arrival/requirement/slack arithmetic before computing these
obligations. All four paths are retained at all three measured corners.

| Selected check | Current slack | Retained floor | Extra slack required | Deficit after replaying the earlier clock environment |
| --- | ---: | ---: | ---: | ---: |
| Slow mode → status | −0.055813 ns | +0.367343 ns | 0.423156 ns | **0.403916 ns** |
| Slow SRAM → status | +0.113294 ns | +0.367343 ns | 0.254049 ns | **0.048422 ns** |
| Fast input hold | +0.064551 ns | +0.079278 ns | 0.014728 ns | **0**; replay gives +0.104386 ns |

The replay retains the newer data delay and substitutes the earlier launch
clock and required time, including the saved required-time corrections. It is
a conditional calculation, not a physical experiment. It shows that restoring
the old clock environment alone would not recover either setup floor.

With data/corrections fixed, the selected setup paths would require their launch
clocks at least 0.423156 ns and 0.254049 ns earlier, respectively. Input hold
requires capture at least 0.014728 ns earlier. These are **one-sided bounds**:
the opposite checks and other paths sharing those clocks have not been collected
as matching witnesses. They cannot establish a feasible clock tree. The
parameter self-hold path instead has cancelling clock-shift coefficients.

## Whole communication families and shared capacity

The screen reconstructs and checks all **1,152** inherited/watchlist connections
against the saved physical endpoints. It reconstructs the five complete selected
trees and reconciles their input loads against pinned libraries in **354
net/corner checks**. Every selected branch receives a wire-capacitance budget,
saved load, electrical reserve and required reduction in the generated report.

| Family | Connections | Terminal consumers | Buffers / protected delays | Current weak connections | Congested edges crossed |
| --- | ---: | ---: | ---: | ---: | ---: |
| Shared mode/admission control | 6 | 43 | 5 / 0 | 1 failing | 4 |
| Serial data bit 50 | 13 | 51 | 10 / 2 | 1 failing | 5 |
| Serial data bit 49 | 8 | 36 | 5 / 2 | 1 failing | 3 |
| Serial data bit 51 | 88 | 434 | 85 / 2 | 1 failing | 15 |
| Parameter control | 3 | 21 | 2 / 0 | 1 below reserve | 3 |

Terminal consumers are pins, not independent registers or exclusive blocks.
The edge counts overlap: the families jointly cross **21 of 33** congested
edges. Ordinary clocks cross nine; no stored-rule-bound clock net crosses a
current congested edge. Every edge also has other signal traffic. These are
observed crossing sets, not a prediction of what rerouting a family would free.

Serial bit 51 is a concrete reason to consider an entire distribution tree:
one logical bit already needs 85 buffers to reach 434 terminal inputs. Counting
only the source register or the currently failing branch hides that cost.

## Three organizations compared

| Organization | Construction and evidence | Disposition |
| --- | --- | --- |
| Current saved chip | Exact baseline: same 20 ns constraints, original cells and transport trees | Retain the measurements. Existing whole-chip qualification remains rejected. |
| Regroup existing consumers | Existing `Planner.exchange`, eight-pass bound per family, same source/driver kind, fixed placement and equal per-corner pin-load limits | **12 swaps / 14 changed branches**; independent virtual buffer-contracted identity passes. No complete family clears the conditional wire screen. |
| Local combinational decoding | One additional copy of each of `_05733_` (XOR) and `_09533_` (NOR); split each root's immediate consumers into two spatial groups | Costs are explicit, with no added state. Outside the current remaining area allowance; retain for structural comparison. Placement and new wire behavior remain unknown. |

For regrouping, the weakest bit-51 branch's wire/budget ratio falls from
**1.725 to 1.186** under proportional pin-envelope scaling; shared control falls
**1.492 to 1.420**. Bit 49 has no permitted exchange. The parameter-control root
is a logic gate outside the buffer-exchange operation. Bit 50 sees exchanges
elsewhere in its tree but no improvement to its weak branch's envelope.
These results reject promotion by this screen; they do not prove that another
route or broader regional organization is infeasible. No routing improvement
is assigned to those geometric ratios.

The XOR copy costs **14.5152 µm²** and the NOR copy **7.2576 µm²**: together
**21.7728 µm²**, about **0.00608%** of the original reference area. The proposals
retain existing cells, so their individual positive costs both exceed the
remaining 0.767837 µm². Replacing or reusing existing buffers could change that
accounting, but no buffer removal is justified by this study.

Copies also add load to their inputs. The XOR's parents `_01590_` and `_01808_`
are outside the saved electrical inventory; their extra pin load is known from
the library, but their current delivery margins need measurement. The NOR's
parents `_04488_` and `_04717_` already have saved measurements. Those raw reports
are reused, and the additional pin load passes the capacitance reserve with
the old wire load held fixed. Extra wire, slew and path timing remain unknown.
The generated consumer lists and region centers are planning guidance, not
legal placement coordinates or an emitted edit plan.

## What is reusable, and the next decision

The existing `physical_organization` machinery still owns reconstruction,
consumer exchanges and independent virtual identity. The new study helper owns
conditional timing obligations and gate-copy costs. The reporter joins them to
bound evidence and exposes shared capacity. It neither duplicates STA nor
implements a placer. Its specification and report cannot admit a physical run.

This follows established ideas with explicit scope:

- [Hardcaml](https://blog.janestreet.com/advent-of-hardcaml-2024/) makes component
  allocation, sequencing and sharing deliberate. Physical representatives can
  vary while a logical owner remains unique.
- [CIRCT scheduling](https://circt.llvm.org/docs/Scheduling/) separates the
  problem, scheduling algorithm and solution verification; this study similarly
  separates obligations from candidate selection and physical qualification.
- [Hammer's hierarchical guidance](https://docs.hammer-eda.org/en/1.1.2/Hammer-Use/Hierarchical.html#tips-for-constraining-hierarchical-modules)
  budgets the timing and pin-access environment at component boundaries.
- [OpenROAD's exploration guidance](https://openroad.readthedocs.io/en/latest/contrib/DesignSpaceExploration.html)
  supports inexpensive intermediate screens, calibrated to retain promising
  candidates. Our span heuristic has not earned the right to eliminate an
  entire organization class.

The next decision should compare **regional distribution trees with an explicit
replacement/replication budget**, retaining the execution contract. First obtain
the two missing parent measurements and the opposite timing checks needed to
bound clock movement. Then account for the complete regional trees, including
retained hold delays, both sides of every new gate, clock delivery and shared
channels. Either show how existing transparent buffers fund the changes within
the old cap, or declare a separate bounded comparison with its own absolute
area limit and the old result alongside it. The old cap is not silently raised.

A physical candidate needs a complete edit plan, independent functional checks,
legal placement and a falsifiable joint timing/electrical/capacity prediction.
Only a qualifying candidate should advance to bounded placement and coarse
routing. No current organization passes that gate; detailed routing stays closed.

## Reproduce the saved-chip study

With the bound local artifacts and pinned libraries available:

```sh
python3 -B scripts/report-physical-organization.py \
  --study physical/experiments/paired-organization-study.json \
  --check-tag organization-comparison-next
python3 -B -m unittest discover -s test -p 'test_physical_organization*.py' -v
```

Use a fresh tag; earlier artifacts are preserved. Portable tests need no CAD
installation. Replaying the full study requires the original ignored `build/`
artifacts and its pinned library files; the result manifest is not a substitute
for them. All physical numbers remain estimates from saved global routes. The
historical fast-screen cell/SRAM temperature mismatch remains explicit.

The selected comparison completes in **4.112 seconds**, with no CAD commands.
**42 focused tests** pass, including eleven study-helper cases. Four integration
mutations reject a changed diagnosis hash, omitted path classification, added
pipeline cycle and attempted state replication. The combined virtual exchange
changes twenty scalar inputs while preserving the complete buffer-contracted
netlist. This is an in-memory check, not a changed physical chip.
