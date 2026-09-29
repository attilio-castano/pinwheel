# Saved-route import and incremental-routing control

Study dated **2026-09-26**. **Reject both unchanged import controls and retain
the saved hold-repair checkpoint.** The second control reproduces every route
and every measured timing/electrical value, but changes the router's resource
accounting. No signal-distribution candidate was attempted.

[Research status](../research/status.md) owns the current decision;
[results](../research/results.md) records dispositions and reopening conditions;
the [manifest](../../physical/experiments/incremental-routing-import-results.json)
binds this experiment to the preceding
[routing-policy study](routing-policy-experiment.md).

## Question and result

Can a saved design be reopened for a local signal edit while preserving the
successful clock routes? The required first step is a no-edit control. A saved
route describes where wires go; the router also needs to know how much space
those wires occupy and which resources are already reserved. Timing can remain
identical while those internal counts are wrong.

| Evidence | Retained source | Import, then initialize | Initialize, then import |
| --- | ---: | ---: | ---: |
| Native routes | 11,342 nets / 126,729 segments | All unchanged | All unchanged |
| Clock routes | 342 | All unchanged | All unchanged |
| Routed demand, Metal2 / Metal3 / Metal4 | 66,971 / 98,058 / 24,590 | 0 / 0 / 0 | 66,930 / 98,016 / 24,590 |
| Router / saved-grid overflow | 25 / 25 | 0 / 0, invalid | 25 / 25 |
| Native marker reconciliation | Passed previously | Rejected: 25 stale markers | Passed, 25 markers |
| Changed saved capacity entries | — | 0 | 79 on Metal2 |
| Changed saved usage entries | — | 30,621 | 171 |
| Slow setup / fast hold | +0.382789 / +0.143801 ns | Not recollected after resource loss | Identical |
| Eligible for a signal edit | Reference | No | No |

The second control adds **348** units to the router's reported Metal2 resource
budget and loses **83** units of routed demand: 41 on Metal2 and 42 on Metal3.
Its saved Metal2 capacity array changes by a net **+191**, and saved usage by
**−198**; Metal3 usage changes by **−42**. Saved arrays include capacity
reductions, so their totals are not the same quantity as available resources
and routed demand. Matching overflow totals does not establish a faithful import.

## Circuit and measurement identity

Independent Verilog readback retains all **11,406** original cells and their
signal and power bindings. Both controls retain every original instance,
placement, fixed physical shape and placement status. Their native segment
exports are identical before initialization, after initialization and after
ending the no-edit incremental session. The control readbacks are also identical.

Fresh STA on the second saved control covers all **10,990** consumed cell-driven
signal nets at three corners: **9,200** timed nets and **1,790** constant ties
without reported timing limits. All connection measurements and selected/write
path records equal the retained source's parsed records. This includes:

- **32,970** physical-load reconciliations, **132** selected-path checks and
  **384** SRAM write-interface checks.
- Zero reported capacitance, slew, fanout or hold violations at every corner.
- **9,195** timed nets retain 20% reserve; the same five miss it, without
  violating the reported limits.
- All 64 SRAM write hold floors pass; the minimum is **+0.145047083 ns**.
- Setup/hold retain the original **+0.3673431 / +0.07927839 ns** floors.

No cells or area were added. Total area remains **361,583.4240 µm²**, including
**2,210.9857632 µm²** above the historical experimental allowance. The user's
exploratory-overage policy remains in force; this import failure is unrelated
to that budget.

## Mechanism and remaining uncertainty

The pinned OpenROAD commit is
`dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`.
In its [global router source](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/grt/src/GlobalRouter.cpp),
`startIncremental` can clear the routing core after guide loading has populated
its usage. Reversing the order calls net initialization twice; each call adds
macro pin-access resources. The observed capacity changes lie at the SRAM's
south edge. This source-based diagnosis has not yet been tested with a patched
native counterfactual.

Imported guide usage reaches
[`incrementEdge3DUsage`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/grt/src/fastroute/src/FastRoute.cpp),
which increments by one. It does not restore effective non-default routing-rule
costs. The missing 83 demand units match the grid-edge lengths of the six clock
nets whose extra routing cost survived the source run. That run disabled the
rule internally on `clk`, `clknet_0_clk_regs` and `delaynet_3_clk`; their persistent
ODB rule bindings alone do not reveal those runtime decisions.

Import also does not reconstruct the routing core's per-net route trees. Before
editing, qualify removal of an old route's demand and consistency between 2-D
and 3-D accounting. A correct no-edit total would not by itself prove that a
subsequent edit releases and reserves resources correctly.

## Verification and receipts

The new [`physical_route_import.py`](../../scripts/physical_route_import.py)
compares complete native segment sets, all clock routes and every capacity/usage
entry. Its verdict requires physical identity and matching measurements as well.
It is an evidence checker, **not a fix to OpenROAD**.

**65 focused tests** pass, including **12 new import regressions** covering
false zero demand, unchanged overflow with capacity drift, spatial drift with
unchanged totals, clock changes, incomplete evidence and invalid values. Six
launch guards pass, including rejection of a candidate after the failed control
and rejection of changed admission inputs. The initial analysis stopped on the
first control's stale markers; its failed version is retained, and the second
version records that expected rejection without weakening the check.

Five CAD stages take **168.145 seconds**: capability inspection, two no-edit
incremental controls, geometry collection and one three-corner measurement.
There are **zero full routes, zero candidate edits and zero timeouts**. All five
containers are absent. The experiment was bounded to 1,800 CAD seconds, three
no-edit controls and one candidate conditional on passing the control. Cumulative
CAD time including preceding experiments is **4,824.299 seconds**.

The sealed report is `build/validation/incremental-repair-01/report.json`,
SHA-256 **`2fc57afea2642eb214a06dc75265bea2c4e33ee4bc7648e27555205fcf3215f6`**. It binds **1,057 artifacts** and
**1,071 source bindings**, including the pinned source inspection. The failed stale-marker analysis and source-discovery 404 receipts are
retained separately from CAD execution.

An independent closeout audit, `build/validation/incremental-import-audit-01.json`,
verified **3,487 hash references across 1,068 files**, including eight historical
reports. The updated documentation has no missing local file-link targets.

The completed command sequence was:

```sh
python3 -B build/validation/incremental-repair-01/run.py inspect inspect
python3 -B build/validation/incremental-repair-01/run.py control incremental
python3 -B build/validation/incremental-repair-01/run.py control-02 incremental
python3 -B build/validation/incremental-repair-01/verify-02.py control-02
python3 -B build/validation/incremental-repair-01/prepare-measurement.py control-02
python3 -B build/validation/incremental-repair-01/run.py geometry geometry
python3 -B build/validation/incremental-repair-01/run.py control-02-timing measure
python3 -B build/validation/incremental-repair-01/analyze.py control-02-timing
python3 -B build/validation/incremental-repair-01/whole-chip.py control-02-timing
python3 -B build/validation/incremental-repair-01/regional-analysis.py control-02-timing
python3 -B build/validation/incremental-repair-01/compare-02.py
python3 -B build/validation/incremental-repair-01/test-02.py final
python3 -B build/validation/incremental-repair-01/check-launch-guards.py
python3 -B build/validation/incremental-repair-01/seal.py
```

These are historical commands against a sealed directory. Replay needs a new
output directory with revalidated hashes and the pinned local Docker image;
existing stages refuse replacement. The tracked manifest cannot recreate missing
ignored artifacts. Portable checker regressions can be rerun directly:

```sh
python3 -B -m unittest discover -s test -p 'test_physical_route_import.py' -v
```

## Next gate

Repair the narrow saved-route import boundary and regression-test it against
this checkpoint. Preserve macro pin-access allocation exactly once, effective
clock-rule costs and per-net route removal. Require both an exact no-edit control
and an edit/revert accounting control before testing the planned local signal
repair. Retain the prior checkpoint and its five weak nets throughout.

This result changes no Lean specification, RTL, execution schedule, SRAM
capacity or toolchain default. It grants no detailed-route, extraction or backend
admission. Existing complete-route measurements retain their original scope;
the false-clean incremental result is not a new physical improvement.
