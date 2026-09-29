# Protection and electrical closure: policy costs and native restart

**Prefer qualifying repair after actual antenna insertion before adding reserve
buffers throughout the signal network.** The bounded assessment costs two useful
alternatives and identifies a missing integration contract: a saved layout and
its extracted parasitics support measurement, but do not restore all the native
router state required for editing. The attempted restart is rejected; no new
physical candidate or detailed layout was produced.

The [frozen protocol](protection-closure-experiment.md) and
[manifest](../../physical/experiments/protection-closure-results.json) retain
both probes, the exact source circuit, cost inventory and failure diagnosis.
The [third A layout](transport-split-results.md) remains the physical result:
one capacitance and four fanout failures, positive measured timing, passing
stated layout/circuit checks, and open fast-view and formal-refinement gates.
[Research status](../research/status.md) owns the active decision.

## Cost reserve across the signal network

The coarse source has 905 signal nets with eight input terminals and no final
antenna cells. The following explicit policy retains all original cells and
connections and adds noninverting buffers until each old and new driver has at
most `m` functional receivers, including other buffer inputs. Clocks are excluded
from this cost exercise and remain protected.

A root with capacity `m` and `k` added `m`-way buffers can reach at most
`m + k × (m − 1)` original receivers. For a source with `n > m` receivers,
at least `ceil((n − m) / (m − 1))` added buffers are therefore required. The
bound assumes unrestricted grouping and placement; actual wires, timing and
antenna protection can require more cells or stronger drivers.

| Maximum functional receivers | Reserve below eight | Affected nets | Minimum added buffers | Minimum added cell area, µm² | Increase over coarse signal/SRAM area |
| --- | ---: | ---: | ---: | ---: | ---: |
| 7 | 1 | 905 | 905 | 6,568.1280 | 1.7502% |
| 4 | 4 | 1,044 | 1,949 | 14,145.0624 | 3.7692% |
| 3 | 5 | 2,266 | 4,143 | 30,068.2368 | 8.0123% |
| 2 | 6 | 2,760 | 8,880 | 64,447.4880 | 17.1733% |

These area bounds use the smallest admitted positive buffer, `buf_1`, at
7.2576 µm². Using the preceding repair's `buf_4` doubles these cell-area costs.
The denominator is the exact 375,276.7008 µm² coarse signal/SRAM area. The
machine-readable inventory names every affected net and its count bound.

This is not a lower bound on every possible architecture or on remapping the
existing trees. It also does not establish a safe antenna reserve: the prior
detailed layouts added up to six or five protection inputs on individual nets,
and another route can produce different demand. The user permits recorded area
overruns; the reason to defer this blanket policy is that it pays for unobserved
demand while leaving the wire-capacitance obligation open.

## The flow has an ordering gap

The pinned `drt.tcl` performs detailed routing, checks antennas, inserts protection
and reroutes up to the configured antenna-iteration limit. It then writes the
views. The later flow extracts wires and checks electrical limits. There is no
electrical repair inside that post-antenna loop. This explains how a previously
legal branch can finish with excess load even when the antenna check passes.

The native library gives input pins a default fanout load of one and a maximum
fanout of eight. Its antenna cell has one input and retains `dont_touch` and
`dont_use`. The probes preserve these rules and explicitly protect all existing
97 antenna instances and all clock nets; no protection input or constraint is
removed to obtain a pass.

## What the restart probe establishes

The input is the third layout before physical fill, with the final nominal SPEF
and unchanged three-corner libraries and constraints. Independent readback matches
all **12,329 cells**, every signal connection, original placement, macro and
fixed geometry to the final layout, excluding only its **45,905** power-only
fill/decap cells. The source files are mounted read-only.

The first invocation stops before repair because `report_worst_slack` does not
accept the requested corner flag in this pinned version. Its 6.006-second
receipt is retained. The corrected invocation removes that reporting call and
reproduces all actual final electrical failures in all three corners:

| Corner | Capacitance on `paired_balanced_5_4_out`, pF | Fanout failures | Slew failures |
| --- | ---: | ---: | ---: |
| Fast screen | 0.303477138 | 4 | 0 |
| Typical | 0.302570105 | 4 | 0 |
| Slow | 0.301837444 | 4 | 0 |

The capacitance limit is 0.300000 pF. The four fanout nets retain counts
12, 9, 9 and 9 against eight, exactly matching the preceding extracted diagnosis.
This verifies the probe's measurement input, not its ability to edit it.

On entering `repair_design`, the corrected process receives signal 11. Its
stack is:

```text
GlobalRouter::getPinGridPositions
Resizer::makeBufferedNetGroute
RepairDesign::repairNet
```

The matching source explains the integration failure. The resizer's
`detailed_routing` estimator mode uses the global-router net/pin map when building
its repair tree. `read_current_odb` loads the database, libraries and constraints;
the probe then reads SPEF and selects that estimator mode, without initializing
the router map. The native lookup dereferences the missing net. Selecting a mode
does not reconstruct the state it requires.

The corrected probe takes **4.642 seconds**, emits no candidate database/netlist
and never reaches its end marker. The failure diagnoses this restart recipe.
Repair while native routing state remains live has not yet been tested. The
existing coarse-route import adapter has a separate, restricted qualification;
its correctness does not automatically extend to this post-detailed state.

## Proposed next integration experiment

Keep the current architecture and measured transport repairs. The next concrete
experiment should qualify the missing transition between antenna and electrical
repair:

1. Use a small routed fixture with a known protection-induced fanout excess and
   a separate capacitive load. Run repair while the router state is live. Check
   actual net/pin/resource coverage before editing, an unchanged control and a
   real buffer edit. Verify protected diode ownership, clock routes and circuit
   equivalence. Reject missing runtime state before entering native repair.
2. Make the transition explicit in the pinned physical flow. Preserve the router
   session through protection and electrical repair where possible. Any restart
   must reproduce its complete required state under an independent control.
   Reuse existing circuit/resource checks; no new Lean CAD implementation is
   needed for this integration test.
3. After edits, legalize and reroute, extract new parasitics, and repeat antenna,
   electrical and setup/hold checks across the complete network. Old SPEF cannot
   qualify changed connectivity. A bounded loop must stop on failure or
   nonconvergence and preserve every failed artifact.
4. Only after those controls and a concrete candidate are reviewable, propose
   **one additional A full-flow attempt**, capped at 5,400 seconds within the
   original 28,800-second aggregate. Limit it to two electrical-repair passes;
   require all existing final layout/circuit gates. The two B slots remain
   reserved. This result allocates no such attempt.

This is the smaller causal intervention to evaluate first. A global reserve
policy remains a costed alternative if the native integration or local wire
repair proves unsuitable. Neither option yet establishes physical feasibility.

## Evidence and resource accounting

The assessment charges **10.648 CAD seconds**, bringing the campaign to
**5,663.370 seconds / 94.39 minutes**. Both scoped containers are absent; source
and artifact hashes verify. Three A full-flow attempts remain consumed, two B
attempts reserved, and no additional detailed route has run.

Recipes and reports are under `build/validation/protection-closure-01/`.
The inherited preparatory request is retained; the executed `probe-request`
files explicitly bind the actual pre-fill database and SPEF. The first probe and
corrected worker/Tcl/launcher are separate frozen files. `analyze.py` verifies
source identity, failure reproduction, the crash/source relationship and reserve
costs; `publish-record.py` binds the result to the predecessor manifest.

| Artifact | SHA-256 |
| --- | --- |
| Pre-fill source database | `43eb960eb037aab867453f10437388d16d671fb2568aa9a67df56b1b551d53f4` |
| Unchanged extracted source SPEF | `52cb33331e4030e3bacbbb71b2fa2241725a9ea658212d8c6c2203e7e04f5888` |

No candidate equivalence/pin replay or new physical acceptance checks are counted
as passes: no candidate exists. The last completed layout's five electrical
failures, fast-view mismatch, complete paired controller/loading/package
refinement, A/B iteration and clean-source replay remain open.
