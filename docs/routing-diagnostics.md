# Cheap routing diagnostics

The September 21 diagnostic cycle separates **checking a saved layout** from
**searching for a better layout**. Reuse the former before funding the latter.
[Research status](research/status.md) owns the next allocation; the
[physical study](chip-physical-study.md) owns the experiment history.

## What changed our understanding

The three-hour `hybrid-chip-14` retry completed all four detailed-routing passes
and RC extraction, then timed out before completing extracted timing. Its final
antenna check still found three violating nets and four pins. A completed
routing step does not mean a clean layout.

Retained optimization reports accumulate old and duplicate markers. A fresh
static check in a new OpenROAD process gives a different measurement:

| Routing pass, iteration 64 | Retained markers | Unique retained | Fresh static DRC |
| --- | ---: | ---: | ---: |
| 0 | 73 | 73 | 75 |
| 1 | 174 | 156 | 103 |
| 2 | 283 | 214 | 112 |
| 3 | 384 | 264 | 103 |

Every preceding report's markers recur in the next retained report. The fresh
checks instead show 68/101/110/101 Metal4 markers, five Metal3 markers only in
pass 0, and two persistent Metal2 markers absent from the retained reports.
The completed detailed-routing ODB independently gives **103 fresh markers**,
with a report byte-identical to the last snapshot's fresh check. Keep the old
counts as historical search output; do not interpret 384 as 384 current errors.

In the last snapshot, all 101 Metal4 markers lie inside SRAM footprints. Exact
integer geometry supports signal-centerline penetration into fixed supply
rectangles at 54 marker locations. For example, `controller.mem_q0[17]` crosses
a `storage0` supply rail. These are positive geometric witnesses, not a complete
wire-width, via, spacing or antenna checker. The two Metal2 markers are outside
the SRAMs. Repair adds 82, nine and two antenna cells across the three reroutes;
no pre-existing instance moves or changes. Placement movement is therefore not
supported as the explanation for this sequence.

The earlier `hybrid-chip-13` timeout endpoint is also corrected: its outer log
and matching report reach pass 1, iteration **38 with 198 markers**. The step
log stops at iteration 35 with 230. Both receipts remain available; the shorter
log must not silently become the endpoint.

## Checks in increasing cost order

| Check | Measured time here | Decision it supports |
| --- | ---: | --- |
| Reconcile reports, compare cells/nets, classify exact geometry and replay screen cases | 6.7 s | Reject mismatched evidence and identify recurring physical conflicts |
| Read two saved Metal4 capacity/usage maps | 0.5 s | Check whether the intended resource change actually happened |
| Standalone pin access | 3.5–3.6 s each | Reject a candidate with pins lacking any access point |
| Fresh static router DRC | 9.1–9.5 s each | Measure violations on a frozen layout without routing or repair |
| One global-routing screen | 44.4 s of OpenROAD process time | Check changed guides, congestion and resource allocation |
| Detailed routing, antenna repair and extraction | Previously capped at 3 hours | Assess convergence and produce artifacts for final physical checks |

These are measurements on the pinned local image, not runtime guarantees. Static
probes are capped at 180 seconds in this cycle, with a CLI ceiling of 300 seconds,
four CPUs and 6 GiB. The single new global screen had a 900-second cap. No new
detailed route or second global screen was allocated.

`routing_evidence.py` owns the shared report parser, pass reconciliation and
geometric predicates. `physical_floorplan.py` owns exact database-unit conversion
and rectangle overlap. `routing_context.py` exports actual geometry, checks
macro transforms against placed pins, and retains database/report identities.
`check-routing.py` combines those observations. The existing diagnosis and
physical reporters use the same pass parser, including the longer consistent
outer log. Conflicting logs, cross-pass snapshots, changed inputs and incomplete
reports fail the check.

Recompute the retained diagnostic cases from the repository root:

```sh
python3 -B scripts/check-routing.py \
  --manifest physical/experiments/routing-diagnostic-cases.json \
  --output build/validation/routing-review-NEW
```

Outputs must be fresh. The manifest identifies the exact saved snapshots and
exports; it does not download missing physical artifacts or launch a router.
Its historical decisions are regression examples, not an independently validated
predictor of routing closure. The wider gap and full corridor fail; the half
corridor qualifies only for a bounded trial. Its later remaining DRC errors
demonstrate the limit of that coarse screen.

Check a frozen completed layout using the pinned image:

```sh
python3 -B scripts/probe-routing.py \
  --design build/physical/hybrid-chip-corridor-half \
  --database build/physical/hybrid-chip-corridor-half/runs/hybrid-chip-14/05-openroad-detailedrouting/tt_um_pinwheel.odb \
  --config build/physical/hybrid-chip-corridor-half/runs/hybrid-chip-14/05-openroad-detailedrouting/config.json \
  --kind drc --output build/validation/static-drc-NEW --timeout-seconds 180
```

Use `--kind pin-access` for the access probe, selecting the candidate ODB and
its resolved configuration. The runner checks the installed image, mounts the
design read-only, disables networking, records source/configuration hashes,
owns the timeout, and independently verifies container termination. A successful
probe execution is distinct from passing DRC: inspect `marker_count` or the
`pin_access.decision` field.

Use the **resolved step configuration**, not the incomplete `core.json` defaults.
This flow resolves both signal and clock routing to Metal2–Metal4. Initial
Metal1–Metal4 probes are retained but superseded by the `resolved-*` receipts;
repeating them under the correct limits confirmed all counts. Both final access
probes report zero `stdCellPinNoAp` and zero `macroNoAp`. Their 157 initial
off-grid warnings are distinct from the completed access result. One access
point per pin does not establish simultaneous routability.

Timing provenance matters too. Global states inherit timing measurements. The
new resumed screen inherited the earlier resizer's −0.472 ns hold estimate;
the baseline inherited the later post-CTS STA's +0.249 ns. These are different
measurement stages, so that apparent difference is not a routing regression.
The screen records the source state and refuses promotion across mismatched
timing stages. Neither estimate is extracted timing.

## The one new screen and its disposition

`hybrid-chip-15` starts from the verified post-CTS checkpoint with two Metal4
signal obstructions covering the SRAM bodies; fixed power nets are exempt.
The half corridor, placements, topology, macro views, pins and clock stay fixed.
The intended change was to keep new global guides out of those bodies.

The obstruction objects survive into the completed ODB, and access checks pass.
However, its global guides are **byte-identical** to `hybrid-chip-12`. The entire
179×98 Metal4 GCell grid has identical capacity and usage. Interior samples still
report capacity 15 and usage 15. Metal4 body-overlapping guides remain 45; total
overflow stays 870 (Metal2/3/4: 676/124/70), and wire length stays 1,836,756 µm.

**Reject this mechanism before detailed routing.** Object existence did not
establish an effective resource restriction. This result does not determine the
vendor-code cause or disprove a corridor/resource-allocation remedy.

The next concrete candidate is an explicit global-region capacity reduction on
Metal4, applied before global routing. The pinned Tcl API was inspected locally;
the [OpenROAD documentation](https://openroad.readthedocs.io/en/latest/main/src/grt/README.html#set-global-routing-region-adjustment)
defines the adjustment as a fractional capacity reduction. A proposed full
reduction over the two existing footprints is:

```tcl
set_global_routing_region_adjustment {252 30 1036.48 94.36} -layer Metal4 -adjustment 1.0
set_global_routing_region_adjustment {252 144 1036.48 208.36} -layer Metal4 -adjustment 1.0
```

This proposal has not been routed or integrated into the flow. Its first gate
must verify reduced saved capacities in the intended GCells; then require fewer
body-overlapping guides without displacing the problem into worse total
congestion, wire length or repair cost. Preserve the macro signal access and
half corridor, compare timing from the same stage, and stop on a failed gate.
Only an effective, improved coarse screen could justify another detailed route.

## Where Lean helps

Keep protocol timing, upload atomicity, admission and SRAM execution contracts
in Lean. Recheck the affected proofs when their inputs change; a physical-only
diagnosis does not require repeating the entire foundation gate.

The new geometry checks use small integer predicates that could later have a
Lean checker and soundness theorem. That would establish those predicates for
the supplied geometry. The OpenDB exporter, library interpretation and complete
rule coverage would still be separate obligations. This cycle implements and
tests those predicates in Python; it adds no new Lean theorem. Static DRC,
antenna checks and extracted timing retain their own physical evidence roles.

The canonical local receipt directory is
`build/validation/routing-diagnostics-01/`. Start with `completion.json`,
`gate-final-02/report.md`, `candidate-comparison.json`,
`resolved-final-drc/report.json` and `hybrid-chip-13-endpoint.json`.
The tracked [physical manifest](../physical/experiments/hybrid-chip-physical-results.json)
indexes this cycle without rewriting prior experiment objects.
