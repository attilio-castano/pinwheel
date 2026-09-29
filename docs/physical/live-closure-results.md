# Live protection and electrical repair

**The small routed fixture passes a complete, independently checked repair
iteration.** It starts with protection-induced fanout and a separate extracted
wire-capacitance failure, preserves a declared protection grouping, repairs,
reroutes, re-extracts, and finishes with zero electrical violations in three
corners. This qualifies a local integration mechanism. The chip's third layout
still has one capacitance and four fanout failures.

The [protocol](live-closure-experiment.md) and
[manifest](../../physical/experiments/live-closure-results.json) retain all
attempts, failed controls and the successful fixture. [Research status](../research/status.md)
owns the next decision. The preceding [restart assessment](protection-closure-results.md)
explains why a saved database and SPEF alone were insufficient.

## What changed and what passed

The fixture uses the pinned OpenROAD revision and actual IHP standard cells,
LEFs, three Liberty corners and nominal extraction rules. Its 18 starting cells
include two flip-flops, eight functional receivers on one buffered branch, four
real antenna cells, and a separate 4.6 mm signal wire. Each diode has an explicit
receiver association for this test. This deliberately sparse, long fixture is
not a model of Pinwheel's density, SRAM or die dimensions.

| Measurement | Before | After fresh routing and extraction |
| --- | ---: | ---: |
| Fanout on the overloaded branch | 12 against 8 | Parent 7, child 6; whole fixture passes |
| Worst reported capacitance, fast corner | 0.366837472 pF against 0.300000012 pF | 0.092448458 pF against the same limit |
| Capacitance / slew / fanout violations | 1 / 0 / 1 per corner | 0 / 0 / 0 per corner |
| Original cells | 18 | All 18 retained at identical positions and orientations |
| Added cells | — | One `buf_4` and four `buf_1`, 43.5456 µm² |
| Protection pairs | Four declared pairs | All four retained on shared branches |

The added `buf_4` moves receivers 2, 3, 6 and 7 together with diodes 2 and 3 onto
one declared branch. Native `repair_design` then adds four repeaters along the
long wire using a 1,000 µm wire-length target and a 40% capacitance search margin.
These are fixture search parameters, not relaxed final electrical limits or an
admitted chip-wide rule. Newly inserted cells receive the existing power-net
bindings before routing.

| Corner | Worst setup slack, ns | Worst hold slack, ns |
| --- | ---: | ---: |
| Fast | +16.389086 | +0.044568 |
| Typical | +15.478432 | +0.127189 |
| Slow | +14.107367 | +0.093725 |

Independent Yosys readback and contraction of known positive buffers establish
unchanged circuit connectivity, including flip-flop clocks and reset. All 12
timed endpoints have both minimum and maximum paths in every corner. Every
signal net has routed wires and fresh SPEF coverage; the old SPEF is rejected
for the new nets. Native detailed-routing DRC and antenna checks report zero
violations, placement passes, and the exported congestion grid has zero overflow.
Power-terminal bindings pass; this small fixture has no chip PDN/signoff result.

Clock routes match the unchanged detailed-route control exactly, including the
native wire encoding, and also match after extraction. This uses matching stages:
DRT emits pin patches and RCX canonicalizes wire encoding. Comparing one stage
against another initially produced a false identity failure, retained in the
first checker receipt.

## The controls changed the repair policy

Native completion was not sufficient. The retained attempts establish three
separate requirements:

1. **Initialize and inspect actual routing state.** Native incremental routing
   starts successfully in the live fixture. The guard checks exact net/pin
   membership before edits. The first conversion updates congestion accounting
   from coarse routes to detailed-wire obstacles; repeating the no-edit
   conversion produces identical cells, wires and complete exported grid state.
   Original wire identity survives that conversion. This is a native conversion
   control, not a claim that the original coarse usage array is unchanged.
2. **Treat protection groups as part of the edit contract.** With instance
   connectivity locks on every diode, native fanout repair aborts with
   `RSZ-3006` when it tries to reconnect a protected load. Releasing those locks
   lets repair finish, but separates two declared diode/receiver pairs. Its
   Boolean circuit remains equivalent and its antenna check still passes: the
   rejection is specifically of the declared ownership contract, not evidence
   of an observed antenna violation. Explicit grouping preserves that contract.
3. **Accept only fresh measured closure.** Capacitance-only native repair detects
   the long-wire failure but leaves it unchanged, even with the tighter 40%
   search margin. The explicit wire-length target produces four actual repeaters
   and clears the freshly extracted failure. Source inspection confirms that the
   resizer's detailed-route mode constructs its repair tree using global-router
   paths and layer RC; extracted acceptance remains an independent gate.

The final checker rejects the actual ownership-breaking native candidate and
the actual candidate with remaining capacitance failure. It also rejects a
changed flip-flop clock, missing parasitic coverage and reuse of the source SPEF.
An earlier checker caught unconnected power terminals on the new buffers; the
final recipe reapplies global connections and independently verifies every
instance's power pins. All failed artifacts remain intact.

## Chip handoff

`build/validation/live-closure-01/chip-intake.json` binds the exact pre-fill
third-layout database, its extracted SPEF, configuration, five failing nets,
all 97 antenna cells and 340 clock nets. It also binds the independently checked
fixture recipe and the coarse database proposed for any later full-flow start.
No chip candidate or new whole-chip route was emitted in this experiment.

The next control should apply the integration contract to that exact chip state:

- Verify actual runtime pin membership **and repair-tree path coverage** before
  editing. The fixture kept routing state live; it does not qualify an arbitrary
  post-route restart or automatically transfer the earlier coarse import adapter.
- Establish explicit protection groups. The chip's `ANTENNA_<number>` names and
  current netlist do not establish unique historical diode/receiver ownership.
  Record native associations at insertion, or deliberately define and validate a
  new grouping contract. Geometric proximity alone is not provenance.
- Build and check a concrete, bounded positive-buffer candidate, including power
  connections, clock/geometry retention, whole-network electrical checks, fresh
  extraction and repeated antenna checks. Reject incomplete state or failure to
  converge. Newly arising violations remain in scope.

Only after this chip integration is qualified should another A attempt be
allocated: one full flow, at most 5,400 seconds and two electrical-repair passes,
with every existing final gate retained. The two B slots remain reserved. Fast
standard-cell/SRAM compatibility, complete paired Lean refinement and A/B replay
are unaffected by the fixture result.

## Receipts and reproduction

Evidence lives under `build/validation/live-closure-01/`. `fixture-06/` is the
qualified recipe; `checks-03/receipt.json` is its independent acceptance.
`fixture-01` through `fixture-05`, `readback-01`, and the earlier check receipts
retain unsuccessful policies, interface fixes and rejected checks. `launch.py`
verifies the pinned image layers/configuration, binds inputs, runs offline with
four CPUs and 6 GiB, caps each invocation at 600 seconds, and verifies cleanup.
Recipes use `/case` container paths and must be copied into a fresh case directory
for replay; the launcher and checker refuse to overwrite evidence.

The complete continuation charges **26.259 CAD seconds**, including failed work
and five independent Yosys reads. Cumulative campaign charge is
**5,689.629 seconds / 94.83 minutes** of 28,800 seconds. All scoped containers
are absent. Three A full-flow attempts remain used; no fourth attempt has been
allocated or run. No full-rule Magic DRC, LVS, silicon or new Lean theorem is
claimed for this fixture.
