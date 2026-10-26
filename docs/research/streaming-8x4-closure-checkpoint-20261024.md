# 8×4 closure campaign: first execution checkpoint

This is an intermediate checkpoint for the approved 24-hour campaign, not its
terminal report. The hard stop remains **25 October 2026 at 14:38:15 UTC**.
The authoritative local journal, immutable attempts and gate snapshots are in
`build/campaigns/8x4-20261024-01/`.

**No mandatory design acceptance gate has closed at this checkpoint.** There
is still no completed authoritative final routed target. Routing, qualified
extraction/timing, final implementation correspondence, full final public wires
and physical/official signoff remain open. Prepared source code, resource
closure and diagnostic observations are not substitutes for those gates.

## Routing: two strategies, one omitted legality rule

The canonical retained case reproduced 35 antenna-net violations, 36 pin
violations and all 39 required new diodes. Strategy A failed its finite local
site search at `ANTENNA_132`, before applying moves or starting detailed routing.
Its terminal record and all failed artifacts are preserved.

The second and last registered strategy B searches the finite legal core sites
in Manhattan-distance order, with a fixed tie order. Independent HOST planners
found positions for all 39 diodes. Actual OpenROAD applied the plan, then its
unchanged placement check rejected `ANTENNA_110` with `DPL-0010`/`DPL-0033`.
Detailed routing did not run. The failed B attempt has closed input/runtime and
cleanup records; that is execution custody, not placement or route acceptance.

Pinned source explains the omission: the native placement checker rasterizes
special-routing blockages into placement pixels and treats an M1 pin as using
M2 for access from above. ANTENNA_110's signal-access shapes cleared the PG
stripe, but its cell overlapped a blocked area at the stripe's end. The planner
must implement this applicable native legality rule as well as its existing
signal-access checks. A correctness repair to the same B strategy is authorized:
its search, ordering, variant ledger, PG, other instances and fatal native
placement check remain fixed. The failed B receipt will not be overwritten,
and no third physical strategy is allowed.

## Extraction: fixed numerical stop reached

The first fresh native pattern census completed 310 actual TYP patterns with
strict source/version/case inventory and an independent readback. It establishes
an intake, not a model. A subsequent fixed six-conductor full-stack near/far
smoke completed both native solves but failed the unchanged 1% complete-matrix
reciprocity criterion.

One predeclared eight-call residual × interaction study then completed every
call with closed resource, source and cleanup evidence:

| Setting | Near geometry | Far geometry | Both passed |
| --- | --- | --- | --- |
| Original residual and interaction | Fail | Fail | No |
| Tighter residual only | Fail | Fail | No |
| Tighter interaction only | Fail | Fail | No |
| Both tighter | Pass | Fail | No |

The last setting's far failure is one pair at **1.010310295496%**, above the
unchanged 1% limit. Its physical discrepancy is about `9.765625e-20 F`. Closeness
does not change the verdict. **Numerical tuning is stopped for this campaign**,
as declared before execution. No tolerance, mesh, interaction, successful-subset
or last-matrix promotion is permitted.

All eight model coverage obligations remain open: resistance, ground C,
coupling C, via resistance, dielectric interfaces, layer coverage, width/spacing
range and actual consumer units/semantics. A passing smoke would still leave
mesh/domain/length/ground-extension convergence, independent accuracy, untouched
heldouts, physical corner justification and final-route applicability to prove.
No qualified timing authority exists.

Separate source/consumer controls may still clarify two reproduced software
seams: diagonal coupling projection/import semantics and the difference between
centerline route length and the consumer's actual shape extent for resistance.
They cannot qualify the physical model or erase previous failed fixtures.
The owned ITF_MIN/TYP/MAX emitter binds exact merged ITF geometry and dielectric
partitions; its labels do not establish foundry-corner qualification.

## Remaining campaign work

First verify the corrected same-B legality plan and actual placement, then seek
completed ordinary detailed routing and its full antenna loop before the primary
routing cutoff. If a completed target exists, independent complete actual-M,
private controls, full public wires, GDS/antenna/LVS, power and official checks
may run even while model/timing gates remain open. Every result must bind that
same final target. The final report will replace this checkpoint as the terminal
gate-by-gate record and include exact cleanup and remaining dependencies.

## Fixed subsequent routing resource policy

The retained full run used about 6,007 seconds and reached 90.6% of its 6 GiB
container limit; the retained repair run reached 94.87%. Subsequent attempts
use a fixed two-worker/two-CPU policy with the same 6 GiB/no-extra-swap limit.
The only allowed resolved configuration changes are the declared PG flow
metadata and `OPENROAD_THREADS: 4 → 2`. This is a resource reduction, not another
placement strategy or a thread-count sweep. Its memory benefit is a hypothesis.
Actual worker banners, cgroup limits and resolved configuration must agree.

The new full Native leaf cap is 14,040 seconds with at least 60 seconds for its
outer controller, within the unchanged 14,400-second supervisor job ceiling.
The primary routing cutoff and all campaign deadlines still constrain admission.
Historical executed packets retain their original four-worker/source identities.
Eight focused controls pass normally and under optimized Python; independent
source review found no routing-rule, clock, footprint or acceptance relaxation.
