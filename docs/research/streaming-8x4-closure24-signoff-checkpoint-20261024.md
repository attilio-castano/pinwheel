# 8×4 closure checkpoint: physical and official packet passes

Snapshot: 24 October 2026, 20:58 UTC. This is an intermediate executed checkpoint, not the final campaign report. The approved hard stop remains 25 October, 14:38:15 UTC.

**Canonical parent gate 5 passes on the frozen target under the pinned deck model. Gates 1–4 remain open.** This is one of five parent gates closed, not a readiness percentage or a tapeout-ready claim.

| Parent gate | Executed result at this checkpoint |
| --- | --- |
| 1. Routing and antenna | Whole ordinary DetailedRouting completed with route DRC 0. OpenROAD antenna count remains 1, so the combined gate fails. Both allowed physical variants are consumed and the target is frozen. |
| 2. Applicable extraction model | All eight coverage rows remain open. Ideal-sheet R, source/grammar and synthetic-C semantics have scoped passes; physical C, via/contact/context/corner applicability and independent references remain incomplete. The fixed numerical conditioning stop remains binding. |
| 3. Qualified extracted timing | Blocked by model qualification. Retained unqualified timing reports do not establish a pass; fast/typical input hold is negative under that inherited model. |
| 4. Final correspondence and public wires | Complete finite public-wire corpus passes. Full positive proof, whole audit and original private controls remain open. Fresh proof preparation preserves every required module and contract. |
| 5. Physical and official verification | **PASS:** fresh full GDS DRC, full foundry antenna, top transistor LVS with complete used-cell references, required PG connectivity, consistent views and all nine applicable unchanged official checks. |

## Same-target signoff evidence

The actual ODB SHA256 is `f516ffbca3cd86e5cd214c515ca0be457a91a517dbe715caa47336aec907eee0`. The fresh GDS SHA256 is `5c1d5635b47023591a0e4f8d76b61b84a4d7ae9bdfa4183700bc955a4cd6261d`. Logical payload, official 8×4 geometry and pins, 6,039 semantic state bits, 64×64 bank, depth-two queues, full protocol capacities, and complete 20 ns timing/I/O constraints remain unchanged.

The [gate-5 aggregate](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/canonical-gate5-closeout-01.json), SHA `7a3bb16aacc815e474cf2fcbb8ea20650ef89e027b47b3d22d81bbb0d2ff12c4`, binds every authority to that target and the criterion in the approved campaign plan:

- Fresh main GDS DRC: 332 categories, zero violations. All nine official checks pass, with three fresh Native calls and six ordered events. [Official readback](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/final24-official-context-independent-readback-01.json), SHA `17008221b592709cb110d9ed62de0ef27446948d07ea3303517f77c7fde5eab7`.
- Foundry antenna: all 23 declared categories, zero violations. Real transistor LVS: 37 matched circuit pairs including top, complete references for 38 used master definitions, and exact CDL recomposition for 98,957 instances and 322,058 positional terminals. Two device-empty filler definitions simplify normally. The reported 244 device definitions are hierarchical, not the flat chip transistor count. [Layout readback](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/final24-layout-resource-independent-readback-01.json), SHA `4c4cb11db1148b8545af33a20284bb4b4ce8467574318584f65efead1743d746`.
- Required PG connectivity is supported jointly by geometric same-rail open paths for every 98,957 ITerm per rail, with zero skips, and real, strict-port GDS-versus-complete-CDL LVS power topology. PSM's short checker is a stub and was not executed; this does not claim a separate exhaustive geometric-short proof, package delivery, IR or EM qualification.
- Fresh consistent views and exact boundary/public-pin geometry pass. All final resource guards close with unchanged inputs and no owned residue. The official and standalone layout replays used one CPU, 6 GiB memory, zero extra swap and unchanged checks/readers/flags. Prior smaller-resource failures remain preserved.

The passing foundry antenna result does **not** erase OpenROAD antenna1 in gate 1. Its Metal3 victim has a cumulative ratio of 213.80 against 200; existing protection joins through Metal4. No further physical repair is authorized within this campaign.

## Digital progress and execution limits

The [complete public-wire readback](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/final24-wire-independent-readback-01.json) passes all four protocols: 35 positive cases, one actual sampler mutation control, 14 processes and 28 events. This is finite zero-delay Boolean validation, separate from universal correspondence and timing.

The original full proof stopped at the 4 GiB aggregate cap after 1,315 modules. One exact-module diagnostic subsequently compiled successfully in 31.502 seconds, with maximum sampled parent-plus-child RSS 3,655,072 KiB. This supports process isolation but supplies no accepted prefix.

The first fresh isolated run completed full independent rederivation in 117.038 seconds, then stopped after 25 closed modules because the observational process monitor rejected a nonabsolute executable token. The failed raw status line was not retained. A bounded owned-child control reproduces the same exception for macOS state `Z` / `<defunct>`; attribution of the historical row remains an inference. A new observer is being prepared to preserve raw state, distinguish dead from live process identity, and keep live identity checks strict. All failed sources, receipts and objects remain preserved and unaccepted.

Another complete fresh source-only owner has already been generated: all 3,966 required M modules, bound N dependencies, full state/output/clock/reset contracts and zero cached objects. The next complete proof and original private controls retain the four-hour/4-GiB limits and original per-module allowances.

The full routed target came from an authenticated post-diode 39 seed and completed the ordinary route and canonical tail. The fresh initial 94-diode path remains failed at strict incremental guide refresh; this checkpoint does not claim clean reproduction of that path.

The [gate ledger](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261024-01/gate-ledger-10.json), SHA `b55edc2dfb0129a631a1fd2d7e5eeb7201446549c441428ed5656946e4bbd761`, records these distinctions. No push, publication, external message or fabrication submission has occurred. The final campaign report must replace pending proof outcomes with their exact terminal evidence and reconcile cleanup.
