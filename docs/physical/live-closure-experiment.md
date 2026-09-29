# Live protection/electrical repair experiment

The September 27 continuation authorizes a local routed fixture and integration
controls for the gap identified by the [restart assessment](protection-closure-results.md).
The fixture uses the pinned OpenROAD image and IHP cell library. It is not an
additional whole-chip A attempt.

Keep the router alive through routing, measured electrical repair, legalization,
rerouting and fresh extraction. Exercise eight functional receivers plus four
real antenna inputs on one net, and a separate long-wire capacitance violation.
Library limits and protection cells remain intact. Preserve all attempted
recipes and failures. Do not qualify changed connectivity with an old SPEF.

Required controls are an unchanged circuit, an actual repair, independent
connectivity readback, original antenna membership/placement, clock connectivity
and route comparisons, route coverage/congestion, fresh three-corner electrical
and timing measurements, and a repeated antenna check. A changed protection
branch must retain its protected functional sink or fail admission. A successful
native command alone is insufficient.

Each invocation is capped at 600 seconds, four CPUs and 6 GiB; one CAD process
runs at a time, offline. Reserve at most 1,800 CAD seconds for this fixture
experiment within the existing 28,800-second campaign, starting from 5,663.370
charged seconds. Three A full-flow attempts remain used and two B slots remain
reserved. If the fixture qualifies, prepare a concrete chip integration and its
admission checks before deciding the additional A attempt. This protocol does
not allocate that full-flow attempt.

Evidence is retained under `build/validation/live-closure-01/`. Each invocation
binds its scripts, inputs and tool lock, records elapsed cost, verifies container
cleanup, and preserves the source files. The experiment result must distinguish
tool integration from whole-chip physical closure, fast-view qualification and
Lean refinement.
