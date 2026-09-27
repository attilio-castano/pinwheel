# Saved-route import experiment

This adapter targets OpenROAD commit
`dcf36133a369abc8f3c5e5738cd4d82e4903c0e0` in the recorded Pinwheel image.
It is an isolated research tool, not a stable plugin ABI or a replacement for
the default router. The runtime rejects other OpenROAD revisions.

The checkpoint's guides retain wire geometry, but omit the router's per-net
resource-release records and runtime NDR relaxations. The adapter initializes
capacities once, restores the explicitly recorded relaxed rules, and replays
saved wires with the native effective per-net costs. It reconstructs removable
edge ledgers in FastRoute. These are not complete Steiner topologies: unchanged
nets must remain frozen, and each edited net must be released and rebuilt by
the native solver before routing. Only an explicitly declared set of ordinary
signal nets can be rerouted. Macro geometry and clock routes must stay fixed.

`build.py` uses exact pinned headers from the retained experiment and adds a
friend declaration to two generated header copies. No member, layout, native
binary, or original header changes. Calls execute against the resident router
objects. This depends on private implementation details and the exact pinned
compiler/image; it is unsuitable as a general OpenROAD extension interface.
The upstream BSD license is retained for the adapted native routing sequence.

Commands after loading `libpinwheel_route_import.so Pinwheelrouteimport`:

- `pinwheel_route_import import {runtime_relaxed_ndr_net ...}` starts one session.
- `pinwheel_route_import snapshot path` exports every valid 2-D and 3-D edge's
  capacity, reduction and usage, plus effective per-net costs.
- `pinwheel_route_import route {exact_dirty_signal_net ...}` invalidates those
  old routes and calls the native solver only for the declared edit. It avoids
  repeating global macro pin-access capacity adjustments.
- `pinwheel_route_import finish` refuses unrouted edits and saves native guides.
- `release net` and `restore {net ...}` exist for removal and edit/revert controls.
  Restore uses native removal and original per-net replay, never a bulk copy of
  resource arrays. Restore alone does not revert circuit edits; the fixture must
  restore the circuit first and compare independent readbacks afterwards.

Admission requires more than successful commands: exact saved-grid and route
comparisons, independent resource-delta checks, a circuit edit/revert control,
unchanged original geometry and clock routes, independent logic verification,
and fresh timing are experiment-level gates. The serialized checkpoint cannot
establish bitwise identity of all original transient 2-D optimization state.
No detailed routing, DRC/LVS or silicon claim follows from this adapter.

The qualified revision also refreshes cached aggregate overflow and the 2-D
congestion flag from the reconstructed edges. The first compiled adapter
restored the arrays but left that scalar stale after a no-edit import. Both
binaries and the follow-up no-edit/edit-revert controls are retained. The final
counter revision reproduces the measured candidate's complete route and edge
state. See the [study](../../docs/physical/route-import-fix-experiment.md) for
controls, the one-buffer result, costs, and remaining routing obligations.
