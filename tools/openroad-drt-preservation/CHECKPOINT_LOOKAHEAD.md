# Completed-iteration checkpoint lookahead

Status: source-grounded proposal only. No exporter was implemented, compiled, or
run for this assessment. The qualified ordinary routing pipeline remains the
preferred path; retain a successful through-3 result before considering another
adapter change. Revisit checkpointing only if actual longer-run limits prevent
useful progress.

## Why the native debug snapshot is not a neutral export

The pinned source revision is
`dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`.

In retained `build/physical/tt-overnight-taper-tools-01/source-extra-03/FlexDR.cpp`,
lines 1994–2009, the snapshot runs after completed `searchRepair`, after the
zero-marker exit, and before progress cancellation and iteration increment.
It calls `io::Writer::updateDb` on the live database before writing the ODB.

In retained `source/src/drt/src/io/io.cpp` beneath the same tools output:

- Lines 3883–3914: `updateDb` updates pin access, destroys/recreates non-fixed
  wires, and processes BTerms above the allowed routing layer. The `snapshot`
  argument passed into `updateDbConn` is unused by that method.
- Lines 3791–3798: pin-access export rebinds live `frAccessPoint` DB pointers and
  clears the master's update indices. Lines 3844 and 3879 clear live instance
  and terminal pin-access update flags.

Consequently, rebinding the snapshot to the corrected Writer repairs the known
wire serialization defects but does not establish read-only behavior. Calling
the full `updateDb` with a detached database is also insufficient: it still
changes live `frDesign` pin-access bookkeeping and can attach its pointers to
clone-owned access points. No source argument presently proves those changes
irrelevant to subsequent routing.

## Narrow feasible alternative, if later needed

Ordinary routing calls `TritonRoute::dr` and then `FlexDR::main`
(`source/src/drt/src/TritonRoute.cpp`, lines 675–691). Copying `stepDR` alone does
not affect that path. Manually invoking `stepDR` would bypass the normal
strategy loop and is not an equivalent checkpoint solution.

A versioned implementation could bind an exact copy of `dr` and the normal
`FlexDR::main` through the existing local-symbol mechanism, inserting one
completed-iteration export callback without changing search/repair strategies,
adaptive clip sizing, marker exits, progress checks, or iteration numbering.
The callback must avoid the full live `updateDb` path.

One plausible exporter uses a detached database loaded from an immutable physical
template and only the corrected route serialization primitives:
`fillConnFigs(false)` copies segments, vias, and patches into writer-owned
storage (io.cpp 3190–3228, 3507–3520); `updateDbConn` writes the supplied DB
block (3565–3688). The implementation would remove stale non-fixed wires in the
detached database, serialize all current route figures and generated vias, and
skip both pin-access update and above-top BTerm processing. Whether that can
faithfully represent this design remains a qualification question. A pure
geometry/rule dump reconstructed in a fresh process is another option, with a
larger custom-format validation burden.

Such a file is a route checkpoint for a fresh incremental restart. It is not a
serialization of all live router state: strategy position, adaptive clip state,
worker history, and marker history are not preserved by an ODB. A fresh normal
run starts its ordinary scheduler again and must not be described as exact
continuation at the next strategy index.

## Required qualification before a real longer trial

1. Pin the source, ELF, adapter, callback, and serializer hashes. Prove actual
   local symbol binding; prohibit native snapshots and unrelated flow modes.
2. Run matched callback-disabled/enabled no-edit controls. Require exact live
   ODB geometry/rules and live `frDesign` geometry, PA identities/update flags,
   marker state, and relevant scheduler state before/after each callback.
3. Use a miniature genuine DRC repair with ordinary through-3 routing, not only
   an importer fixture. Under a deterministic test configuration, require
   identical final routes, effective path rules, iteration DRC tables, native
   connectivity observations, and final scope with the callback enabled and
   disabled. Retain mixed default/NDR widths, vias, patches, and endpoint
   extensions in the serialization regression matrix.
4. Require a real P2 no-edit control and a completed-iteration checkpoint whose
   full route multiset agrees with the live router state and whose fixed cells,
   SRAMs, PG, clock topology, rules, and layer limits agree with the template.
   Validate fresh import and final corrected export independently.
5. Bound checkpoint number, wall time, memory, and atomic file publication.
   Export only after all workers of that iteration have joined. An interrupted
   run may expose the last completed checkpoint, never a partially written or
   mid-iteration state. Production multithread nondeterminism must be reported
   separately from adapter-induced differences.

No current routing experiment is changed by this note.
