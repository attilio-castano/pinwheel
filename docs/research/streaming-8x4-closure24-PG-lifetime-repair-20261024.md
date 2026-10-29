# Same-target PG observer lifetime repair

The first final PG observer failed before its checks. Its preserved report is
`final24-PG-01/report.json`, SHA256
`3140bad96810c57a67f9dc7ce4c92c9fdb0d1a939c03a14e6cfeca09f1209371`.
The OpenROAD leaf returned −11 with `Signal 11 received` in
`ord::OpenRoad::readDb`; it produced no PG marker, rail error report or
`native.json`. The outer worker returned normal failed2 after 10.677 seconds;
its resource report SHA256 is
`b3c8ac46266363c3f806cafc119e3f9058cd6c501a96b91cdfd322acd09b6e71`.
Inputs and owned cleanup closed. No PG check or numerical/physical pass is
inferred from that failure. The sparse resource observations are not an OOM
diagnosis.

The failed loader constructed `Design(Tech())`. At exact OpenROAD
`dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`, `Design.cc` stores a raw `Tech*`
and dereferences its `app_` member for `readDb`; `Tech.cc` owns and deletes
that OpenROAD application. The Python interface exposes these classes without
an argument keepalive hook. A temporary Tech can therefore be destroyed before
the next statement, leaving a dangling application pointer. This is a strong
source-backed explanation of the observed load-time signal. The same
`f516ffbca3cd86e5cd214c515ca0be457a91a517dbe715caa47336aec907eee0` ODB
was successfully read by both the canonical C exporter and the final V
Tcl/raw-ODB exporters in the same pinned image. Corrupted ODB bytes are not
established by the PG crash.

Six exact primary files are retained as data under
`build/campaigns/8x4-20261024-01/pg-lifetime-source-01`; manifest SHA256 is
`8ab5ad5fcab77443c603771eb245b42d9141b66da52655c3a333249ed3667b0b`.
The files are `Tech.cc`, `Design.cc`, their two headers, `OpenRoad-py.i` and
`OpenRoad.cc`, with exact byte/size/Git-blob identities and pinned URLs.
They are never imported or executed.

The new context and entry point are
`streaming_8x4_closure24_pg_lifetime_context.py` and
`streaming_8x4_closure24_pg_lifetime.py`. They adapt the exact immutable
controllers in isolated namespaces. The only Native loader change is:

```diff
-design=Design(Tech());design.readDb(request['source_odb']);block=design.getBlock()
+pg_tech_owner=Tech()
+design=Design(pg_tech_owner);design.readDb(request['source_odb']);block=design.getBlock()
```

The unique strong owner remains live through the complete callback, including
the same-ODB inventory, all actual PG ITerm/MPin/BPin geometry, all supply
terminals, both rail queries and final unchanged-input/census checks. The
Design/OpenROAD instance, no-skip/no-waiver flags, positive PSM graph-statistic
and connectivity log joins, empty error-file requirement and strict readers
are unchanged. So are one CPU, 2 GiB, no extra swap, the 180-second OpenROAD
leaf, 240-second internal supervisor and planned 300-second campaign guard.

Preparation/run receipts have new `power-grid-lifetime` schemas. They bind
the original failed receipts, exact same selected target/views and primary
source data; the old PG01 producer/preparation/reports are not rewritten.
The unchanged canonical internal request/result protocol remains separate
from the new HOST authority. Preparation always leaves actual repair
observation false; only a fresh successful Native callback could establish
that loading and the retained PG checks actually completed.

Eight portable controls pass normally and under `python3 -O`. A weak-reference
backend reproduces the unsafe temporary-owner failure, then executes the
complete repaired callback with collection at intermediate census/PSM calls,
confirming both rail checks run while the owner remains alive. Complete source
reversal and AST controls preserve all other Native/reader/supervisor bodies,
resource limits, strict terminal flags and false scope flags. Context controls
reject target/source/failure/owner/claim changes. No CAD or actual ODB is read
by these controls.

This repairs an observer API lifetime, not a physical placement strategy,
model, routing or numerical policy. Geometric same-rail open-path connectivity
remains the only possible PG claim. PSM's short check is a stub; cross-rail
shorts, cell-internal GDS, package delivery, IR drop, activity and EM remain
outside this leaf, and physical/model/timing/tapeout acceptance stays false.
Root must commit/review the fresh preparation and grant a separate guarded
Native GO. The actual repair has not yet been observed.
