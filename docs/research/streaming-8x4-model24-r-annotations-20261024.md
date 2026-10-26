# Distinct pre/post R terminal-annotation witness, October 24

The decoder02 Native observation failed after extraction because the observer
did not declare the terminal annotations inserted by canonical wire ordering.
Its first MIN leaf reports `Undeclared actual decoder opcode 10`, then exits
one. It was not timed out or memory-killed. All 30 nets had been extracted, but
the strict packet stopped its suffix with zero admitted absolute audits.

The exact saved HOST closeout preserves that failure in
`model24-r-decoder-independent-readback-02.json`, SHA256
`5736e18c1f461c6be3401a3b7bd6e2e6f852a2efd03f7a6c955b3f27d9f6eeec`.
Root's outer guard closes failed with cleanup and input seals confirmed. Before
and after DEF bytes remain identical and retain the complete declared physical
geometry. The complete before TSV demonstrates the new decoder APIs working
for all 30 nets. The after TSV is empty because the Tcl output channel was
buffered when the first BTERM caused an error. Actual post-annotation names,
association and order were therefore not measured by this failed run.

The pinned source explains the mechanism:

- [`ext.cpp:216`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/rcx/src/ext.cpp#L216)
  calls `orderWires` before RC segment extraction.
- [`wOrder.cpp`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/odb/src/db/wOrder.cpp)
  sends each unordered non-supply net through `tmg_conn::analyzeNet`.
- [`tmg_conn.cpp`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/odb/src/db/tmg_conn.cpp)
  prefers an INPUT BTerm as driver at lines 24–44, loads existing wire and
  terminals at 1315–1331 and starts re-encoding at 1432–1458. For this one-body
  fixture, `addToWire` emits each endpoint followed by its associated terminal
  at 1680–1694 and 1786–1813. The exact source shape determines retained endpoint
  extensions at 1560–1606.
- The already bound `dbWireCodec.cpp:399` stores the BTerm identity, its enum
  gives BTERM the value 10 and decoder `getBTerm` returns that actual dbBTerm.
  Existing public BTerm getters supply actual name/net/direction/use metadata.

These are source predictions for the new complete observation. The unique
INPUT `_A` endface and OUTPUT `_B` endface make the predicted order explicit
for every one of the 30 nets; actual observations must still meet it.

RCX also writes non-geometric RC-segment IDs into encoded wire properties:
the retained `netRC.cpp:693–704` creates a segment and calls `setProperty`.
The retained decoder skips internal `kProperty` operands. This control observes
the complete **public decoder geometry/terminal stream**, not every raw wire
encoding operand. It does not assert raw encoding byte identity or expose
internal RC-property IDs. The independent complete DEF, exact public geometric
projection, global inventory and strict complete SPEF graph/reference remain
the geometry and electrical obligations. Root explicitly reviewed this limited
scope; internal property-ID readback is not substituted for a physical claim.

The new source-data intake `model24-r-annotation-source-01` pins `ext.cpp`,
`wOrder.cpp` and `tmg_conn.cpp`, including observed/computed Git blobs. Its
manifest SHA256 is
`253c7626135184d55c8f2a2116a463ea32eea3ed010f259c62236b0d35aa3930`.
The earlier immutable source intakes continue to bind the codec, shape math,
Tcl decoder API and enum typemaps. No fetched source is imported or executed.

The separate new family `streaming_8x4_model24_r_annotations{,_observe,_readback}.py`
requires the following complete observations before any numeric result passes:

| Before each net | After that same net |
| --- | --- |
| PATH and optional exact NDR RULE | Identical PATH and RULE |
| Actual POINT_EXT at `_A`, extension zero | Identical POINT_EXT, followed immediately by actual BTERM `_A`, exact net, INPUT, SIGNAL and attached observed endpoint coordinates |
| Actual POINT_EXT at `_B`, extension zero | Identical POINT_EXT, followed immediately by actual BTERM `_B`, exact net, OUTPUT, SIGNAL and attached observed endpoint coordinates |
| END_DECODE | END_DECODE |

Every net must have exactly these two post-order annotations, no pre-order
annotations and no foreign, duplicate, missing or reordered metadata. Only
after validating all actual annotation records may the exact public geometric
projection be compared. It must match the before stream and all native
block/net/port/layer/NDR/global-endface records. Full before/after DEF bytes
remain identical. Snapshot output is line-buffered so a future error retains
its observed prefix instead of losing the entire buffered TSV.

All 90 controls, source-defined three corners, physical dimensions, ideal
full-endface `Rsheet*L/W` reference and 0.1% absolute tolerance remain unchanged.
So do the extractor policy, strict complete SPEF graph, resource/cleanup/clock
limits and suffix stop behavior. The new HOST reader reopens both previous
failed raw/resource results, including the original opaque-uint64 failure, and
requires exact equality. All 47 decoder02 producers and receipts stay unchanged.

Twenty-two portable controls pass normally and under `python3 -O`. They include
exact positive pre/post association, wrong terminal/name/net/direction/use or
point, duplicate/missing/reordered annotations, unexpected opcodes, changed
physical/global metadata, explicit-zero and full R graph/reference failures,
source-body reuse and both preserved failure authorities. Tests read no ignored
campaign data and execute no Native process.

Fresh preparation01 binds 50 sources and 39 inputs. The plan SHA256 is
`37baf20e3e6a6f21fa4537217686a08badb6432615ad945fcf0b63b28ce15160`;
proposal SHA256
`80619a24c92131ce5bbaf874245e6b1f747d7dfaa91335e518a408b7d4e8b6da`;
launcher SHA256
`50b7a2ecb4cac143bf99d2c74ee5a2b7e08bfc061fda1ba6be7249e3ce78cf7b`.
The launcher carries 94 input seals. At preparation time no Root GO or Native
execution exists; post-order annotations remain unobserved predictions.

After independent review and separate Root GO, only Root may use its saved
`resource_supervisor_argv`. Following actual terminal cleanup and Root's signal,
the saved `HOST_closeout_argv` writes
`model24-r-annotations-independent-readback-01.json`. Even all passing results
would establish this limited ideal-sheet endpoint/consumer convention only.
Arbitrary-route/contact/via physics, capacitance, process-corner correlation,
full model and qualified timing remain false, and numerical conditioning stays
stopped.
