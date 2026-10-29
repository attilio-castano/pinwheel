# Distinct R decoder observer repair, October 24

The original R endpoint02 observation failed because its Tcl observer printed
an opaque `uint64_t` pointer instead of a numeric wire length. This is an API
correctness failure. It is not a new numerical-conditioning experiment, a
geometry/reference rejection or evidence of a successful physical model.

Root's original Native process exits zero without warnings. The first MIN
leaf is resource-feasible and reaped; all source/input/runtime and supervisor
cleanup checks close. Its complete before/after DEF bytes are identical,
SHA256 `2bc98f9e5cb76d90459326913c574eff9ed05d6886b7339e8f17dca9d8c54372`.
Both exact DEF geometry checks pass. However, all 30 TSV NET length fields are
SWIG `_…_p_uint64_t` objects whose addresses differ before and after extraction.
The strict observer therefore correctly stops the suffix before TYP/MAX and
before any admitted R audit.

The exact saved HOST closeout returns two and preserves the failed result in
`model24-r-endpoint-independent-readback-02.json`, SHA256
`08cd85ea8bd440f093bf200c37bfcd2d3779e821499854775790247421b196a2`.
It reports incomplete measurement, zero completed absolute controls and false
model/timing qualification. A separate read-only diagnostic of the retained MIN
SPEF finds all 30 raw R values within the unchanged 0.1% ideal-sheet tolerance
(maximum relative error about `8.89e-7`). That diagnostic does not replace or
promote the failed strict result.

The cause is explicit in the pinned primary SWIG source:
[`common/odb.i`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/odb/src/swig/common/odb.i)
maps `uint32_t`, `uint64` and `int64_t` at lines 39–42, but does not map the
`uint64_t` returned by `dbWire::getLength`. Its lines 74–78 expose the decoder
and rename the three-output overload `getPoint_ext`.
The exact
[`dbWireCodec.h`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/odb/include/odb/dbWireCodec.h)
declares constructor, begin/next, current layer, coordinate/extension and rule
APIs. The pinned
[`test_wire_codec.tcl`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/odb/test/test_wire_codec.tcl)
uses those Tcl APIs and verifies numeric point/extension lists. The retained
Tcl enum typemap explicitly returns `ROUTED` for `dbWireType::ROUTED`.

Six exact primary files are retained as data only under
`model24-r-decoder-api-source-02`; manifest SHA256
`25aef3b0773799f6286c7551e4ca821dd20cfa0671b33d9c955d0c53846dab12`.
They are neither imported nor executed. The prior five-file source intake and
preparation01 are preserved unexecuted/superseded; preparation02 additionally
binds the full Tcl wire-type output typemap.

The new sources are `streaming_8x4_model24_r_decoder.py`,
`streaming_8x4_model24_r_decoder_observe.py` and
`streaming_8x4_model24_r_decoder_readback.py`. They leave all 44 original
producers, original preparation, Native outputs and failed HOST receipt
unchanged. The replacement observation contract requires, for every net before
and after extraction:

- One actual decoder PATH on the declared layer with ROUTED type, optional exact
  native NDR rule/layer/width/spacing, two actual numeric POINT_EXT records with
  zero extensions and an explicit END_DECODE. Every missing, extra, foreign,
  reordered or unsupported opcode rejects.
- The unchanged complete DEF, all global BPin end-face rectangles and statuses,
  all ports/nets/components/ITerms/special-wire counts, actual layer/default/NDR
  widths and exact source-corner sheet values.
- A shape bbox derived from the observed endpoints, explicit extensions and
  native width using the pinned dbShape construction. The reported bbox and
  long-dimension-minus-width are explicitly derived quantities; they are never
  called a measured `getLength` API result.

All 90 controls, three source-defined corners, actual physical dimensions,
independent ideal full-endface `Rsheet*L/W` reference and 0.1% absolute tolerance
remain unchanged. The extractor flags, numeric parsing, reference math, leaf
resource/cleanup code, whole-work bounds and suffix stop policy are reused
without changes apart from distinct receipt schemas. Portable controls compare
those function bodies to the frozen original after schema normalization. The
new HOST reader also independently reopens the original failed raw/resource
result and requires exact equality to the copied failed receipt.

Eighteen portable controls pass normally and under `python3 -O`, with no ignored
campaign data dependency. New preparation02 binds 47 sources and 32 inputs.
Its plan SHA256 is
`6b13e5d1d96406335212a0d39651cfffb667f83a0b5fac80444480f112ebaf8c`;
proposal SHA256
`d1978af4230cc65f7ef4c3ea7990f8bd8000c3dd7b903d89e852a95c5e1bdd24`;
launcher SHA256
`5098ba9bcba5fd8b6c669cf3c96618c5ec4d2faf7fb00d8b26f2523d9b29ee35`.
The launcher has 84 resource input seals, no Root GO and no Native execution.
Its fixed limits remain 30 seconds per Native leaf, 120 seconds work and 180
seconds outer, one CPU, 2 GiB and no extra swap.

After separate Root review/GO, only Root may use the saved
`model24-r-decoder-launch-reopen-02.json:resource_supervisor_argv`. Following
actual terminal cleanup and Root's signal, the saved `HOST_closeout_argv` writes
`model24-r-decoder-independent-readback-02.json`. Even complete passing results
would establish only this ideal-endface sheet/consumer convention: contact or
via physics, arbitrary-route R, capacitance, process-corner correlation, full
model and qualified timing remain false. The failed conditioning stop and all
historical failures remain in force.
