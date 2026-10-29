# Synthetic diagonal projection, import and consumer control

This two-call proposal tests a software convention with synthetic matrices. It
performs no FasterCap solve, physical coefficient fit, model calibration or
qualification. Root alone may admit Native after source review. The separate
failed full-stack conditioning packet and its mandatory numerical stop remain
unchanged.

Authenticated upstream parser `fasterCapParse.py` (Git blob
`e55a5fd574874fbd9fad45a9ed1c1b09959c16be`) writes ordinary `CC` as immediate
same-layer coupling and prints cross-layer `DiagCC` separately. At pinned
OpenROAD `dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`,
`extRCmodel_solver.cpp:229` reads ordinary `CC`; lines 251–255 store that value
for diagonal tables. The importer does not read `DiagCC`, `DiagWidth` or
`DiagDist`. Open-pattern handling forces `CC=0` and distance zero. A prefix such
as `wire_` alone is not a demonstrated classification defect.

The importer divides total femtofarads by wire length in nanometers and two.
Prior actual marker evidence established two callback contributions to the
stored coupling. Its original 1 pF/m prediction failed by a factor of two and
remains failed; this new control explicitly predicts that convention rather
than relabeling the old receipt.

The declared synthetic three-conductor matrices contain a lower/upper pair
with 2 pF/m coupling and 3 pF/m ground capacitance. Exact 10/20 um differences
recover every signal-matrix cell. The chosen 20 um pair coefficient is 0.04 fF.
Import normalization is `0.04 / 20000 / 2 = 0.000001 fF/nm`; two consumer
contributions predict 2 pF/m. These numbers are declared synthetic unit data,
not CMOS5L physics or fitted values.

Both fresh OpenROAD processes import complete synthetic supporting tables
whose path/role census is bound to all 310 observed native patterns. Regular
capacitance and resistance records are synthetic scaffolding, never qualified
model coefficients. The legacy projection uses the open diagonal slot and
retains an exact zero-coupling failure. The candidate supplies the explicit
pair coupling to a documented nonopen import slot and uses actual edge distance
zero. Logical importer labels select API branches; they do not assert that the
synthetic two-signal reference has three lower-layer neighbors. The format's
missing independent upper-width axis remains an explicit limitation.

Each process then extracts the same six-net/twelve-port, three-length centered
M1/M2 fixture using command version 1.0, threshold zero, no cell/ITerm/via loads,
no NDR and unchanged default widths/technology units. Actual before/after DEF,
full CAP incident totals, mirrored-pair deduplication and complete Maxwell
ground/coupling semantics are checked. The baseline must retain all three zero
couplings and the original strict failure. The candidate must match 2 pF/m in
both 50/100/150 um intervals within 0.1%, preserve coupling linearity within
0.1%, and complete-matrix/ground consecutive slopes within 5%.

The independently parsed imported deck must contain the source-predicted zero
row and differ between calls by exactly one numeric coefficient: M1/M2
distance-zero fringe `0 -> 0.000001 fF/nm`. Any other table change, warning,
nonzero exit, wrong version/unit/geometry or missing coupling fails the control.
No successful-prefix or complete-generation claim confers physical accuracy.

Bounds are two calls, 30 seconds per call, 90 seconds measured work, 120 seconds
outer supervision, one CPU, 2 GiB memory, no extra swap, 128 MiB tmpfs and
256 MiB polled owned output per call. Source, image/executable/version,
input/output, complete raw inventories, cgroup and Root resource/cleanup joins
are independently reopened. Downloaded source is data only. Eight portable
HOST controls pass normally and under optimization. Preparation01 is preserved
unexecuted and superseded by preparation02 after final width/output/work gates.

## Public API and model-context source closure

Preparations01/02 remain preserved unexecuted and superseded by03. The exact
pinned Tcl definitions are in `OpenRCX_process.tcl`, not core `OpenRCX.tcl`:
`init_rcx_model` accepts `-corner_names -met_cnt`, `read_rcx_tables` accepts
`-corner_name -file -wire_index`, and `write_rcx_model` accepts `-file`.
The older `-corner` abbreviation is accepted by the retained STA prefix-key
parser;03 uses the exact full option spelling for clarity.

Tree-confirmed `process_ext.cpp:21` shows init allocates a model and its tables,
then stores the current-model pointer. Read/write require that pointer. These
wrappers and the retained model constructor do not access technology or design
block state, so the original init-before-read_lef order is supported. This
source check changes no coefficient, geometry, semantic policy or numeric gate.
The four public API/class files are bound in
`model24-rcx-api-source-03/manifest.json`, SHA256
`4c55aa722c16faae0192f026cea54d069c59e20f999eee9370ea289df4abee2e`.
Every fetched file's observed directory-entry Git blob was independently
recomputed; none of the downloaded sources was imported or executed. The
fresh03 packet additionally seals both inherited historical resource producers,
for 48 exact producer seals. All older 34/37 and process 22 producers are unchanged.

Preparation03 is also preserved unexecuted. Preparation04 corrects its independent
reader's cgroup dictionary to the frozen producer's literal dotted kernel keys.
A portable control invokes that actual producer with literal mocked kernel
files, then exercises the new contract and rejects underscore/extra/resource
aliases. Nine HOST controls pass normally and under optimization. This is an
artifact-reader repair before Native; the synthetic source/policy/geometry/math
and 48 producer seals remain otherwise unchanged.
