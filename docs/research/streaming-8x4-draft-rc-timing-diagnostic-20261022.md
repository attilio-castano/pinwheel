# Fixed-target draft-RC timing diagnostic plan

Prepared from pinned local source before diagnostic implementation or Native
execution. Root must approve the concrete adapter and separately admit the
closed target. This is a new model-consumer diagnostic, with
`model_qualified=false` and `qualified_timing=false` under every result.
It cannot replace the original flow receipt or create a physical candidate.

The target must be the latest actual ODB selected by the existing typed final
authority after a unique completed DetailedRouting state and closed owned
cleanup. An interrupted prefix is insufficient. The original 8x4 and separately
typed post-antenna candidate remain distinct through `physical_candidate`.
Prefer the existing closed final-views packet: its canonical read-only exports
supply `design.def`, `signoff-views/implemented.v`, actual `inventory.json`, and
the exact source ODB binding. A carried pre-antenna netlist or proof-only graph
is forbidden. Every signal-bearing actual instance, including passive antenna
loads, must be present in the timing graph.

The canonical RCX class consumes DEF, not ODB. Fresh same-ODB DEF provenance is
therefore a required join. STAPostPNR runs OpenSTA on NL plus SPEF; its optional
ODB is used by the canonical unannotated-net filter. It does not analyze the
ODB graph directly. The read-only ODB, freshly exported NL/DEF, all six original
standard-cell/I/O Liberty files, original technology LEF, and complete original
SDC must be bound before and after the diagnostic. No PDK byte changes.

| Pinned source/input | SHA256 |
| --- | --- |
| LibreLane `steps/openroad.py` | `e74a7d61680e4ec700a1ae6b9ca2c6148b97d3f8c6d670db4b12c57ec65b04db` |
| `scripts/openroad/rcx.tcl` | `932121962e2c1853048fe1def545d90c66f44e6c65c3b77a8990fbb7a69d531f` |
| `scripts/openroad/sta/corner.tcl` | `e0096884c1929ed80506366ecc3e809c78c8493180e366fc095e2b09f5c36f53` |
| `scripts/openroad/common/io.tcl` | `c7b28322f0853c7c6ebe6076a454c0baf3d97cc6194c0931eae7bf17a442b80f` |
| Canonical `filter_unannotated.py` | `1af71a8ff58dafa4cf88793edfa9e432ee1b7ad347668d60da50f751c03d8434` |
| Original complete `core.sdc` | `bcfd5a3ee86ccf13d6a8851e4b8d05b02584926862b922efa00204b3f628d0e5` |
| Original five-metal technology LEF | `3edd5a1ad31e8307be537d0d1b85c3258fefeb21aac04aaa476e4f72de4cffd5` |
| Inherited seven-layer aliased RCX rules | `ffda02d57a6ecb39b02268be9511d89ef072911f17bd2dcd095f3f3cbeb5a905` |
| Owned rules consumer plan | `51a58576fe349c88b6900185db8c7134172564d1ffcda40e46595747e3c1378a` |

Source files are retained under campaign `intake/librelane-native-source`;
its manifest binds the exact image
`sha256:5825633bea1f9cbc705ece2de2bc31de6e4ec83d233739205a0f265ef9d92f92`.
The consumer source is pinned OpenROAD `dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`.

Three fresh sequential passes use the owned MIN, TYP and MAX files from
`rc-consumer-preparation-02/*-owned_explicit_via_rules.txt`, copied into the new
diagnostic inputs and hash-checked against that plan. Only the existing
`RCX_RULESETS["nom_*"]` model path changes in each diagnostic config. Its
LayerCount changes from inherited 7 to draft 5. All three original cell corners
remain unchanged in every pass: `nom_fast_1p32V_m40C`,
`nom_slow_1p08V_125C`, and `nom_typ_1p20V_25C`. This yields nine cell-by-draft-RC
cases and avoids inventing a foundry-approved cell/metal corner correlation.
Each fresh state contains only the bound ODB, actual NL/DEF, complete SDC, and
empty inherited SPEF/SDF/LIB/metrics. No result may carry another pass's SPEF.

Each pass executes unchanged `OpenROAD.RCX` then `OpenROAD.STAPostPNR`, using
the pinned registered flow with `--from OpenROAD.RCX --to OpenROAD.STAPostPNR`.
Its earlier/later scheduled steps are skipped and are never called executed
ordinary-flow checks. The original resolved config remains otherwise exact;
no clock, exception, I/O delay, load, uncertainty, cell corner or design rule is
relaxed. `--jobs 1` bounds the global executor, while the explicit resource
environment `_OPENLANE_MAX_CORES=1` serializes the separate canonical per-corner
executors (`STA_THREADS` remains null). The CLI callback alone only changes the
global executor and is insufficient. The original explicit OpenROAD thread
count remains unchanged.

Canonical `rcx.tcl` always includes `-lef_res`. The pinned extractor source
retains LEF wire resistance under that flag. The retained LEF values equal
merged ITF MAX, so these passes do not establish MIN/TYP/MAX wire-R behavior.
The five-metal draft capacitance tables and owned explicit VIARES entries are
presented to the unchanged canonical consumer. A logged rules path does not
prove which numerical fields affected the result; that remains a measured
consumer question, particularly for via behavior under `-lef_res`. VIARES uses
ITF per-cut resistance divided by counted explicit cuts, an unqualified
parallel-cut assumption. Generated
dbVia coverage, contact physics, all used widths and layers, and model accuracy
remain separate gaps. The unexecuted six-call consumer fixture uses a different
declared policy (`-no_merge_via_res`, no `-lef_res`) and cannot qualify this one.

One additional observation-only config hook needs explicit review:
`STA_EXTRA_CORNER_TCL_FILE` points to a frozen read-only query script. The
canonical body remains unchanged. The hook may query and print graph/clock
facts or reject a missing binding; it may not set constraints, edit the graph,
read another model, estimate parasitics or alter timing. It must confirm exact
master/name membership for all signal-bearing actual instances and exact
actual passive-cell signal-pin/net connections. It also queries the actual
`clk` period 20 ns and `is_propagated == 1` after the unchanged SDC executes.
This prevents assuming that a generic Verilog writer retained antenna loads.

The hook also avoids a known pinned report-label defect: `corner.tcl` sets
`is_virtual` rather than `is_propagated` when formatting its `Propagated:` label.
Preserve that raw report unchanged; require the independent Boolean query,
the nonempty exact `clk` inventory/period, empty canonical `unpropagated.rpt`,
and full expanded-clock path reports. The SDC itself explicitly calls
`set_propagated_clock` when canonical post-PnR sets ideal-clock mode to zero.

The query API was checked against OpenROAD's pinned OpenSTA submodule
`857316ff001b2a8dbbdc5996944d08a6d38c87ab`:
[`get_cells/get_pins/get_nets`](https://github.com/The-OpenROAD-Project/OpenSTA/blob/857316ff001b2a8dbbdc5996944d08a6d38c87ab/sdc/Sdc.tcl#L343),
[`get_full_name`](https://github.com/The-OpenROAD-Project/OpenSTA/blob/857316ff001b2a8dbbdc5996944d08a6d38c87ab/tcl/CmdUtil.tcl#L278),
and [instance `ref_name`, pin/net `full_name`](https://github.com/The-OpenROAD-Project/OpenSTA/blob/857316ff001b2a8dbbdc5996944d08a6d38c87ab/search/Property.cc#L938).
The observer enumerates object handles, so it does not interpret cell names as
glob patterns. OpenSTA's [SDC network adapter](https://github.com/The-OpenROAD-Project/OpenSTA/blob/857316ff001b2a8dbbdc5996944d08a6d38c87ab/network/SdcNetwork.cc#L643)
reverses internal syntactic escapes for ordinary names containing brackets or
slashes. Tcl braced dict keys retain their literal spelling. Genuine backslash,
brace and newline names are explicitly unsupported and reject rather than being
translated speculatively. This source check is not a separate provenance proof
for the installed standalone `sta` binary: the actual hashed executable and
successful observer execution remain mandatory runtime observations.

The adapter wraps `TclStep.run_subprocess` only to journal the exact argument
vector and complete pre-reroute environment, then delegates the identical call
to the unchanged method. Canonical `_env*.tcl` files remain retained too. It does
not wrap timing graph or model operations. The wrapper, query script and
complete producer dependency closure are frozen before a Root-admitted run.

Retain all canonical logs, exact command/environment files, fresh state files,
SPEFs, SDFs/LIBs and metrics. Reopen each model-to-SPEF and cell-corner-to-SPEF
binding; require all three cell corners actually execute. Capture raw and
canonical-filtered unannotated/partially annotated counts, and independently
join SPEF net/connection inventory to the actual ODB signal nets/terminals.
Missing or unsupported coverage grammar is explicit incomplete evidence.
Reuse the pure `streaming_tt_quality.timing_quality` reconciliation for
consumed-net annotation and raw fanout rows, preserving its precise scope.
Record setup/hold slack/counts, slew/cap/fanout violations and unconstrained
checks per case. Negative results remain measured failures; zero slack
violations alone never qualify the model or timing.

Budget: one owned offline container, at most four CPUs and 6 GiB including
swap limit 6 GiB, bounded scratch, immutable pinned image and read-only
inputs/PDK/target. Proposed whole leaf is 1080 seconds with a 1200-second outer
guard including cleanup reserve; approximately 900 seconds is available for
three passes and 180 for verification/closeout. These are ceilings, not runtime
guarantees. Expected direct native inventory is three RCX OpenROAD calls,
nine OpenSTA calls and nine canonical ODB annotation-filter calls. If the
whole matrix cannot finish, preserve every partial output and report incomplete;
no corner reduction or timeout extension is implicit. This is a fixed-target
validation slice, admitted only under Root's shared heavy lease and deadline.
