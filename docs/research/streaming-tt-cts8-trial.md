# Controlled CTS8 trial for the fresh balanced candidate

This is an unexecuted physical experiment. It requests explicit eight-sink
clustering in the pinned CTS implementation; it does not establish a maximum
fanout on actual clock nets, improved timing, or physical acceptance.

The paired recipe baseline is commit
`71decd66e04c0aadcc2ae4447c59013b22ac3ece`, candidate configuration SHA256
`5407fb171ab040ce83e50cb867a5215de6080638f4595b3575e0932c0a659513`.
The only new configuration delta is `CTS_SINK_CLUSTERING_SIZE: null → 8`.
The historical five-setting ledger against the original coarse03 recipe is
retained independently. The source retains the same 20 ns clock, 0.2 ns
uncertainty, 4.0/0.2 ns I/O delays, 10 fF output load, clock drive assumptions,
all-corner requirements, Metal4 routing ceiling, die allocation, and state and
buffer capacities. The already admitted PDN correction is described separately
in [the power-grid admission](streaming-tt-pdn-clearance.md).

Pinned native CTS source captured by the closed PDN probe is
`build/streaming-physical-development/pdn-clearance-unqualified-02/pinned-tool-source/scripts__openroad__cts.tcl`,
SHA256 `436f4f89f290f14cc2c982907af79a8a79f9f56b64e9bfe83ff63636ce6608d5`.
Lines 67–71 forward clustering size as `-sink_clustering_size` and the enabled
flag as `-sink_clustering_enable`. The retained resolved configuration enables
clustering, leaves size and maximum diameter null, uses root buffer `buf_8` and
buffer choices `buf_8/buf_4/buf_2/buf_1`, and disables clock NDR. The trial
requires resolved enable=true and integer size 8, plus the actual native CTS log
command containing both expected options. Diagnostic DRT admission checks the
hash-recorded resolved configuration and CTS log. A log saying that automatic
search found size 8 is insufficient to pass this delivery check.

A bounded runtime inventory now reports OpenROAD revision
`dcf36133a369abc8f3c5e5738cd4d82e4903c0e0` in its startup banner, with executable
SHA256 `b2159d4a99a9b236a6e95bbf6efc88bcfd2b843df273e97f169b456bc3b0453b`
inside the pinned image. The `ord::openroad_git_describe` command exists but
returns an empty string. The strict inventory probe therefore exited 1; its
OpenROAD command exited 0, and resource cleanup/input checks closed. The failed
probe is preserved without being upgraded to a passed job. A separate host
interpretation binds both observations at
`build/streaming-physical-development/pinned-tool-inventory-interpretation-unqualified-01/report.json`,
SHA256 `5a89f71860532c8759c5a599dc366c7debbeea3e48d961c1595e7ef86465dc62`.
Reported build revision and executable identity are the provenance boundary;
this is not a reproducible-build proof.

The exact upstream source at that reported revision narrows the causal
uncertainty. [CtsOptions.h lines 229–234](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/cts/src/CtsOptions.h#L229-L234)
sets `sinkClusteringUseMaxCap_` to false when an explicit clustering size is
set. [SinkClustering.cpp lines 410–419](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/cts/src/SinkClustering.cpp#L410-L419)
uses a capacitance limit when max-cap mode is enabled, and a size/diameter limit
otherwise.
The retained, Git-blob-checked source intake is
`build/streaming-physical-development/cts-source-research-unqualified-01/report.json`,
SHA256 `62e985aea516f3a5a1708a770254456f6ce849c7cc12da274d2d540bf2249444`.
Thus an automatically reported size 8 can coexist with more than eight sinks,
while requesting size 8 changes a relevant option in this source. Actual flag
delivery and resulting loads still require the fresh trial. Dummy, buffer and
passive inputs added around a cluster can also make total net fanout exceed
the FF count; every load class remains in acceptance accounting.

The option/caller order was also checked, because a setter alone is not enough:
`SinkClustering` snapshots the mode at construction, and explicit reset APIs can
re-enable maximum-capacitance mode. In the retained normal call path,
[TritonCTS.tcl lines 439–449](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/cts/src/TritonCTS.tcl#L439-L449)
sets the explicit size and conditionally sets diameter, without resetting an
omitted diameter, before invoking CTS at line 588. The SWIG bridge calls the
size setter. Characterization clamps a specified size to the buffer's fanout
limit through `CtsOptions::limitSinkClusteringSizes`, reusing the same setter
and preserving its count-based mode; with no explicit size, only the default
candidate-size vector is clamped. `HTreeBuilder` then constructs the matching
object and uses the explicit scalar size while searching diameters. No later
mode reset was found in this examined route.

These eight exact-commit source files and the relevant call sites are bound in
`build/streaming-physical-development/cts-causal-review-unqualified-01/report.json`,
SHA256 `d446a9eec8ca4aa238b288cc3ce689547b7d842e152f17916a848d20478ec584`.
This supports retaining the single size-8 recipe change. During the fresh run,
inspect the register-tree diagnostic for groups of up to 8 instead of clustering
based on buffer maximum capacitance. That message is a diagnostic handoff,
not a new acceptance rule. Small sink sets can bypass preclustering entirely,
and later dummy/buffer loads remain another reason to measure actual nets.

There is still meaningful uncertainty about benefit. The old07 native CTS log already
reports an automatic best solution with size 8 and diameter 50, after stating
that clustering is based on buffer maximum capacitance. Its actual GRT
connectivity contains 394 FF-driving leaf nets serving 6,039 clock terminals.
Their FF loads are:

| FF loads per leaf | Number of leaves |
| --- | --- |
| 3 | 1 |
| 8 | 1 |
| 11 | 3 |
| 12 | 3 |
| 13 | 17 |
| 14 | 61 |
| 15 | 131 |
| 16 | 106 |
| 17 | 55 |
| 18 | 16 |

All 392 clock nets over the pinned Liberty limit 8 are leaf nets. Every one of
the 74 upper/root nets already has at most 8 loads. Leaf loads also include 226
inverter and 56 positive-buffer inputs. The complete topology includes 336
unconnected dummy outputs: 226 inverting and 110 positive-buffer outputs. These
loads remain part of fanout accounting; their unused output nets do not erase
their input load. Thus the original problem is predominantly the produced
leaf clustering, while recursively adding 650 clones can create a new upstream
load problem. Explicit size 8 is a plausible experiment in changing the
automatic behavior, not evidence that the resulting cluster size will be 8.

The host-only anatomy report is
`build/streaming-physical-development/clock-fanout-anatomy-unqualified-01/report.json`.
It binds actual ODB SHA256 `039d396596297963041ef641dcbf246fbcbe0bebd6cd4a6c5c506cb8e340e831`,
its sealed OpenDB inventory, the pinned interpreted Liberty, and the old native
CTS log. It contains every clock-net row, load class, driver master, and unused
clock output rather than only the violating subset.

The 18 signal nets over limit 8 have loads 9×8, 10×6, 11×1, 12×1, 14×1, 15×1.
Seventeen are driven by `buf_1`, one by `buf_4`. Although the configuration says
`MAX_FANOUT_CONSTRAINT: 10`, the selected Liberty declares
`default_max_fanout: 8`, native reports apply limit 8, the custom SDC has no
`set_max_fanout`, and the logged repair command has no fanout option. A change
to the configuration field alone has not been shown to alter delivered
constraints or repair behavior. It is therefore left unchanged in this trial.

Use the fresh balanced source, raw gate, semantic state map, optimizer proof,
and source-correspondence replay as new parents. The old07 candidate and frozen
replay are historical evidence, not parents for the changed source. The paired
configuration comparison isolates configuration differences; it does not
attribute changes from the balanced hardware or PDN to CTS.

Run the fresh coarse flow through global routing, retaining its closed CTS and
post-CTS timing states for diagnosis before any detailed-route admission.
Export the actual ODB connectivity and compare all clock-load classes, leaf/upper distributions,
unused branches, buffer count and area, skew, all-corner setup/hold, slew and
capacitance. Compare fanout against limit 8 including passive/dummy loads. If
the trial reproduces the old behavior or remains overloaded, use measured
load locations for a separate clock-tree/placement repair instead of assuming
the configuration value solved it. Later routing still requires a newly closed
postGRT parent, a complete fresh source-bound replay/private control with its
regenerated module inventory, the full
native tail, final actual-netlist export and new correspondence, and all
physical signoff and official-precheck obligations.
