# Buffered SRAM overnight routing and qualification

Closed 2026-10-16. **Retain C14 as the best completed routing checkpoint, with
physical acceptance rejected.** The [tracked result manifest](../../physical/experiments/tt-buffered-overnight-campaign-results.json)
owns checkpoint identities, compact measurements, source bindings and evidence
retention; the [archive receipt](../../physical/experiments/tt-buffered-worktree-retention.json)
owns off-worktree custody. The [next experiments](../research/tt-buffered-next-experiments.md)
record proposed work; this study grants no new execution authority.

## Comparison and frozen contract

The question was whether longer, controlled detailed routing could improve the
saved P2 layout without changing the design. The campaign froze RTL, serial
ABI, all 28,970 instances and masters, placement, SRAM pins/obstructions, power
geometry, clock topology, SDC and original technology/NDR rules. Signal and
clock **route geometry** could change; clock topology could not. No cell
insertion, resizing, finishing or placement ECO was performed.

| Completed source | Native DRC records | Disposition |
| --- | ---: | --- |
| Matched original P2 control | 22,115 | Reference, reproduced by fresh control |
| C3 | 7,973 | Retained comparator |
| C9 | 1,889 | Retained comparator |
| **C14** | **1,732** | **Best completed routing; 92.17% below reference** |
| C17 | 2,511 | Rejected; 779 more than C14 |

C14 has 889 metal-short and 843 metal-spacing records, including 1,585 Metal4
records. Its exact-geometry control regenerates 1,731 markers; that one-record
difference earns no physical improvement credit. The earlier 30,218-record
first-pass diagnostic used different initialization and is not the matched
denominator. C17's regression is concentrated below y = 300 µm, mainly on
Metal4. More routing iterations are not a reliable improvement policy.

## Qualification and what passed

The native adapter repaired import/export loss of per-path default/NDR TAPER
semantics. Positive, negative and unsupported-form fixtures and full no-edit
wire/rule controls passed. Observers were separately qualified; earlier failed
observation gates and the final failed producer remain preserved. Fifty-five
native jobs ran without overlap. Final closeout verified all 507 protected
sources and seven reference files unchanged, with owned jobs/processes stopped.
This campaign proved no new core theorem and did not rerun the retained finite
upload-to-pins or mapped protocol regressions.

| C14 same-source check | Actual result |
| --- | --- |
| Three-Liberty-corner extracted STA | Slow setup −7.353613 ns; fast hold −0.023768 ns; 372 slow setup / three fast hold failures |
| Public PDK recommended-enabled GDS DRC | **Fails: 4,053 records**, including 2,053 NW.b |
| Boundary GDS LVS | **Fails pin matching**; SRAM supplies collapse onto VPWR |
| Antenna | **Fails: 124 nets / 135 INPUT contacts** |
| Official Tiny Tapeout precheck | **Not run** |

SPEF coverage checks pass for 28,948 consumed nets and 90,759 contacts. Timing
uses one nominal SG13G2-derived RC model whose CMOS5L stack calibration and
min/max corners remain unqualified; FAST combines −40 °C logic and −55 °C
SRAM. Electrical/table-domain limits remain open. Named-net STA is conditional
on intended connectivity while the actual layout contains shorts. Earlier
positive estimated margins are not an identical-wires extracted comparison.

Public DRC and router counts use different rules and cannot be combined. Actual
geometry demonstrates signal bridges across SRAM supplies and a fixed-cell
NWell gap of 0.480 µm against a 0.620 µm rule. Routing cannot move those wells.
Boundary comparator fault fixtures qualify sensitivity, not chip LVS or SRAM
interiors; extraction warnings remain unresolved. Local TT geometry checks on
C9 and a separately captured newer whitelist do not establish official precheck.

## Diagnosis, disposition and retained evidence

A C14 restart fails DRT-1231 on storage1/A_BM[31], net7845. The observed worker
ends at y = 144.000 µm; both fresh access points lie at 144.130 µm, leaving
zero eligible points. An internal wire split on the boundary is a proposed
cause requiring a geometry-preserving counterfactual. The actual Python
Design router used one thread despite frontend CLI `-threads 4`; increasing
concurrency is a different experiment requiring a fresh control.

The ignored local [morning report](../../build/physical/tt-overnight-campaign-20261015/MORNING_REPORT.md)
and [verified closeout](../../build/physical/tt-overnight-campaign-20261015/FINAL_CLOSEOUT_VERIFIED.json)
retain detail; the tracked manifest explains custody of the sealed copied
evidence pack. Its external native runtime was not packed, and remote image
availability was not tested. A clean Git checkout alone cannot reproduce the
CAD observations. This buffered design and the older 512×64 chip differ in
architecture, capacity and instance count; no overall superiority is claimed.
