# SRAM and latch feasibility

This closes the primitive-feasibility portion of the [storage study](storage-study.md).
The measured flip-flop implementation remains the implementation candidate.
These primitive measurements do not constitute an SRAM- or latch-based machine.

## Pinned SRAM evidence

The CMOS5L PDK at `607e18d4bd9214a52575c194b4181ef449f9252f` contains
[`libs.ref/sg13cmos5l_sram`](https://github.com/IHP-GmbH/ihp-sg13cmos5l/blob/607e18d4bd9214a52575c194b4181ef449f9252f/libs.ref/sg13cmos5l_sram),
a symbolic link to the sibling SG13G2 SRAM library. Thus the public PDK provides
a concrete SRAM reuse path; a directory name alone was insufficient evidence.
The inspected target library is fixed at IHP Open PDK revision
[`5e6d592e4002946a4616f798c357f0f3c06cf3b6`](https://github.com/IHP-GmbH/IHP-Open-PDK/tree/5e6d592e4002946a4616f798c357f0f3c06cf3b6/ihp-sg13g2/libs.ref/sg13g2_sram).
The two repositories must be installed with their expected sibling relationship;
this study downloaded selected views, not a complete PDK installation.

| Single-port macro | LEF dimensions, µm | Footprint, µm² | Potential allocation |
|---|---:|---:|---|
| `RM_IHPSG13_1P_64x64_c2_bm_bist` | 784.48 × 64.36 | 50,489.1328 | Both 32-entry dictionaries; bank selects one half |
| `RM_IHPSG13_1P_512x8_c3_bm_bist` | 236.80 × 110.38 | 26,137.9840 | Both 256-entry address maps |
| `RM_IHPSG13_1P_512x64_c2_bm_bist` | 784.48 × 191.34 | 150,102.4032 | Both direct 256-record images |

The indexed allocation has **76,627.1168 µm²** of macro footprint and reserves
8,192 physical bits for 6,080 logical dictionary/map bits. Metadata, controller,
cache, decoder, clocking, routing, halos, power distribution, and loading logic
are additional. The direct alternative uses more memory footprint but removes
the index-to-dictionary dependency. These are geometric allocations, not measured
whole-machine area savings. The 784.48 µm width also makes aspect ratio and
floorplanning material; a small area sum does not ensure a legal placement.

The [behavioral model](https://github.com/IHP-GmbH/IHP-Open-PDK/blob/5e6d592e4002946a4616f798c357f0f3c06cf3b6/ihp-sg13g2/libs.ref/sg13g2_sram/verilog/RM_IHPSG13_1P_core_behavioral_bm_bist.v)
updates its output register on a positive clock edge when reading is enabled.
It supports masked writes and shows the newly masked data when reading and writing
the same addressed word together. This is a different read contract from the
current combinational stores. Integration must also bind the enable, bit-mask,
and BIST controls and use the corresponding timing/physical views.

The atomic loader currently rejects uploads while execution is busy, which avoids
execution/upload port contention. It does not eliminate the execution read-latency
problem. An indexed SRAM lookup introduces a dependency between an address-map
read and a dictionary read.

## The scheduling gate

The present machine can capture an input, use that capture to choose a branch,
and enter its successor on the same protocol edge. A synchronous SRAM cannot
supply an unanticipated record to a register that is sampling on that same edge.
A one-word cache fixes the current-word read but does not solve successor supply.

A future SRAM experiment needs an explicit schedule and proof obligations:

1. Define request/response latency, reset, retained outputs, disabled reads, and
   simultaneous read/write behavior for the selected macro.
2. Hold the current record and prefetch both possible branch successors before
   terminal capture. The branch decision must select records already available.
3. Account for the dependent map/dictionary accesses and the worst case of
   consecutive one-cycle instructions and branches. Average I²C wait time cannot
   justify the general engine's schedule.
4. Either establish sufficient ports/buffering under the existing clock contract,
   or introduce a faster internal schedule with a proved correspondence to the
   same external pin/capture edges. Extra visible wait cycles require a changed
   contract and are outside this study.
5. Prove reset/commit invalidate pending reads, prevent responses from the old
   image entering the new one, and retain atomic replacement. Then test a macro
   simulation model and measure the complete wrapper and physical implementation.

No SRAM replacement is adopted here. The verified scheduling contract must come
before memory inference or macro mapping. The
[memory abstraction](memory-abstraction.md) (2026-09-17) now states that
contract and proves obligations 1, 2, 4 and 5 at the functional level: a
prefetch machine that reads both candidate successors from next-state values on
two read ports refines the atomic reference edge for edge. Obligation 3 becomes a
structural constraint: the composite read is latency one only if the address
map or the dictionary stays combinational.

## Latches

The pinned typical CMOS5L standard-cell library contains these cells:

| Cell | Cell area, µm² |
|---|---:|
| `sg13cmos5l_dfrbpq_1` (FF reference) | 48.9888 |
| `sg13cmos5l_dlhq_1` | 30.8448 |
| `sg13cmos5l_dlhr_1` | 32.6592 |
| `sg13cmos5l_dlhrq_1` | 27.2160 |
| `sg13cmos5l_dllr_1` | 34.4736 |
| `sg13cmos5l_dllrq_1` | 29.0304 |

For 6,080 storage bits, multiplying the reference FF area gives 297,851.904 µm²;
multiplying the smallest listed latch area gives 165,473.280 µm². This comparison
is a cell-only lower bound. It omits clock/enable circuitry, input buffering,
write decoding, timing closure, and the remaining machine. The latch cells have
different polarity/reset behavior and are not interchangeable replacements.

A transparent latch can change during part of a cycle. Directly gating it with
live host command/data can therefore modify staging storage before the edge on
which an upload is accepted or rejected. A viable implementation needs a phase
contract, stable write selection, and appropriate clock/enable circuitry. A
registered upload followed by a separate write phase may preserve external
behavior, but requires a new phase-aware proof and a check that commit cannot
expose an incomplete write. The existing edge-based equality theorem alone does
not establish that behavior.

## Reproduction and decision

`python3 scripts/inspect-storage-macros.py` downloads selected public views at the
fixed revision and records SHA-256 identities, LEF dimensions, and typical/slow
Liberty metadata in `build/storage/macros/report.json`. It does not install tools,
map a design, or run placement/routing. The standard-cell source identity remains
in `tools/technology-library.json`.

Carry the general **32-entry, dense, cached flip-flop candidate** into a separate
physical-feasibility milestone: an actual floorplan, placed/routed area, clock
constraints and full timing analysis, plus translation/equivalence evidence.
Retain the 64-entry machine for programs that do not fit the smaller dictionary.
Keep the repetition backend as a bounded research result until its abstraction
supports the intended protocol set. Pursue SRAM or latches only with the read or
phase contract above; their raw bit-cell savings are not sufficient grounds to
replace the measured implementation.
