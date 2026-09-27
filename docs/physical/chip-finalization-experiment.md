# Repaired chip final layout checks

The September 27 continuation takes the exact checked
[chip repair](chip-closure-results.md) through layout finishing and final checks.
The user authorized this gate after its explanation. Preserve the source and all
earlier receipts. This is a tail-of-flow continuation of the existing candidate;
it allocates no fourth architecture/full-routing A attempt and no B attempt.

Start from `chip-closure-01/candidate-05/output/native/final.odb` with empty
initial metrics. Freeze the source netlist, database, previous checked results,
pinned container, PDK, configuration and recipes. Fill/decap insertion is the
only intended circuit-database change. Require all pre-existing instances,
signal connections, original antenna bindings, physical clock routes, signal
wires, ports and power geometry to survive. Verify the final circuit separately;
allow only declared library filler/decap cells with no signal terminals.

Resume the standard flow at fill insertion, extract fresh parasitics, check
every recorded setup/hold/electrical corner, export GDS, run full-rule Magic DRC
and LVS, and inspect power/connectivity and antenna results. Where supported,
extract the LVS circuit from exported GDS. Record the actual extraction source,
macro blackboxing and disabled checks; do not equate tool availability or an
absent metric with a pass. Keep final route coverage, consumed-net annotation,
64 SRAM write holds, circuit readback and package-pin replay explicit.

Before interpreting any final timing result, independently bind its netlist,
database, constraints and new SPEF. No routing, clock, electrical-limit or timing
constraint relaxation is authorized by this experiment. A failed final check
remains a failure and receives a diagnosis; a tool/interface repair requires a
new recipe and retained failed receipt.

Reserve at most 1,800 CAD seconds for this continuation within the campaign's
28,800 seconds, starting at 6,324.523 seconds. Bound each native finalization
invocation to at most 900 seconds, four CPUs and 6 GiB; use one offline CAD
container at a time. Count independent CAD checks and failed runs. Evidence lives
under `build/validation/chip-finalization-01/`.

Passing these checks establishes the stated final-layout evidence for this
candidate. Fast logic/SRAM characterization compatibility, complete timed Lean
controller/loading/package refinement, accepted A, capacity-change B,
clean-source replay and competition admission retain their separate gates.
