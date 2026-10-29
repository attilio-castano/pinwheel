# Fixed-target 8x4 closeout gates

This is a prepared execution checklist for the October 22 campaign. It is not
a signoff receipt. The initial 8x4 G0 result covers exact boundary, public pins,
power-port geometry and unchanged official Pincheck on a probe database. Every
final gate below must bind the actual completed routed implementation.

1. **Authenticate the final target.** Require a terminal full-flow receipt,
   closed cleanup/input/runtime guards, a completed DetailedRouting state and
   the latest authoritative ODB. Reject timeout, partial router memory, probe
   or GRT substitutions. Keep the original source, 6,039 semantic states,
   20 ns/I/O contract and actual state/output/clock coverage explicit.
2. **Fresh views from that ODB.** Run the unchanged native
   `streaming_tt_export_signoff.py` body for unpowered/powered Verilog, CDL and
   abstract LEF. Bind a genuine completed streamout GDS to that same ODB, or
   stream out the target freshly with exact GDS/LEF dependencies. Preserve all
   original views. If the official LEF parser needs canonical spelling, use
   the existing exact-coordinate adapter and retain its full equality report.
3. **Final geometry and Pincheck.** Rerun the 8x4 boundary/pin readback and the
   unchanged official Pincheck on final views. The G0 probe result is not a
   final routed result. Confirm the same official DEF and allocation identity.
4. **Official nine checks.** Use the unchanged support snapshot at
   `d66cf179e7bc4d296362ab7e2e3b344dc3c4f665`, adding its exact official 8x4
   DEF to the staged support payload. Stage `info.yaml` with `tiles: 8x4` and
   correct top. The applicable ordered set is: pin-label drawing overlap;
   SG13CMOS5L DRC; zero area; KLayout checks; Pincheck; boundary; layer;
   cell names; analog pins. All nine must actually execute. Preserve failed,
   unsupported or skipped outcomes. The historical coordinator writes 6x4
   metadata and must not be called as the new packaging function.
5. **Independent physical obligations.** Official precheck omits timing,
   transistor LVS, antenna and CMOS5L Verilog/LEF power-pin checking. Require
   fresh full-deck antenna results, meaningful transistor LVS with complete
   used-cell reference, GDS DRC, overlap/disconnected-pin results, actual
   geometric supply connectivity and final view consistency. Logical power
   names and a successful Pincheck do not establish all supply connections.
6. **Timing and model scope.** Bind extraction model, corner definitions,
   extractor/SPEF units and complete annotation to the final database. Require
   fresh setup/hold/slew/capacitance/fanout observations at the declared corners.
   GRT nominal estimates, stale carried fast/slow metrics and nonfinite diagnostic
   observations do not establish final timing. CMOS5L model qualification remains
   an independent gate even when extraction exits zero.
7. **Proof and public behavior.** Complete the actual final-netlist proof,
   whole-proof/private controls, full implemented-state and public-output
   coverage, and separate public-wire regressions against this target. The
   unchanged prephysical logic certificate does not certify physical repairs.

Preserve inherited `RUN_EQY=false`, `RUN_KLAYOUT_XOR=false` and
`RUN_LINTER=false` as explicit disabled checks. Scheduled flow order is not
evidence that those checks ran. Where final equivalence or view consistency
is required, supply independently executed evidence rather than calling a
skipped step successful.

The HOST-only `scripts/streaming_8x4_signoff_plan.py` prepares a target-bound
inventory and execution requests. It launches nothing. Each native request
needs its own Root GO, frozen inputs, bounded owned container, shared heavy
lease and actual cleanup/closeout. Suggested fixed-target caps are 300 seconds
for view export, 900 seconds for the complete official precheck, and 900 seconds
per antenna/LVS execution, subject to the remaining approved budget. Stop heavy
work by 08:00:35 UTC and all owned work by 09:00:35 UTC on October 23.

No failed gate is waived to meet the clock. Record unresolved obligations and
their exact artifacts in the morning report.
