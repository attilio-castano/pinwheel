# Design A: detailed layout and extracted timing

On 2026-09-26, the first full-flow attempt under the
[complete design iteration plan](../research/complete-design-iteration.md)
completed detailed routing, extraction and downstream checks. **The routed
layout passes antenna, connectivity, LVS and a matched full-rule Magic DRC
replay. It fails extracted timing and electrical limits.** The fast cell/SRAM
temperature mismatch independently prevents all-corner qualification.

The [acceptance audit](../research/design-iteration-acceptance.md) freezes the
starting contract. This study owns the new physical measurements; the
[image certificate](../storage/paired-image-certificate.md) and
[host workflow](../host-workflow.md) own their separate formal and behavioral
results. All run-local evidence is under
`build/validation/design-iteration-01/`.

## First full attempt

`route-run-receipt.json` records a 2,122.352-second continuation from the exact
`route-import-fix-01/candidate/repaired.odb`. The initial metrics were empty.
The die, I/O assumptions and 20 ns clock were unchanged. Detailed routing adds
151 antenna cells; fill insertion adds 46,659 power-only fill/decap cells.

| Check | Measured result |
| --- | --- |
| Detailed router DRC | Zero final errors despite the starting 25 coarse overflow units |
| Antenna | Zero violating nets/pins |
| Critical disconnected pins | Zero; eight unused package inputs remain listed separately |
| Netgen LVS | Circuits match uniquely: 11,562 devices and 11,483 nets on each side; zero errors |
| Power continuity | Both VPWR and VGND shapes connected |
| Full Magic DRC, default import | 230,225 markers, all inside the SRAM rectangle |
| Full Magic DRC, flat-import control | **Zero**, same GDS and rules; see below |
| Extracted slow setup | **−3.190857 ns**, 11 failing endpoints; register-to-register worst −0.652731 ns |
| Extracted fast-screen hold | +0.151234 ns; mixed-temperature qualification remains open |
| Maximum cap / slew / fanout violations across corners | **34 / 94 / 66** |
| Functional cell and macro area | 362,419.86 µm², including 821.923 µm² of added antenna cells |

The full-flow exit remains failed: its default hierarchical Magic invocation
failed and extracted timing failed. The separate matched DRC control resolves
the former without rewriting that receipt. Disabled KLayout DRC/XOR and
whole-flow EQY do not count as passes. Power continuity and a small typical
estimated voltage drop do not establish board-level power integrity; voltage
source placement was not explicitly qualified in this run.

## Why Magic initially reported 230,225 markers

`drc-classification.json` binds the baseline report and its seven error classes.
Every marker lies within `[252, 144, 1036.48, 335.34]` µm, the SRAM rectangle.
The dominant classes are 122,880 Metal2 minimum-area markers and 103,368 layer
overlap markers. Marker count is not a count of independent manufacturing
defects.

The first diagnostic control changed only `MAGIC_GDS_FLATGLOB` to `["*"]`
for import of the **same final GDS** into Magic 8.3.674. It retained full DRC,
the pinned PDK, and all macro polygons; no blackboxing, rule waiver or geometry
edit was introduced. It completed in **54.520 seconds with zero errors**.
`drc-flat-request.json`, `drc-flat-receipt.json` and `drc-flat/report.json`
retain the exact configuration, input identity and result. The GDS SHA-256 is
`b303011a054439cc3e905ff5b438f7d95b9e822f48d4f672d487b7f33cbba30c`.

This matched result identifies an import-hierarchy artifact for this layout.
It supports flat import in future runs under this pinned deck; it does not
prove that every macro, PDK revision or DRC tool is interchangeable.
This is a layout-checker import setting, not a change to RTL module hierarchy.

## Why estimated timing did not survive extraction

All 11 slow setup failures start at `_12259_/Q`, the controller's mode bit 2.
`extraction-comparison.json` compares seven nets on the failed status/decode
path. Their extracted wire capacitance is **1.65–2.06 times** the coarse
estimate, although detailed/coarse wire length is only **0.852–1.011 times**.
None of these seven nets gained an antenna cell. Coupling accounts for roughly
42–60% of their extracted wire capacitance. Wire detour and added antenna loads
therefore do not explain the main discrepancy on this path.

The existing `scripts/fit-wire-rc.py` fits 4,110 routed signal nets of at least
20 µm. `wire-rc-fit.json` records the measured per-layer capacitance:

| Layer | Nominal estimate, pF/µm | Fitted value, pF/µm |
| --- | ---: | ---: |
| Metal2 | 0.000093020 | 0.000161661 |
| Metal3 | 0.000092000 | 0.000201863 |
| Metal4 | 0.000091788 | 0.000136639 |

The capacitance fit has R² = 0.993218. The selected path lengths independently
match the existing DEF parser (`wire-fit-reconciliation.json`). Nominal wire
resistance is retained for repair. This reuses the earlier
[estimate/extraction study](../physical-correlation-study.md); it is a
chip-specific optimization model, **not** a replacement for final extraction
or a qualified RC corner.

## Bounded repair screens and the next design question

The first calibrated screen stopped after 67.185 seconds: native electrical
repair tried to insert a buffer at protected hold cell `hold1989/A` and raised
`RSZ-3006`. Its failed exit and partial work are retained; it produced no
admissible candidate. A matched control skips protected input nets during that
electrical repair while keeping the established hold-repair adapter.

The third and final configuration lets signal inputs of fixed state, hold and
macro cells be buffered, retains protected clock drivers/nets, and gives setup
repair ten passes. Both completed candidates undergo independent actual-netlist
readback, all-corner function comparison, buffer contraction and geometry/power
checks. Those checks pass. Every original state/hold/macro cell remains fixed;
clock topology and power binding remain unchanged. This does not claim that all
signal placement or routing is unchanged.

| Fresh calibrated coarse screen | Protected input nets | Editable signal inputs |
| --- | ---: | ---: |
| Added buffers/delay cells / resized gates | 284 / 3 | 305 / 6 |
| Functional area, µm² | 367,832.2176 | 368,178.7680 |
| Added area relative to routed A, µm² | 5,412.3552 | 5,758.9056 |
| Slow setup / fast-screen hold, ns | −2.632147 / +0.161329 | −2.571731 / +0.155004 |
| Slow cap / slew / fanout violations | 1 / 9 / 2 | 0 / 4 / 0 |
| Reported coarse overflow | 201 | 202 |
| Repair screen time, seconds | 114.569 | 110.074 |

`calibrated-timing*/report.json` uses fresh explicit corners and verifies global
route estimates and propagated clocks. Default typical-corner STA alone would
have shown positive setup and missed the real failure. Temporary missing-route
warnings during repair are not accepted as final timing; the subsequent saved
checkpoint checks report zero partially unannotated drivers. These are fitted
coarse estimates, not second extracted results. Neither candidate qualifies for
the remaining A full-flow attempt. The three-configuration allocation is now
exhausted, counting the retained baseline and these two completed alternatives.

The last candidate's worst path reaches **`uo_out[4]`, the live command-rejection
status bit**, from SRAM output `A_DOUT[53]`. The calibrated path has 1.329 ns of
clock arrival, 6.465 ns of SRAM clock-to-Q and 10.578 ns of downstream logic/wire
delay: arrival at 18.372 ns misses the 15.800 ns requirement. Internal
register-to-register setup on this candidate is positive; the output path and
four slew violations still fail the unchanged contract.

`rejection-cone-diagnosis.json` records the source-level hypothesis. The
controller shares a parameter lookup between execution and upload validation.
That sharing connects SRAM successor selection structurally to rejection.
Yet accepting a command implies the engine is not busy, while non-busy entry
selects the boot token instead of SRAM Q. This suggests rejection can use a
separate validation-only lookup without changing any observed edge.

**Discriminator selected at this phase's close:** prove the specialized validation calculation equivalent
to the current transition/output functions, including malformed uploads, and
then check that synthesis removes SRAM Q from the rejection cone. This is an
architectural hypothesis, not a proved false path or an implemented change.
Do not add a timing exception or extra execution cycle. A later physical
allocation should test that specific change instead of another buffer sweep.

The subsequent approved [validation-isolation experiment](validation-isolation-experiment.md)
implements and checks that architectural hypothesis. Its new physical screen
has a separate source lineage and remains unaccepted; it does not revise this
phase's results or use its routed evidence for the new circuit.

## Final-netlist behavior and validation

`post-route-check-02/report.json` independently reads the final fill-stage
netlist. All original signal connections match the retained source after
accounting for 151 input-only antenna cells and 46,659 cells with no signal
terminals. The actual final netlist passes **331,401 external-pin edges and
1,517 serial frames** under pinned functional cell/SRAM models. This is finite
functional evidence without SDF, not a universal proof or timing simulation.
The first checker attempt expected antenna additions only and failed on the
fill census; its readback and failed receipt remain separate from the corrected
explicit fill/decap check.

The paired host additionally passes eight kernel-certified canonical uploads on
RTL identical to A. The portable image gate passes six positive and ten
kernel-proved rejection cases. The foundation gate passes 32 executable suites
and audits 15,471 declarations / 7,733 theorems with standard axioms only.
The Python suite passes 510 tests, with two skips. The campaign
[manifest](../../physical/experiments/design-iteration-results.json) binds these
receipts and the resource ledger.

The campaign charges **2,640.603 seconds (44.01 minutes)** against its eight-hour
CAD budget, conservatively counting the entire host demonstration including its
Lean work. One of four total full-flow attempts, and one of the two reserved for
A, has been used. All owned CAD containers are absent. Remaining time does not
override the three-configuration decision limit or make a failed screen pass.

## Reproduction and evidence boundaries

The audit and recipes bind the prepared design in worktree `33a5`, the pinned
PDK/tools in `fc40`, and the retained checkpoint in this checkout. Run-local
`route-launch.py`/`route-worker.py` and the matched DRC launch/worker preserve
bounded isolated commands, source hashes, logs, failed exits and container
cleanup. Replaying these requires those declared inputs or their exact restored
copies; it is not yet a clean-source physical build.

The first route consumes one of the two allowed A full-flow attempts. A new
attempt must be justified by an independently checked repair, retain the same
timing contract, and use final extraction for acceptance. Successful routing,
DRC and LVS do not establish the missing timed-controller refinement or remove
the mixed-temperature corner blocker. B's 64-record capacity iteration remains
behind acceptance of reference A.
