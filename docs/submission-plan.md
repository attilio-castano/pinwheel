# From the experimental chip to submission

Implementation sequence recorded 2026-09-21; navigation clarified 2026-09-24.
[Research status](research/status.md) owns current priorities. This page retains
the earlier hybrid-SRAM sequence and the submission acceptance gates;
[validation](validation.md) defines the local merge gate. Dated next steps below
describe that phase and are not the current work queue.

The sequence below records the earlier hybrid-SRAM implementation. The later
paired controller is the active experimental architecture in the
[research status](research/status.md). The [integration record](branch-integration.md)
explains its correspondence and physical boundaries at consolidation. The
earlier hybrid selection below does not supersede that newer decision.

## Starting point

The [whole-chip model](whole-chip.md) connects serial pins to a committed program
and subsequent reference-machine execution. The one-port core has one
command-split routed sample with +0.602 ns slow setup, passing hold and layout
checks, and remaining slew/fanout violations. The new result-enabled chip has
its own external-pin validation path. Its input pins and boundary differ from
the routed core. Its [first SRAM physical experiment](chip-physical-study.md)
now reaches routing with the official pin template; closure remains open.

The two-port flip-flop core timed out under the recorded flow budget. The early
SRAM study makes an unrestricted two-read organization worth investigating
before tailoring UART to one port. Preserve both historical physical results;
they do not choose between the new storage organizations.

## Consolidate shared contracts and host results

**Implemented:** generic upload encoding in `Loader.ProgramImage`, separate
storage rules and compiler certificates, shared netlist/input/feeder/observer
composition, and shared validation command capture. `AdmissionNetlist` realizes
the generic word filter without reconnecting payload data to commit/start
decoding. The result-enabled one-port circuit uses its proved readiness gate.

`HostResult` provides a 16-bit retained result and outcome, paged host reads,
consumption, overflow and sticky command rejection. Its step/output proofs and
core noninterference theorem bind the structural observer to that contract.
The [version-1 interface](whole-chip.md#host-result-interface-version-1) specifies
reset, stop, replacement and simultaneous consume/arrival. UART remains one-shot
on this interface; the continuous-RX supervisor has no composed chip circuit.

**Gate:** fresh foundation audit, unchanged historical emissions for the shared
cleanup, and the independent chip checks below. Generic infrastructure can
advance before selecting the final memory implementation.

## Use the bounded SRAM study to choose storage/fetch

**Candidate selected for this phase:** [the complete-chip comparison](storage-primitives.md#complete-chip-comparison-2026-09-19)
favors hybrid dictionary SRAM with two reads. Its complete mapped chip occupies
393,558 µm², versus 479,596 for direct SRAM and 622,897 for the matched flip-flop
reference. Both SRAM prototypes pass independent external-pin and core-edge
traces, including 1,000 consecutive branches and immediate commit/start. The
selected macro/cell views match the pinned physical PDK byte for byte.

Macro-aware pre-layout STA at 20 ns gives hybrid +10.26 ns slow setup and
−0.86 ns hold, with fanout violations. Clock/hold/fanout repair, physical-view
installation and macro integration remain required. No routed fit or complete
SRAM refinement follows from the comparison. The current two-port flip-flop chip
remains the unrestricted proved reference.

## Finish the selected admission and protocol contract

Existing one-port admission enforces `SinglePort.Ready`; two ports require no
duration rule. Both retain the small dictionary's capacity check. The current
UART receiver violates the one-port rule even at a slower baud, so rejection
does not constitute receiver support.

The hybrid selected in this phase keeps the small dictionary's capacity contract
and adds no duration restriction; retain the current UART compiler and timing
contract.
The closed-loop hybrid array/controller model now refines the capacity-adapted
atomic reference after initialization, including uploaded word correspondence,
actual lookup addresses, held Q and commit/start bypass. Every controller
register matches the shared netlist. Complete package-wrapper/Verilog binding
and translation correspondence remain separate gates. Later uploads and
abort/restart are already part of the independent regression. Reopen a one-port
receiver schedule only if physical evidence changes the storage decision.

**Done when:** the emitted filter enforces the selected rule, supported compiler
images satisfy it, and protocol tests pass with explicit timing bounds. Shared
admission/result work does not depend on resolving this specialization early.

## Validate the emitted chip independently

**Implemented:** `check-chip.py` drives the emitted `tt_um_pinwheel` from an
independent serial/core/mailbox oracle, simulates RTL and generic gates, checks
their equivalence and requires a corrupted result bit to fail behaviorally.

The regression covers initialization from unknown RTL registers, minimum/uneven
serial phases, partial frames, reset during upload, malformed/over-capacity/
non-ready images, busy rejection, commit/start, replacement, result ownership,
all 16 capture bits, UART TX, SPI mode 0, a stretched I²C read and two-port UART
framing capture. The interactive [host demonstration](host-workflow.md) adds
same-chip protocol replacement and a custom captured-input trigger.
Respect the digital session contract; analog metastability remains outside it.

Retain source/MLIR/RTL/tool/oracle identities, check RTL/generic-gate equivalence
for the complete chip, and require corruption cases to fail for behavioral
reasons. Do not count a compile failure or a stale failing baseline as detection.
Make the reset and storage-definedness relation explicit; register-name matches
alone are insufficient when synthesis narrows or removes registers.

**Done when:** the final feature-complete chip passes the independent serial and
result-transfer regression, required mutations and equivalence, with a fresh
receipt binding the exact artifact. A check of today's incomplete interface may
be a useful intermediate result, but must be rerun after interface changes.

## Prepare and validate the physical chip

**Implemented:** chip-specific configuration/SDC, official 6×4 DEF, pinned macro
GDS/LEF/CDL/Liberty views, explicit array/core power connections and immutable
preparation/runner snapshots. The shared PDK stays read-only. The bounded
[physical experiment](chip-physical-study.md) records the attempted placements,
power-grid correction, hold-repair area and remaining congestion. It runs early
enough to inform the proof/storage investment.

The verified half-height placement corridor lowers global overflow 1,255→870
and Metal4 body-overlapping guides 129→45 without materially increasing area.
The full-height reservation is rejected. In the half strip's 90-minute
continuation, matched first-pass iteration-59 markers improve 126→92; the first
pass ends with 73 markers inside macros. Its antenna check finds 49 net/55 pin
violations and the budget expires during the second routing pass, after
iteration 35 with 230 markers. These passes must be reported separately.
The corridor survives both repair stages. The
[physical study](chip-physical-study.md#corridor-continuation-2026-09-21) retains
the exact geometry and comparison boundaries. Its proposed macro-body
obstruction screen was subsequently
[tested and rejected](routing-diagnostics.md#the-one-new-screen-and-its-disposition).
The later [paired physical comparison](physical-targets.md) owns the current
physical evidence. Neither phase established physical closure or backend
promotion.

**Remaining:** qualify the macro power grid and mixed-temperature fast screen,
close routing and electrical limits, then validate the implemented chip netlist
with the external-port regression. Keep each new attempt bounded and preserve
the exact inputs and failed receipts. Physical learning and adapter proof can
advance independently.

**Done when:** the final chip routes with the official template; all declared
corners meet extracted setup/hold and electrical limits; required DRC, LVS and
antenna checks pass; and the implemented netlist passes the external-interface
regression. Record disabled/deferred checks explicitly. A timeout or missing
signoff step is partial evidence. One successful sample does not establish
repeatability or board-level electrical behavior.

## Demonstration and submission package

Use the [official template and competition brief](competition.md), rechecked
at packaging time. Set the actual tile allocation, source list, pin map and
clock information. **Licensing is pending by user decision**; do not add an
implied license or describe the repository as submission-ready open source.
The reproducible host upload/readback tools and UART/SPI/I²C/custom-trigger
examples are implemented, with declared digital roles and cycle counts. Keep
proved, simulated and physically measured behavior distinct.

The demo identifies program-upload cost as the next data-flow question. Measure
repeated transfers with varying payloads before selecting data registers, shifts,
rearm or FIFO changes. Preserve a resident program and define delivery/overflow
semantics; use the physical results to bound the hardware budget.

Check electrical drive/release, pull-ups, voltage and reset assumptions against
the intended board. FPGA or board demonstration is a separate evidence step
if selected; passing digital models alone does not establish it. Review the
final source/artifact identities and required template checks before publication.
The announcement's submission form was still forthcoming at the last source
check; recheck it and the deadline before any submission.

**Done when:** the package can be reproduced and exercised through its documented
host interface and passes the applicable submission checks. Publishing, opening
a PR, and submitting remain distinct user-authorized actions.

## Other architecture experiments

Address-path factoring, alternative gating and physical repeatability remain
separate experiments. Reopen them when the selected chip's measured bottleneck
justifies the work. Preserve historical receipts when adding new results.
