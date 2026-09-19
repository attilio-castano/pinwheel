# From the experimental chip to submission

Prepared 2026-09-19. [Research status](research/status.md) owns priorities; this
page owns the remaining implementation and acceptance gates. These steps are
planned work, not claims of completion or permission to start physical runs.
The current PR can preserve the proofs and experimental evidence before these
chip milestones are complete; [validation](validation.md) defines its merge gate.

## Starting point

The [whole-chip model](whole-chip.md) connects serial pins to a committed program
and subsequent reference-machine execution. The one-port core has one
command-split routed sample with +0.602 ns slow setup, passing hold and layout
checks, and remaining slew/fanout violations. The emitted whole chip has only
mapping evidence. Its input pins and core boundary differ from the routed core.

The one-port organization is the candidate for the current official 6×4 limit.
The two-port attempt timed out under the recorded flow budget. Preserve both
results; neither a new floorplan allocation nor a universal fit cutoff follows.

## Close the one-port program contract

**Exists:** generic fetch-policy refinement, `Readiness.Image`, compiler
readiness proofs for TX/SPI and sufficiently long I²C phases, and
`Admission.admit` as a proved model filter. **Missing:** a compatible UART
receiver and that filter in an emitted circuit.

1. Choose a receiver polling schedule that obeys readiness. A two-cycle poll
   is a candidate, not a proved replacement. State supported bit periods and
   re-prove start detection, data/framing capture, clock/observation-age bounds,
   and any continuous-stream composition affected by the schedule.
2. Realize the readiness predicate and rejection path in the structural chip,
   preserving capacity admission and atomic loading. Use the existing feeder
   abstraction where it fits; prove the actual circuit equals the admitted
   reference for arbitrary pushes, including later uploads.
3. Specify how a host observes rejection. The current `rejected` status is a
   command-edge indication; it is not a sticky acknowledgement protocol.

**Done when:** uploaded UART RX images are proved ready, non-ready pushes are
rejected by the emitted circuit without corrupting active/staged program state,
and the updated receiver/compiler/link tests pass with explicit timing bounds.
Rejecting the current receiver's image does not satisfy UART receive support.

## Return captured results to the host

**Exists:** 16 internal capture bits, protocol read models and compiler proofs,
status pins, and a Lean continuous-RX supervisor. **Missing:** a result-transfer
interface in `Chip.outputs` and a composed hardware lifecycle for that supervisor.

Define the smallest useful host transaction: upload, start, run a receive/read,
observe completion or error, and retrieve the exact result. Choose the pin or
serial return path and specify framing, width/order, stable result snapshot,
consume/acknowledgement, overflow, reset, stop and program replacement. Decide
the supported one-shot/continuous behavior explicitly; do not imply the Lean
supervisor's queue already exists in the chip.

Build the structural output path and prove its connection to the captured
result. Preserve protocol pin timing while the host transfers data. Include
result ownership when a reset or new program arrives before consumption.

**Done when:** UART bytes and SPI/I²C read results are observable through actual
chip ports, with proved transfer/ownership behavior and executable negative cases
for incomplete transfers, duplicate consumption, reset and replacement.

## Validate the emitted chip independently

**Exists:** `chip_emit`, core oracles, core RTL/generic-gate equivalence and
mutation checks, and a Lean host-session test. **Missing:** an independent test
of the emitted `tt_um_pinwheel` at its external ports.

Add a driver outside Lean for the specified host transactions and actual pin
map. Compare execution, status and returned results to the reference oracle.
Cover initialization from unknown RTL registers, minimum/uneven serial phases,
idle gaps, partial frames, reset during upload, malformed/over-capacity/non-ready
images, busy rejection, commit/start, replacement and pin-sampling latency.
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

**Exists:** pinned CMOS5L tools/PDK/support files and
`tt_block_6x4_pgvdd.def`, core flow scripts and recorded core constraints.
**Missing:** a chip-specific physical configuration and validation path.

Before a run:

- Add a configuration for `tt_um_pinwheel` and the official 6×4 DEF, with the
  template's ports, power nets and pin placement. Keep the existing core
  configuration as historical comparison evidence.
- Add SDC for `ui_in`, `uio_in`, `rst_n`, `ena`, outputs and output enables.
  State clock, host/protocol timing, reset and synchronizer assumptions. Existing
  `physical/core.sdc` constrains `command`, `data`, `incoming`, `init` and `reset`;
  renaming a design directory does not adapt those constraints.
- Extend preparation, execution, targeted timing and netlist regression for
  the actual chip top and ports. `--design` currently selects a core artifact
  directory; `prepare-physical.py`, the flow config and checker still assume
  the core module. `run-physical.py`'s allowed overrides do not include the
  top-level module, SDC or DEF template.
- Freeze the verified chip RTL, constraints, DEF, PDK, libraries and flow
  controls. Declare time, CPUs, RAM, stopping steps and comparison objective;
  obtain the physical-run allocation before execution.

**Done when:** the final chip routes with the official template; all declared
corners meet extracted setup/hold and electrical limits; required DRC, LVS and
antenna checks pass; and the implemented netlist passes the external-interface
regression. Record disabled/deferred checks explicitly. A timeout or missing
signoff step is partial evidence. One successful sample does not establish
repeatability or board-level electrical behavior.

## Demonstration and submission package

Use the [official template and competition brief](competition.md), rechecked
at packaging time. Set the actual tile allocation, source list, pin map and
clock information. Choose and record an open-source license; none is currently
present at the repository root. Include reproducible host upload/readback tools,
example UART/SPI/I²C transactions with declared rates/roles, tests, and a clear
account of proved behavior versus simulated and measured behavior.

Check electrical drive/release, pull-ups, voltage and reset assumptions against
the intended board. FPGA or board demonstration is a separate evidence step
if selected; passing digital models alone does not establish it. Review the
final source/artifact identities and required template checks before publication.
The announcement's submission form was still forthcoming at the last source
check; recheck it and the deadline before any submission.

**Done when:** the package can be reproduced and exercised through its documented
host interface and passes the applicable submission checks. Publishing, opening
a PR, and submitting remain distinct user-authorized actions.

## Optional architecture experiments

SRAM, address-path factoring, alternative gating plans and additional physical
repeatability studies are separate experiments. For SRAM, bind the actual
macro's read enable, masked-write/collision behavior and latency to
`Memory.spec`; account for dependent map/dictionary reads and two-bank loading.
The existing read-first abstraction and one-port schedule are not yet proofs
of that macro. Screen the complete wrapper's area and timing before allocating
a physical comparison. Do not replace this branch's historical receipts with
new experimental results.
