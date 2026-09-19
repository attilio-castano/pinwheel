# Research status

Updated 2026-09-19 during local PR preparation. This is the current decision
brief; [results](results.md) owns completed conclusions and [journal](journal.md)
owns the dated evidence trail. The [submission plan](../submission-plan.md)
records the work and acceptance criteria behind the next steps below.

## Objective and current belief

Build a reloadable protocol engine whose implementation preserves specified pin
timing, input capture, branching, and atomic program replacement, then establish
physical feasibility under the [competition constraints](../competition.md).
Lean remains the specification and proof foundation; emitted RTL and physical
implementation each need their own evidence.

**Advance the experimental one-port organization.** Its command-split core
completed one routed run on the 6×4 die area at 69.3% utilization, with setup and
hold met at all three extracted corners and slow setup +0.602 ns. DRC, LVS and
antenna checks passed; 5 slew and 15 fanout violations remain. This is core
engineering evidence, not a validated whole chip or a qualified frequency.
The [routed record](../memory-abstraction.md#the-command-split-backends-routed)
and [manifest](../../physical/experiments/oneport-split-physical-results.json)
own the exact boundary and receipts. The legacy dense cached emitter remains
the default; no experimental backend has been promoted.

The one-port refinement requires ready program words. The current compiler
proves that condition for UART/SPI transmission and for I²C writes/reads with
phases of at least two cycles. **The compiled UART receiver fails it.** A
readiness admission filter is proved as a model transformation but is absent
from emitted hardware. Both a compatible receiver and an enforced acceptance
rule are required for the candidate's supported program contract.

The [whole chip](../whole-chip.md) is a Lean netlist containing the Tiny Tapeout
pin map, two-register samplers, three-pin serial loader, and a proved core. A
host upload commits a fitting program with the engine stopped; later execution
follows the reference machine under the stated rules. The chip has been emitted
and mapped, but its RTL has no independent serial-driver simulation, gate
equivalence, or routed result.

**The chip has no defined host result-readback transaction.**
The output map exposes status and protocol levels/enables, not the 16 capture
bits. Result transfer and ownership across consume/reset/program replacement
must be specified before calling UART reception or SPI/I²C reads usable from a
host. This is broader than the previously listed missing serial status readback.

## Evidence and boundaries

| Layer | Established | Remaining boundary |
| --- | --- | --- |
| Protocols and compilers | UART, SPI, I²C models and compiler correspondence; input-latency contracts; I²C STOP now qualifies bus-free time | One-port-compatible UART RX; declared supported rates and lifecycle/result ownership |
| Memory and fetch policies | Generic memory/latency contracts and one-, two-, and three-port refinements; command/data dependency separation | One-port admission not emitted; SRAM's actual collision, enable, and dependent-read schedule unvalidated |
| Translation | Actual RTL read-back for the composed baseline; equivalence and independent regressions for recorded core variants | New chip RTL has not inherited a read-back or independent simulation claim |
| Core physical result | One-port command-split run meets setup/hold and completes layout checks | Electrical violations, repeatability, real chip pin template and changed interface |
| Whole-chip model | Serial session delivery, committed image, subsequent execution and pin-map composition | Host result transfer, independent chip RTL checks, board/electrical assumptions and physical closure |

The fresh `pr-review-20260919` foundation gate audited 183 modules, 13,322
declarations and 6,873 theorems with standard axioms only, and passed 30 suites
from a clean source snapshot. All 250 recorded inputs match the current working
tree. These include generated declarations; counts are not counts of handwritten
proofs. The [validation guide](../validation.md) defines current local checks;
the [journal](journal.md#2026-09-19-local-branch-review-and-submission-plan) records
the validation scope and receipt location.

Earlier results remain in their owners: [hardware closure](../hardware-closure.md),
[bank selection](../bank-selection-study.md), [cache enables](../cache-enable-study.md),
[flow correlation](../physical-correlation-study.md), [pin sampling](../pin-sampler-study.md),
[structural timing](../structural-timing.md), [register enables](../register-enables.md),
[input latency](../input-latency.md), and [memory/fetch organization](../memory-abstraction.md).
Historical next-step proposals in those records are not the current allocation.

## The official outline (2026-09-18)

The announcement's maximum is **6×4 tiles**; 8×4 remains a possibility. The
[competition brief](../competition.md#the-outline-and-the-pinned-files) records
the checked source and pinned template.

Every routed core used the official 1,289.28 × 710.64 µm die area and
902,417 µm² core area. None applied `tt_block_6x4_pgvdd.def`: its 43 Metal4 pins
sit in the top-left corner, whereas the core's roughly 200 stand-in ports were
spread around the edge. The template is available, but applying and validating
it requires chip-specific flow configuration and timing constraints.

The two-port run timed out after 150 minutes, at 75.2% utilization, before
detailed routing; there is no extracted timing. This supports deferring that
candidate under the tested flow and budget. It does not prove an absolute
utilization cutoff or that two ports cannot fit. The old 8×4/56% estimate is
inapplicable. Whole-chip one-port mapped area is 0.8% above its test-boundary
core; that estimate does not predict its routed area or routability.

## Next discriminators

1. **Close the one-port program contract in Lean.** Build a UART receiver that
   passes readiness and re-prove its timing/link bounds. Realize the rejecting
   filter in the chip and prove accepted/rejected uploads against the reference.
   A filter alone cannot make the existing UART receiver supported.
2. **Define and implement host result transfer.** Specify capture visibility,
   acknowledgement/consumption, overflow, reset and program replacement, then
   prove the output path. Include observable command rejection and the existing
   continuous-receiver supervisor's lifecycle.
3. **Check the resulting emitted chip independently.** Use an external serial
   driver, the reference oracle and corruption cases; establish RTL/generic-gate
   equivalence with explicit initialization and storage-X handling. Validate
   the final interface before relying on physical measurements of it.
4. **Prepare the real physical boundary, then allocate a run.** Add the
   `tt_um_pinwheel` configuration, chip-port SDC, official DEF template, and
   chip-aware regression/reporting. Require a fresh allocation specifying
   time, memory, CPUs and stop conditions before any physical run. Accept only
   evidence for the actual chip artifact and its declared constraints.

The [submission plan](../submission-plan.md) gives the required tool changes and
completion gates, including host demonstration and submission packaging.
Screen structural changes with `check-structure.py` before mapping/routing.
Pin-sampling latency remains part of protocol bounds: SPI requires
`d + tco ≤ halfCycles`; I²C requires `d ≤ phaseCycles` and `d < waitCycles` under
the tested contract. Digital two-edge delay is not an analog detection bound.

## Deferred questions

SRAM and address-path rewrites remain possible follow-ups, not prerequisites
for merging the current proofs and experiment records. SRAM targets the large
flip-flop area, but the real macro must meet the dependent map/dictionary read
schedule and collision contract. Repeatability, technology-mapped sequential
equivalence, alternative gating plans and cache-enable experiments retain
separate acceptance gates and run allocations.

Current local PR preparation covers review, bounded fixes, documentation and
local validation. It authorizes no new physical run, backend promotion, push,
PR creation or submission. Historical cumulative physical resource use remains
unrecorded.
