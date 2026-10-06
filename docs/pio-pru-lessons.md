# Lessons from RP2040 PIO and TI PRU

Research note, **2026-09-22**. Primary sources were reviewed on this date.
This records architectural lessons and a proposed future comparison. It does
not select a new ISA, change Pinwheel's timing contract, or allocate another
physical run. [Research status](research/status.md) owns the active work queue.

**Follow-up:** the [bounded comparison](storage/compact-execution-study.md) rejected the
first encoding's lost capacity and operations. The
[revised organization](storage/compact-execution-study.md#full-capacity-follow-up) restores
both with a larger SRAM and banked parameter tables. Its
[complete experimental controller](storage/compact-execution-study.md#complete-controller-and-macro-timing)
now saves 22.88% of total mapped area after signal load repair, with positive
setup but unresolved hold before wires. This justifies a bounded physical
comparison while retaining the existing chip as control. The proposal below
records the motivation, not a selected ISA.

## Why these references matter

The [Jane Street competition announcement](https://blog.janestreet.com/protocol-emulator-asic-competition/)
asks for programmability that supports new protocols after fabrication within
the chip's timing and I/O limits, and points to PIO and PRU as inspiration.
Our interpretation is that physical timing should help determine the execution
model: flexibility can come from carefully selected operations, storage and
pin access, with compilation doing the remaining work.

| Design | Mechanism | Question it raises for Pinwheel |
| --- | --- | --- |
| RP2040 PIO | Nine instruction types, 16-bit instructions, a 32-slot program store shared by four state machines per PIO block, shift registers and FIFOs; explicit waits/delays and concurrent pin updates through side-set | Which small operations provide the protocol flexibility we need? |
| TI PRU | A simple processor with dedicated instruction/data memory and direct pin access through R30/R31; memory latency depends on the access and contention | Which state and communication must be local for predictable execution? |
| Pinwheel | Timed actions combine capture, branching, successor entry and preparation of later SRAM requests | Which parts must happen at one boundary, and which can be prepared earlier? |

Sources: [RP2040 datasheet, chapter 3](https://datasheets.raspberrypi.com/rp2040/rp2040-datasheet.pdf#page=312),
[TI PRU hardware overview](https://software-dl.ti.com/public/hpmp/sitara/building_blocks_for_pru_dev_m1_hardware/presentation_content/external_files/PRU_Building_Blocks_M1_Hardware.pdf),
and the [Pinwheel fetch contract](fetch-contract-study.md#availability-and-deadlines-in-the-existing-loop).
PRU capabilities vary by device. These references do not supply comparable
area, clock frequency or routing results for Pinwheel's process and allocation.

## The most direct PIO lesson: preparation has a deadline

PIO can refill its output shift register while the last bits of the preceding
word leave. It cannot refill an empty register and output from it in the same
cycle: the datasheet identifies the resulting long logic path. The schedule
therefore distinguishes independent work that can overlap from dependent work
that requires time. See [§3.5.4.2](https://datasheets.raspberrypi.com/rp2040/rp2040-datasheet.pdf#page=340).

For Pinwheel, distinguish operations that must be simultaneous at the pins from
preparation that merely must finish before those events. The current execution
loop can use a captured input to select the word being entered, then use that
word to determine the next pair of memory requests. Consecutive one-cycle
branches leave no spare edge for an extra register. The existing
[fetch-dependency analysis](fetch-contract-study.md#what-the-dependency-proofs-establish)
is the starting point for checking that constraint.

A pipeline proposal must state when each input becomes available, when its
result is required, and what happens if it is late. Preserving an external pin
trace does not necessarily require identical internal registers, but it does
require the same observation times and reactions under the stated assumptions.
Splitting a dependent operation across edges needs a refinement argument or an
explicitly different contract. It cannot be called a transparent timing repair.

## Keep protocol code resident and supply payload separately

PIO transfers payload through FIFOs and shift registers while executing a
resident program. That separation suggests a useful Pinwheel workload: one UART
program should transmit successive byte values without reuploading its code.
[PIO programmer's model](https://datasheets.raspberrypi.com/rp2040/rp2040-datasheet.pdf#page=313)

The existing [resident-payload proposal](host-workflow.md#bounded-resident-payload-proposal-2026-09-19)
already specifies a small candidate: snapshot the accepted START payload and
shift once per instruction entry. It remains a proposal, including its current
physical-budget gate. Reuse that specification rather than create a second
payload mechanism here. Its tests must distinguish entry from hold, protect
execution-owned data, and preserve reset, busy-start and result behavior.

Update 2026-10-06: [reusable payload programs](protocols/reusable-programs.md)
now expose that mechanism through the existing paired hardware and public
host API. Code remains resident across all 256 UART/SPI payloads. The new
source/kernel/package gates check its ownership rules; physical qualification
and universal initialized resident protocol composition remain separate.

This could reduce upload traffic and program expansion. It does not establish
a smaller chip: encoding, selection logic, registers and transport changes all
need to be costed. A FIFO is optional; the smallest useful comparison can use
the existing accepted-start transaction.

## State where waiting is permitted

TI distinguishes single-cycle non-memory PRU instructions, local memory accesses
whose latency includes possible arbitration, and external accesses whose timing
depends on the wider system. Dedicated memory and direct I/O reduce dependencies;
shared resources still require a contention model.
[TI read/write latency guidance](https://e2e.ti.com/support/processors-group/processors/f/processors-forum/1625250/faq-pru-read-write-latencies?ReplyFilter=Answers&ReplySortBy=Answers&ReplySortOrder=Descending%29)

For Pinwheel, an idle transmitter may wait for a payload before starting a UART
frame. Once it starts, an unexpected wait must not extend a bit. An I²C wait for
observed clock release has different semantics and a bounded timeout. These
cases need explicit rules rather than one universal assumption about stalling.

A useful component contract should name:

- the state it owns and the event that transfers ownership;
- when operands become available and the earliest/latest allowed observations;
- resource requirements, such as SRAM ports and access priority;
- permitted waiting points, starvation behavior and timeout bounds;
- reset, cancellation and commit behavior.

Use the existing typed interfaces, observers and schedule obligations to express
these rules. Introduce another abstraction only if a concrete implementation
needs it. Lean can check the digital scheduling assumptions; physical setup,
hold, wire load and pin access still require measured evidence.

## What Pinwheel could do differently

The proposed differentiator is **formal compilation from rich protocol intent
to a compact, explicitly timed execution mechanism**. Keep protocol descriptions
and their reference traces expressive, while comparing alternative instruction
layouts or preparation schedules underneath them.

The compiler/refinement obligation should preserve output edges, capture times,
conditional reaction bounds and failure behavior for all admitted inputs.
The supported timing envelope must be explicit. In particular, a smaller engine
that cannot sustain the current one-cycle dependent branches implements a
different capability unless additional preparation or resources recover those
deadlines. Do not silently weaken existing programs' guarantees.

Physical locality must also be part of the comparison. Account for source wires,
both SRAM replicas, clock loads, hold repair and other consumers of shared
signals. A smaller instruction word or fewer logic levels alone does not prove
a cheaper placed chip. The [architecture comparison](physical/chip-architecture-study.md)
and [interface geometry study](chip-physical-study.md#sram-interface-geometry-and-upload-staging--september-22)
provide existing evidence and methods.

The experimental [upload pipeline](fetch-contract-study.md#experimental-upload-pipeline--september-22)
is a limited application: it uses flexibility in physical write timing while
preserving execution reads. It does not simplify the execution feedback loop,
and its schedule proofs and RTL checks do not establish physical benefit or
a composed full-chip refinement.

## Proposed comparison to resume later

When this question is selected in research status, compare the current timed
actions with one concrete compact execution model on these workloads:

| Workload | Required observations | Main discriminator |
| --- | --- | --- |
| Resident UART transmitter | All 256 byte values on one program; exact start/data/stop timing; defined busy-start, reset and missing-payload behavior | Benefit and full cost of separating code from payload |
| SPI transfer with changing payloads | Correct clock/data edges and capture phase; explicitly permitted waits at transaction boundaries | Cost of shifts, counters and simultaneous pin operations |
| Conditional input response | Defined sampling edge, both branch outcomes, consecutive one-cycle branches, and timeout behavior | Whether a simpler fetch/decode schedule preserves the existing reaction contract |

Begin with execution models and independent trace comparisons. Record program
bits, payload state, total register bits, memory copies/ports, required accesses
per edge and the dependency path for the worst branch. Identify any incompatible
timing cases before changing emitted hardware. Finite examples help reject
proposals; an adopted general correspondence claim needs the matching proof.

For a viable candidate, use matched synthesis and cell/macro timing as cheap
screens, with all distribution and control costs included. Admit placement and
wire analysis only for a specific locality hypothesis. Decide whether to retain
the current mechanism, implement an equivalent alternative, or propose a
separately named capability with a different timing envelope. This note itself
does not make that decision.
