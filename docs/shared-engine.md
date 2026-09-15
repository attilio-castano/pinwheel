# Shared engine design from UART and SPI

Design record: **2026-09-13**. This document preserves the requirements and design
choices of the original timed Action/Halt engine. [The engine model](engine-model.md)
owns exact semantics, proofs, and executable evidence; [research status](research/status.md)
owns current priorities. Later reactive and hardware implementations retain their
own contracts and evidence.

The [UART model](uart-model.md) and [SPI model](spi-model.md) supplied two concrete contracts for designing the engine. Both now execute as reloadable programs on one unchanged Lean machine. The original protocol specifications and controllers remain references, and the compiler proofs connect engine execution to the independent specifications through those verified controllers.

## What the experiments require

| Observation | Engine requirement | Hardware question it exposes |
| --- | --- | --- |
| UART holds ten successive symbols for an exact duration. | Bounded positive-duration actions, with no extra cycle between actions. | Can instruction fetch/decode sustain consecutive one-cycle actions? |
| SPI controls chip select, clock, and data together. | Update a bounded output-pin vector atomically at an action boundary. | Which registers change on the same system edge? |
| SPI samples MISO on eight specific rising edges. | An action may capture an input from the boundary's input snapshot while updating outputs. | How does the physical input path correspond to that digital sampling convention? |
| SPI transmits and receives independently. | Bounded receive storage; outgoing levels cannot depend accidentally on received data. | Register organization and input/output timing paths. |
| SPI has a final low-clock hold before completion. | Completion occurs after the last action's full duration. | How does halt avoid an early valid indication or chip-select release? |
| Both protocols ignore busy requests and prioritize reset. | One explicit request/reset/halt contract. | Reset priority, safe idle levels, and output-enable behavior. |
| A fabricated engine must accept new protocol programs. | Writable bounded program storage, replaced only while halted in the first model. | Loading interface, storage capacity, and area. |

The current proofs establish digital behavior of the fixed controllers and their compiled programs on the shared engine. They do not establish a minimum instruction set, efficient silicon, or a universal protocol engine.

## Selected first instruction model

The original typed instruction model has the following operations; the later [hardware baseline](hardware-baseline.md) defines their 16-bit encoding:

```text
Action(levels, duration, capture?)
Halt

capture? = none | receive slot
```

`levels` is a complete bounded output vector. `duration` is 1–256 system cycles, matching both experiments. The initial instance has one input, so a capture names only one of eight receive slots; input-pin selection is unnecessary for this instance. The program has a configured idle-output vector, needed because UART idles high while the SPI clock idles low. These are logical pin assignments; no package-pin allocation is selected.

On entry to an action, update all output levels and, if requested, write the selected receive slot from the input snapshot at that edge. Hold those levels for exactly `duration` following intervals. At the end of the duration, enter the next instruction on that same edge. `Halt` restores the configured idle outputs, clears busy, and exposes the completed receive storage. There is no implicit fetch or decode interval in these semantics. A later hardware design must implement that promise or explicitly revise it and recheck the protocol claims.

Acceptance enters the first instruction at elapsed cycle zero, clearing receive storage before any entry capture. Reset aborts execution, clears receive storage and valid, and restores the configured idle outputs. Busy requests are ignored, including on the completion edge. A halted machine retains its completed result until reset, a new accepted start, or an explicit program replacement. Atomic loading while stopped replaces the program, clears execution/results, and immediately applies its idle profile. Loading while busy is rejected without changing the machine. See the engine contract for fault and empty-program behavior.

An explicit receive-slot destination avoids introducing a general register file or arithmetic instructions before they are needed. A full output vector is sufficient for these single-program examples; output masks and concurrent independent programs remain separate design choices.

## Compile two concrete programs

- **UART 8N1:** ten actions, one for each start/data/stop symbol, each lasting `B` cycles, followed by `Halt`. No input captures. Completion remains at `10B`.
- **SPI mode 0:** seventeen actions, each lasting `H` cycles, followed by `Halt`. The eight odd-numbered phases capture MISO into slots 0–7 as SCLK rises. The final action holds SCLK low with chip select asserted. Completion remains at `17H`.

The typed compilers expand an outgoing byte into literal output levels. This demonstrates timing and reloadability with a very small machine. It also means changing the transmitted byte changes the program; the payload-reuse alternatives are evaluated in the later studies linked below. UART uses 11 instructions including halt, SPI 18, in a shared 32-slot store. The encoded instruction bank contains 512 bits, excluding execution state and any future upload staging.

## Acceptance and implementation ownership

The original milestone required exact action duration, entry-edge capture, defined
halt/fault behavior, compiler correspondence for arbitrary sampled input histories,
and UART → SPI → UART reloadability on one unchanged engine. Its completed checks
are recorded in [engine-model.md](engine-model.md). The [processor verification gates](processor-verification.md)
cover subsequent circuit, translation, loading, and physical obligations.

Implemented module ownership, consistent with [architecture.md](architecture.md): `Engine/ISA.lean` owns typed instructions and finite program storage, `Engine/Step.lean` owns execution/loading, `Engine/Proofs.lean` owns general timing and interface proofs, and `Compile/UART.lean` and `Compile/SPI.lean` own protocol compilation and refinement proofs. `test/Engine.lean` covers reloadability and execution. A separate shared trace module remains unnecessary for these proofs.

## Lessons carried into later protocols

The original fixed schedule cannot wait for an observed SCL release or branch on
an ACK. The [I²C reference](i2c-model.md) exposed the need to separate drive commands
from observed levels, start a high timer only after SCL is observed high, and use
an explicitly timed SDA capture in control flow. These are requirements learned
from a protocol, not reasons to copy the reference controller's phases into a
permanent instruction set.

The [reactive engine](reactive-engine.md) and [compiled I²C](compiled-i2c.md) records
own the implemented extension and its compatibility/correspondence proofs.
[Counted loops](looped-i2c.md), [binary images](binary-images.md), and
[storage experiments](storage-study.md) own the subsequent payload-reuse and cost
comparisons. Those studies supersede the original proposal to investigate these
features; [research results](research/results.md) records their conclusions.

The durable lesson is to let protocol timing and observation requirements expose
machine-model gaps before adding abstractions. Keep simple reference controllers
and exact compiler correspondence while measuring each hardware realization.
Even for SPI, generated-clock propagation and peripheral setup/hold requirements
remain physical obligations. Edge-indexed digital input histories do not establish
pin-level electrical behavior or routed timing.
