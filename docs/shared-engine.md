# Shared engine design from UART and SPI

Design record: **2026-09-13**. The first pure Lean engine and typed UART/SPI program compilers are implemented. The [engine model record](engine-model.md) owns exact semantics, checked proofs, and execution evidence. The later [hardware baseline](hardware-baseline.md) adds proved binary encoding, and the [countdown slice](countdown-hardware.md) has generated RTL evidence. The later [complete core](core-hardware.md) adds structural execution proofs and reloadable RTL checks. Physical loading transport remains future work.

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

The typed compilers expand an outgoing byte into literal output levels. This demonstrates timing and reloadability with a very small machine. It also means changing the transmitted byte changes the program; reusable instruction sequences with separate payload data require another design step. UART uses 11 instructions including halt, SPI 18, in a shared 32-slot store. The encoded instruction bank contains 512 bits, excluding execution state and any future upload staging.

## Implementation plan and acceptance gates

The following original plan is complete for the typed, pure Lean milestone. Its results and limits are recorded in [engine-model.md](engine-model.md); encoding and the countdown hardware gate are covered by the [hardware record](countdown-hardware.md); the later [core record](core-hardware.md) covers complete structural refinement, RTL simulation, and generic synthesis. Physical loading and implementation remain open.

1. **Specify the machine interface.** Fix bounded pin/register/program capacities for the experiment, action-entry timing, halted loading, start/reset priority, invalid-program behavior, and idle-profile changes. Use a three-output/one-input instance for the two protocol examples; keep physical pin mapping separate.
2. **Implement a finite Lean machine.** Separate loaded program/configuration from execution state. Use bounded program, duration, and receive indices. Define explicit faults for invalid encodings when an encoding exists; the typed model must still handle falling off program memory and attempted loading while busy. A rejected operation must have specified outputs and state effects.
3. **Prove timed execution.** Prove that an action runs for exactly its duration, adjacent actions have no gap, captures use the entry-edge input, and halt/reset produce their defined state. Cover duration one and the program-memory boundary.
4. **Compile UART and SPI.** Prove each compiled program matches its existing independent waveform specification. For SPI, also prove arbitrary-input receive correctness and result timing. Do not use the compiler's own action list as the only oracle.
5. **Demonstrate reloadability.** Run UART, halt, load SPI, run SPI, then reload UART on the same machine definition. Test quiet/noisy inputs, all byte values, duration bounds, reset, invalid execution, and loading requests while busy. Emit comparable CSV traces and report exact program sizes.
6. **Review the next boundary.** Record what worked, instruction/storage costs, and any timing compromises. Commit validated increments. Hardware backend integration and the I²C experiment require their own concrete plans; neither follows automatically from these two programs passing.

Implemented module ownership, consistent with [architecture.md](architecture.md): `Engine/ISA.lean` owns typed instructions and finite program storage, `Engine/Step.lean` owns execution/loading, `Engine/Proofs.lean` owns general timing and interface proofs, and `Compile/UART.lean` and `Compile/SPI.lean` own protocol compilation and refinement proofs. `test/Engine.lean` covers reloadability and execution. A separate shared trace module remains unnecessary for these proofs.

## What remains open for later protocols

The [processor verification plan](processor-verification.md) is the complementary hardware track: implement and prove the circuit that executes the current actions, with explicit encoding, memory, loading, and physical-flow obligations. Use that implementation as a measured baseline while the protocol experiments below challenge the instruction set.

The [pure Lean I²C experiment](i2c-model.md) now exercises a single-controller write, ACK/NACK, and stretching. It establishes the need to separate pin drive from observed levels, wait for observed SCL high before starting the high timer, and branch on an explicitly timed SDA capture. The current fixed schedule does not define those operations. A naïve two-phase expansion already needs 36 actions for 18 clocks before START/STOP, so program capacity and reusable payload storage also need review. Reference-controller phases are not a finalized instruction set.

The [candidate reactive engine](reactive-engine.md) implements drive/observation and wait-then-timed continuation, with a compatibility proof for every original typed program. It now also executes [compiled I²C writes](compiled-i2c.md), with qualification, guarded phases, terminal capture, ACK-dependent continuation, and reference-controller correspondence. Its 79-instruction expansion uses an experimental 128-slot bank; original programs retain a 32-slot execution limit. The original encoded core remains intact. Compare program/data storage designs before revising the encoding and structural core; compiler correspondence is now proved, while extended circuit and target-liveness proofs remain separate work.

Even for SPI, generated-clock propagation and peripheral setup/hold requirements remain a separate physical obligation. Lean's edge-indexed input history is the boundary of today's proof. RTL simulation, implementation correspondence, synthesis area, and routed timing must be reported as separate evidence.
