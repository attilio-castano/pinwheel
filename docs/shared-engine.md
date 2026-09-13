# Shared engine proposal from UART and SPI

Design record: **2026-09-13**. This is a proposal; no programmable engine, instruction encoding, assembler, or RTL is implemented.

The [UART model](uart-model.md) and [SPI model](spi-model.md) now give two concrete contracts against which to design the engine. The next useful experiment is to execute both as reloadable programs on one unchanged Lean machine. Keep the existing protocol specifications and controllers as references while proving the new program executions against the independent specifications.

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

The current proofs establish the digital behavior of the two fixed controllers. They do not establish a minimum instruction set, efficient silicon, or a universal protocol engine.

## Smallest candidate to evaluate

Start with a typed instruction model, leaving binary encoding until its semantics work:

```text
Action(levels, duration, capture?)
Halt

capture? = none | (input pin, receive slot)
```

`levels` is a complete bounded output vector. `duration` is 1–256 system cycles, matching both experiments. A capture names a bounded input pin and one of eight receive slots. The program has a configured idle-output vector, needed because UART idles high while the SPI clock idles low. These are logical pin assignments; no package-pin allocation is selected.

On entry to an action, update all output levels and, if requested, write the selected receive slot from the input snapshot at that edge. Hold those levels for exactly `duration` following intervals. At the end of the duration, enter the next instruction on that same edge. `Halt` restores the configured idle outputs, clears busy, and exposes the completed receive storage. There is no implicit fetch or decode interval in these semantics. A later hardware design must implement that promise or explicitly revise it and recheck the protocol claims.

Acceptance enters the first action at elapsed cycle zero and clears receive storage and valid. Reset aborts execution, clears receive storage and valid, and restores the configured idle outputs. Busy requests are ignored, including on the completion edge. A halted machine retains its completed result until reset, a new accepted start, or an explicit program replacement. The next specification must define program replacement as a separate operation, including whether changing the idle profile immediately changes pins; it must not leave that behavior implicit.

An explicit receive-slot destination avoids introducing a general register file or arithmetic instructions before they are needed. A full output vector is sufficient for these single-program examples; output masks and concurrent independent programs remain separate design choices.

## Compile two concrete programs

- **UART 8N1:** ten actions, one for each start/data/stop symbol, each lasting `B` cycles, followed by `Halt`. No input captures. Completion remains at `10B`.
- **SPI mode 0:** seventeen actions, each lasting `H` cycles, followed by `Halt`. The eight odd-numbered phases capture MISO into slots 0–7 as SCLK rises. The final action holds SCLK low with chip select asserted. Completion remains at `17H`.

The initial assembler can expand an outgoing byte into literal output levels. This demonstrates timing and reloadability with a very small machine. It also means changing the transmitted byte changes the program; reusable instruction sequences with separate payload data would require another design step. Record program length and storage cost rather than treating this expansion as the final architecture.

## Next implementation plan and acceptance gates

1. **Specify the machine interface.** Fix bounded pin/register/program capacities for the experiment, action-entry timing, halted loading, start/reset priority, invalid-program behavior, and idle-profile changes. Use a three-output/one-input instance for the two protocol examples; keep physical pin mapping separate.
2. **Implement a finite Lean machine.** Separate loaded program/configuration from execution state. Use bounded program, duration, and receive indices. Define explicit faults for invalid encodings when an encoding exists; the typed model must still handle falling off program memory and attempted loading while busy. A rejected operation must have specified outputs and state effects.
3. **Prove timed execution.** Prove that an action runs for exactly its duration, adjacent actions have no gap, captures use the entry-edge input, and halt/reset produce their defined state. Cover duration one and the program-memory boundary.
4. **Compile UART and SPI.** Prove each compiled program matches its existing independent waveform specification. For SPI, also prove arbitrary-input receive correctness and result timing. Do not use the compiler's own action list as the only oracle.
5. **Demonstrate reloadability.** Run UART, halt, load SPI, run SPI, then reload UART on the same machine definition. Test quiet/noisy inputs, all byte values, duration bounds, reset, invalid execution, and loading requests while busy. Emit comparable CSV traces and report exact program sizes.
6. **Review the next boundary.** Record what worked, instruction/storage costs, and any timing compromises. Commit validated increments. Hardware backend integration and the I²C experiment require their own concrete plans; neither follows automatically from these two programs passing.

Suggested module ownership, consistent with [architecture.md](architecture.md): `Engine/ISA.lean` owns typed instructions and program validity, `Engine/Step.lean` owns execution and timing proofs, and `Compile/UART.lean` and `Compile/SPI.lean` own protocol compilation and refinement proofs. Add a shared trace module only when these proofs expose useful common definitions. Add `test/Engine.lean` for the reloadability experiment. Do not create empty modules in advance.

## What remains open for later protocols

I²C should be the next deliberate challenge to this candidate: first specify the desired role and subset, then examine line drive/release behavior, observed inputs, conditional progress, and bounded waits/timeouts. The current fixed schedule does not yet define those operations. A separate I²C contract should determine which are necessary before extending the instruction set.

Even for SPI, generated-clock propagation and peripheral setup/hold requirements remain a separate physical obligation. Lean's edge-indexed input history is the boundary of today's proof. RTL simulation, implementation correspondence, synthesis area, and routed timing must be reported as separate evidence.
