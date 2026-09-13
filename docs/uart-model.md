# Pure Lean UART experiment

Implemented and checked: **2026-09-13**, Lean 4.33.1.

This completes the specification and executable-model portion of [stage 1](uart-experiment.md#stage-1-fixed-uart-transmitter). It produces Lean pin traces and checked theorems. RTL generation, RTL simulation, synthesis, and physical timing remain unimplemented.

## Interface contract

- One synchronous clock; inputs are sampled at rising edges. The output describes the interval immediately following each edge.
- `Config.durationMinusOne : Fin 256` selects a fixed duration of 1 through 256 clock cycles per symbol. Configuration is a parameter of the model, not an input changed during execution. No physical frequency or baud rate is selected.
- An idle transmitter drives high and reports `busy = false`. A request carries an eight-bit byte and is accepted only when idle before the edge.
- Acceptance captures the byte and starts the low start-bit interval immediately after that edge. This is elapsed cycle zero, with `busy = true`.
- The frame contains one start bit, eight data bits in least-significant-bit-first order, and one high stop bit, with no parity. Each symbol lasts exactly the configured duration.
- Reset is synchronous and active-high. At the sampling edge it aborts any transmission, drives high, clears busy, and overrides any simultaneous request. The waveform theorem assumes no reset during its quiet execution; abort behavior has a separate theorem.
- Requests while busy are ignored, including on the edge ending the stop interval. They do not overwrite the captured byte or queue a transmission.
- Completion is the falling of `busy` after exactly `10 * cyclesPerBit` intervals; there is no separate done pulse. A new request can be accepted on the following edge. Thus this first interface permits one idle cycle between immediately restarted frames, rather than accepting a new byte on the completion edge.

## Specification and implementation

[Spec.lean](../Pinwheel/UART/Spec.lean) defines the frame as an explicit array of ten Boolean levels. `expected` selects the symbol by elapsed cycle divided by duration and returns high after the frame.

[Tx.lean](../Pinwheel/UART/Tx.lean) defines an idle/active machine. Active state contains a captured byte, a `Fin 10` symbol index, and a bounded intra-symbol counter. The transition increments the counter, rolls over to the next symbol, or becomes idle after the final stop interval. Its pin selection uses start/stop tests and direct byte-bit selection; it does not call the specification's frame constructor.

`run` executes quiet transitions after acceptance. `quiet_step` connects these transitions to `step` with reset low and no request. Separate interface theorems cover reset, start acceptance, ignored busy requests, and restart. No correctness claim is made for an arbitrary reset/request history as though it were one uninterrupted frame.

The `Represents` invariant connects the two counters to elapsed time. The key step proof establishes preservation through every counter and symbol rollover. Finite counter types prevent out-of-range states; this does not yet choose their RTL encoding or demonstrate a hardware implementation.

## Checked claims

| Theorem | Claim |
| --- | --- |
| `waveform_correct` | Every byte, every supported duration, and every elapsed cycle of quiet execution matches the independent specification. |
| `symbol_interval` | Every cycle within a symbol's interval has that symbol's specified level. |
| `busy_exact` | Busy is true precisely during the ten symbol intervals, with no early completion. |
| `run_complete` | Quiet execution is idle at and after the exact frame boundary. |
| `cycles_bounds` | Bit duration is positive and at most 256 cycles. |
| `reset_dominates`, `start_accepted`, `busy_request_ignored` | The sampled-input contract holds for the specified states and inputs. |
| `restart_after_completion` | The first request after completion captures the next byte. |

The main waveform, interval, busy, completion, restart, and range proofs depend on the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. The inspected reset and ignored-request proofs depend only on `propext`. No inspected proof depends on `sorryAx` or a project-defined axiom, and no source contains unfinished proofs. These are symbolic proofs over the supported parameters, not conclusions inferred from a sample of executions.

## Run the experiment

From the repository root, with the [development environment](development.md) available:

```sh
lake build
lake env lean -DwarningAsError=true --run test/UART.lean
```

The executable checks all 256 bytes at durations 1, 4, and 256: 768 frames total. At every checked cycle it compares the model pin with the independent specification, checks exact busy timing and reset priority, and checks that busy requests are ignored. It also checks restart after each frame. These checks exercise the executable code and boundary examples alongside the universal proofs.

The script writes `build/uart/0x53-4cycles.csv`, with `cycle`, `tx`, and `busy` columns. It includes 40 frame cycles and two idle cycles. Each row describes one interval after an edge, not a physical measurement.

| Cycles | Symbol | TX |
| --- | --- | --- |
| 0–3 | Start | 0 |
| 4–7 | Data 0 | 1 |
| 8–11 | Data 1 | 1 |
| 12–15 | Data 2 | 0 |
| 16–19 | Data 3 | 0 |
| 20–23 | Data 4 | 1 |
| 24–27 | Data 5 | 0 |
| 28–31 | Data 6 | 1 |
| 32–35 | Data 7 | 0 |
| 36–39 | Stop | 1 |
| 40–41 | Idle | 1 |

Busy is true for cycles 0–39 and false thereafter. Adjacent equal symbols do not create an edge on the pin; their durations are defined by the clock intervals.

To inspect proof dependencies, place `import Pinwheel` and `#print axioms Pinwheel.UART.waveform_correct` in a scratch Lean file and run it with `lake env lean -DwarningAsError=true`. Generated files belong under the ignored `build/` directory.
