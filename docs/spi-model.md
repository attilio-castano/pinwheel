# Pure Lean SPI experiment

Implemented and verified: **2026-09-13**. Pure Lean specification, finite controller, proofs, executable checks, and CSV trace are complete.

Scope: one controller, one peripheral, eight-bit full-duplex transfers, most-significant bit first, and mode 0. This is a pure Lean model. Other SPI modes, peripheral mode, multi-byte transactions under continuous chip select, RTL, and physical timing are outside this milestone.

## Interface and edge convention

- The configuration fixes a half-clock duration `H` of 1–256 system cycles. No physical frequency is selected.
- Inputs are sampled at system-clock rising edges. Output state describes the following interval. Cycle zero begins immediately after acceptance.
- Idle outputs are `CS_N=1`, `SCLK=0`, `MOSI=0`. A request carries a byte and is accepted only when idle before the edge.
- Acceptance asserts `CS_N`, presents outgoing bit 7, clears the receive slots and result-valid indication, and asserts busy.
- The eight rising SCLK edges and MISO samples occur at cycles `H, 3H, ..., 15H`. Falling edges occur at `2H, 4H, ..., 16H`; outgoing data advances on the first seven falling edges. The last transmitted bit remains on MOSI through the final hold interval.
- Chip select remains asserted through cycle `17H - 1`. At `17H`, chip select deasserts, SCLK and MOSI return low, busy clears, and the completed receive byte becomes valid.
- Completed data remains available during idle until an accepted request or reset. Requests while busy, including the completion edge, are ignored. A request can be accepted on the next edge, giving one idle system cycle between immediately restarted transactions.
- Synchronous active-high reset takes priority over any request or input value, aborts the transfer, clears the result, and restores idle outputs.

`incoming n` means the MISO value observed at system-clock edge `n`. A transition from elapsed cycle `n` to `n+1` consumes `incoming (n+1)`. The model's sampling edge also updates the generated SCLK output. This is a discrete digital convention, not a claim about pin propagation, setup/hold time, or metastability. A physical implementation must relate these samples to a peripheral's timing requirements.

Mode-0 edge behavior follows the [Microchip SPI transfer-mode table](https://onlinedocs.microchip.com/oxy/GUID-F5813793-E016-46F5-A9E2-718D8BCED496-en-US-15/GUID-0E901CC4-8D8D-458D-8FF5-8898F0C41259.html). The duration bounds, chip-select setup/hold intervals, and request/result interface are Pinwheel design choices, not universal SPI requirements.

## Model and proof coverage

`Pinwheel/SPI/Spec.lean` defines an explicit seventeen-phase pin waveform, absolute sampling times, and receive-byte assembly. `Pinwheel/SPI/Controller.lean` implements bounded phase (`Fin 17`) and interval (`Fin H`) counters, a captured transmit byte, eight Boolean receive registers, and result-valid state. Its output logic computes levels directly; it does not call the specification's waveform array. The cycle-indexed input history belongs to the specification and execution harness, not to the controller's stored state.

Theorems quantify over every configuration (`H=1–256`), outgoing byte, elapsed cycle, and arbitrary Boolean incoming history where applicable:

| Claim | Main checked theorem(s) |
| --- | --- |
| Finite control tracks absolute elapsed time, then stays idle. | `run_control`, `control_advances` |
| All three output pins match the independent waveform every cycle. | `waveform_correct` |
| Busy lasts exactly `17H` cycles. | `busy_exact` |
| Each of eight receive slots is enabled only on its designated edge; those edges are positive and distinct. | `capture_correct`, `sample_positive`, `sample_times_distinct` |
| Receive storage contains precisely the samples whose edges have occurred; other input changes do not affect it. | `run_samples` |
| MOSI is stable throughout each low/high phase pair, including the rising sample edge. | `phase_interval`, `mosi_stable_pair` |
| Result is absent before completion and equals the specified received byte afterward. | `received_complete`, `result_exact` |
| Reset dominates; busy requests are ignored; idle accepts a new byte; quiet idle retains the entire state. | `reset_dominates`, `busy_ignores_request`, `idle_accepts`, `idle_retains` |

The execution-refinement theorems describe an uninterrupted accepted transfer. The interface theorems separately describe reset, requests, and idle transitions; they do not claim a completed receive result for an aborted transfer. Together with the explicit waveform, the sampling theorems identify eight rising-edge captures. There is no analog input-stability assumption hidden inside the arbitrary Boolean history.

`lake build` checks these proofs through the root library import with warnings treated as errors. Axiom inspection of the main waveform, receive, result, stability, and interface theorems reported only subsets of `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, custom axioms, `sorry`, or `admit` were found in the library.

## Runnable checks and trace

From the repository root:

```sh
lake build
lake env lean -DwarningAsError=true --run test/SPI.lean
lake env lean -DwarningAsError=true --run test/UART.lean
```

The SPI checks passed 1,792 transfers:

- All 256 outgoing values, paired with their bitwise-complement replies, at `H=1,4,256`, each with quiet and noisy inputs away from sample edges: 1,536 transfers. This covers every TX and RX value at each duration, not every Cartesian pair.
- Fixed TX `0x53` with every possible reply at `H=1`, with off-edge noise: 256 more transfers, checking RX independently of TX.
- Every transfer checks every modeled cycle, exact pins and busy/valid timing, each receive slot, eight rising/falling/capture events, reset with a simultaneous request, restart after abort, ignored busy requests including the completion edge, retained results, and earliest restart after completion.

The CSV `build/spi/0x53-rx0xa6-4cycles.csv` contains 70 rows: 68 transfer intervals and two idle intervals. Columns are `cycle,cs_n,sclk,mosi,miso,sample,busy,valid,rx`. `sample` marks a capture at that row's edge; `miso` is the input snapshot at that edge; all other fields describe the resulting state. The partial receive register is shown even while valid is false.

An independent CSV check confirmed literal transmitted bits `01010011`, received bits `10100110`, samples at cycles `4,12,20,28,36,44,52,60`, falling edges at `8,16,24,32,40,48,56,64`, and idle/valid/RX=`166` beginning at cycle `68`. The existing UART checks also passed all 256 bytes at durations `1,4,256`.

A deliberately false scratch claim that a transfer with `H=1` is already valid at cycle `16` was rejected by `decide` because the proposition is false. This checks the distinction between the final falling edge and completion after the hold interval. Generated traces and scratch proofs remain under ignored `build/`.

These are Lean model results. No RTL, peripheral hardware, synthesis, or electrical timing has been validated. The [shared-engine proposal](shared-engine.md) records the requirements learned from UART and SPI and the next bounded implementation plan.
