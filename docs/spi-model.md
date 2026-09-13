# Pure Lean SPI experiment

Contract selected: **2026-09-13**. Implementation and proof verification are in progress.

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

## Planned evidence

The independent specification defines output waveforms, absolute sampling times, and the received byte. The implementation will use finite control state and receive storage. Proofs must connect both for arbitrary incoming samples, alongside reset/request/completion properties. Executable checks will cover all outgoing and incoming byte values at boundary and representative durations, input changes between sample points, reset, busy requests, and restart.

The completed record will include exact theorem coverage, axiom dependencies, runnable checks, and CSV traces. The existing UART experiment remains a regression check.
