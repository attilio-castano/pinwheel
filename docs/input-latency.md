# Input latency

This record owns input latency as a parameter of the pin-level protocol
contracts: the shared model, what the two-register [pin sampler](pin-sampler-study.md)
does to UART, SPI and I²C, and the I²C contract revision it calls for. It is pure
Lean and executable evidence; no CAD tool runs. The
[external interface contract](external-interface.md) owns the digital boundary;
[research status](research/status.md) owns allocation.

## Question

Outputs leave the engine undelayed; inputs now arrive two edges late. Every
protocol model and compiler theorem speaks about the engine-side input history.
What does each protocol's contract say at the pins when that history is the pin
history `d` edges earlier, and which contracts survive unchanged?

## Model

`Pinwheel/Latency.lean`: `delayed d idle pins` is the history consumed behind `d`
registers that all held `idle` at cycle zero — `idle` for the first `d` cycles,
then `pins (n − d)`. `delayed_shift`, `delayed_draining`, `delayed_zero` and
`delayed_add` (pipelines compose) are its algebra.

`Hardware/InputLatency.lean` bridges to the structural pipeline:
`PinSampler.delayed_incoming` proves that the wrapped netlist's engine-side
`incoming` list is the pin list shifted by two edges, preceded by the pipeline's
power-up contents; `delayed_incoming_get` states it cycle by cycle. This is the
bridge the sampler study listed as missing.

Because the protocol and compiler theorems already hold for **every** input
history, a pin-level statement is obtained by substitution. What is
protocol-specific is which assumption about the peer makes the delayed history a
good one. That assumption is the contract.

## UART: unchanged up to the age bounds

Proved earlier in `UART/LinkPipeline.lean` and now phrased in the shared
vocabulary (`delayed_observe`): behind `stages` idle-high registers the receiver
consumes an ordinary observation history whose age is `stages` RX ticks later.
`Link.Safe` and `StreamLink.Safe` constrain only the earliest age from below and
the age spread, so both survive (`Safe.delayed`). Obligation: the stages hold
idle-high when a receiver program starts.

## SPI: a rate condition

`SPI/Latency.lean`. The controller's waveform is `waveform_correct` for every
input history, so latency cannot disturb it. Its samples are consumed at each
rising clock edge, hence taken at the pins `d` cycles **before** that edge.

- `Presents cfg pins reply lead`: the peripheral carries each reply bit from
  `lead` cycles before its sampling edge until that edge.
- `expectedByte_delayed` / `result_behind_pipeline`: if `d ≤ lead ≤ halfCycles`,
  the byte received behind `d` registers is the reply.
- `Mode0 cfg pins reply tco`: a mode-0 peripheral that changes MISO `tco` cycles
  after each falling edge. `Mode0.presents` gives `lead = halfCycles − tco`, and
  `mode0_behind_pipeline` is the rate condition:

  > **`d + tco ≤ halfCycles`** suffices.

- `Compile.SPI.received_behind_pipeline` transfers it to the compiled engine
  program.

`test/Latency.lean` runs 600 transfers over half-periods 1, 2, 3, 4 and 6, `tco`
0–3 and latency 0–4 against a peripheral that shows the least helpful value outside its
windows: every transfer inside the bound is correct, and one cycle beyond it
(`d + tco = halfCycles + 1`) the reply `0xAA` is misread, so the bound is tight for
this capture schedule. With the two-register sampler and a peripheral delay under
one cycle, the half-period must be at least three cycles: SCK at most one sixth of
the system clock. A compiler that captures `d` cycles later would lift this;
capture happens at action entry, so that means splitting the high phase. Not built.

## I²C: three hazards, all from observing its own drive

`I2C/Latency.lean`. Unlike UART and SPI, this controller checks the bus right
after changing its own command. A delayed view shows it that earlier command.
Each statement below holds **for every target**.

| Hazard | Theorem | Consequence |
| --- | --- | --- |
| STOP echo | `stale_stop_observation_faults`: in `stopFree`, an observation resolved while the controller was in `stopLow`, `stopRise` or `stopHigh` yields `busFault` | For any `d ≥ 1` a transaction whose wire behaviour is complete and correct reports a bus fault |
| Wait budget | `stale_clock_observation_blocks`, `echo_exhausts_wait`: observations from the controller's own clock-low phases count as blocking in `rise`/`stopRise` | Every clock rise spends `d` units of the wait budget; `waitCycles ≤ d` times out with no stretching target |
| Premature high | `stale_low_in_high_faults`, with `released_clock_starts_timer`: an observation older than the clock-low phase reads high and starts the high timer; the low phase then arrives in `high` as a fault | The clock-low time must cover the latency: `d ≤ phaseCycles` for the first clock |

ACK sampling is not a hazard: the sample consumed at the end of the engine's high
phase was taken `phaseCycles` after the true rising edge, inside the true high
window in which a target holds SDA. The register-read controller
(`I2C/RegisterRead.lean`) has the same `stopFree` guard and therefore the same
STOP echo.

**Revised controller.** `tolerantStep` differs from `step` in one place: in
`stopFree`, an SDA that still reads low *before any bus-free cycle has been
counted* is waited out against the wait budget, exactly as a low SCL is in
`rise`. `tolerantStep_eq_step` shows it is otherwise identical;
`tolerant_waits_out_stop_echo` removes the first hazard;
`tolerant_faults_after_free` keeps a later low SDA — another controller's START —
a fault. For `d = 0` it changes one outcome: a target that holds SDA low at STOP
now ends in `timeout` after the wait budget instead of an immediate `busFault`.

`test/Latency.lean` closes the loop around both controllers with an
acknowledging, optionally stretching target that changes SDA only while the true
SCL is low (58 runs, phase 2/3/5 cycles):

- `d = 0`: both succeed.
- `1 ≤ d ≤ phaseCycles`: the specified controller produces all 18 clock pulses
  with the right bits and a STOP, then reports `busFault`; the revised one
  succeeds, with and without stretching, and reports address and data NACKs.
- `d = phaseCycles + 1`: both fault before any clock pulse (premature high).
- wait budget `d`: `timeout`; wait budget `d + 1`: success.

So behind `d` input registers the write controller needs the revision and
**`d ≤ phaseCycles` and `d < waitCycles`**, and each SCL high period is `d` cycles
longer on the wire.

## Boundary

- The revised controller is a reference model. The reactive compiler, its phase
  tables and proofs (`Compile/I2C*.lean`) still implement `step`; recompiling and
  re-proving against `tolerantStep`, and the matching revision of the register-read
  controller, are open. Until then I²C behind the sampler reports bus faults.
- The I²C statements are per-observation theorems plus closed-loop executions,
  the same split the existing I²C evidence uses; no closed-loop theorem over all
  targets is claimed.
- Everything here is digital. Metastability, thresholds, rise times and
  asynchronous arrival remain outside the model, as before.

## Reproduction

```sh
lake build Pinwheel
lake env lean -DwarningAsError=true --run test/Latency.lean
lake env lean -DwarningAsError=true --run test/UARTLink.lean
```
