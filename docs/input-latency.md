# Input latency

This record owns input latency as a parameter of the pin-level protocol
contracts: the shared model, what the two-register [pin sampler](pin-sampler-study.md)
does to UART, SPI and I²C, and the I²C contract revision it called for, now made
in both reference controllers and all three compiled programs. The protocol results are
Lean proofs and executions; one RTL simulation closes the I²C loop around the
sampled hardware. No place-and-route runs. The
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
| STOP echo | `guarded_stop_echo_faults`: under the bus-free transition specified until 2026-09-17 (`guardedStopFree`), an observation resolved while the controller was in `stopLow`, `stopRise` or `stopHigh` yields `busFault` | For any `d ≥ 1`, a transaction whose wire behaviour was complete and correct reported a bus fault. **Removed by the revision below.** |
| Wait budget | `stale_clock_observation_blocks`, `stop_echo_is_waited_out`, `echo_exhausts_wait`: observations from the controller's own clock-low and STOP phases count as blocking in `rise`, `stopRise` and `stopFree` | Every clock rise, and the bus-free hold, spends `d` units of the wait budget; `waitCycles ≤ d` times out with no stretching target |
| Premature high | `stale_low_in_high_faults`, with `released_clock_starts_timer`: an observation older than the clock-low phase reads high and starts the high timer; the low phase then arrives in `high` as a fault | The clock-low time must cover the latency: `d ≤ phaseCycles` |

ACK sampling is not a hazard: the sample consumed at the end of the engine's high
phase was taken `phaseCycles` after the true rising edge, inside the true high
window in which a target holds SDA.

### The revision

Bus-free time after STOP is now **qualified**, exactly as it already was before
START: both lines must read high for `phaseCycles` consecutive observations; a low
observation restarts that count and spends the wait budget; persistent blocking
ends in `timeout`. `stop_echo_is_waited_out` shows the echo is absorbed,
`stop_completes` that a full free interval still reports the transaction's
outcome. The register-read controller (`I2C/RegisterRead.lean`) has the same
revision and the same two lemmas.

Two multi-step closed forms say what the wait budget buys. Both hold for every
observation history of the stated shape, and both rest on `blocked_prefix`
(blocked observations change nothing in a fresh waiting phase but the budget):

- `rise_behind_pipeline`: from a fresh `rise`, `d ≤ waitLeft` observations that
  still show SCL low followed by one high observation enter `high` with a full
  timer. The blocked observations may be the controller's own echo, a stretching
  target, or both; they share one budget.
- `stop_completes_behind_pipeline`: from a fresh `stopFree`, `d ≤ waitLeft`
  blocked observations followed by `phaseCycles` free ones report the
  transaction's outcome. The register-read controller has the same theorem.

With `echo_exhausts_wait` as the converse at a clock rise, `d < waitCycles` is
exactly what the echo alone requires there, and it suffices at STOP.

Nothing was added to the instruction set or the hardware. The revised phase *is*
the existing `qualify` instruction — the one at address 0 — so:

| Program | Change | Re-proved |
| --- | --- | --- |
| Explicit write, `Compile/I2C.lean` | Address 77: guarded `checked` → `qualify` (identical to address 0) | `Compile/I2CPhases.lean` `advance_stopFree`; the complete-state correspondence in `I2CProofs.lean` is unchanged in statement and still holds for every request, configuration and input history |
| Counted write, `Compile/I2CLoop.lean` | Template 13 likewise | Fetch equality and complete-state equality with the explicit program |
| Register read, `Compile/I2CRead.lean` | Address 153 likewise | `I2CReadProofs.lean` correspondence |

The serialized write images shrink by two bytes ([713 and 203](binary-images.md));
the emitted RTL is byte-identical, because programs are loaded, not synthesized.

**What changed for `d = 0`.** Under the former contract any low observation during
the bus-free hold was an immediate `busFault`. Now a target that holds SDA low
after STOP ends in `timeout` after the wait budget, and a disturbance shorter than
the budget is waited out. A second controller that takes the bus after our STOP
produces `timeout` if the blocking exhausts the wait budget, replacing the
transaction's ACK outcome. If the bus becomes free in time to complete the
qualified interval, the original outcome is retained. Bounded waiting remains
a project policy, not an I²C rule.

A narrower revision was modelled first: wait out only the low observations that
precede the first free one, and keep any later low observation a fault. On the
engine that is a `wait` followed by a guarded `checked` action, one more
instruction, a shifted address map and a new lift; the qualified hold reuses a
record the program already contains. The narrower model was removed.

### Closed-loop evidence

`test/Latency.lean` closes the loop around the reference controllers **and the
compiled engine programs**, with a target that changes SDA only while the true SCL
is low, optionally stretches, and sees the controller's pins undelayed (111 write
runs at phase 2, 3 and 5 cycles; 64 register reads at 3 and 5):

- `d = 0`: the former and the revised write controller both succeed.
- `1 ≤ d ≤ phaseCycles`: the former transition produces all 18 clock pulses with
  the right bits and a STOP, then reports `busFault`. The revised controller and
  the compiled program succeed, with and without stretching, report address and
  data NACKs, and produce identical pulse sequences.
- `d = phaseCycles + 1`: fault before any clock pulse (premature high).
- wait budget `d`: `timeout`; wait budget `d + 1`: success.
- Register read, `d = 0…3`, four data bytes: reference and compiled program return
  the byte after 36 pulses and a STOP.

So behind `d` input registers I²C needs **`d ≤ phaseCycles` and `d < waitCycles`**,
each SCL high period is `d` cycles longer on the wire, and so is the bus-free hold.
With the two-register sampler: phase at least two cycles, wait budget at least
three.

### On the emitted hardware

The independent core and loader vector generators (`i2c_latency` in
`scripts/reactive-core-vectors.py`) also run both programs with the bus consumed
two edges late while the target sees the pins at once: two data bytes, quiet and
stretched, write and register read, eight runs per suite. They rerun the former
guarded record in place of the final `qualify` as well: it completes on an
undelayed bus, and behind two registers it ends in the engine's fault state after
a complete, correct wire transaction. The direct and indexed cores (40,881 and
45,297 edges) and the atomic loader (33,858 edges) match the oracle throughout, as
Lean structural components and in RTL simulation.

`check-sampled.py` presents each row's pins two edges early to the pin-sampled
RTL. For those eight runs the presented pins are exactly the bus a target would
produce, so the sampled netlist executes complete I²C writes and register reads
in closed loop: 35,824 edges pass, and the unshifted and inner-shifted replays are
rejected. The emitted `sampled.sv` is byte-identical to the routed candidate
(`3e6cf6be…`), so the [physical results](pin-sampler-study.md) describe the
hardware that runs the revised programs. Receipt:
`build/sampled/i2c-02/report.json`.

## Boundary

- The I²C statements are per-observation and per-phase theorems plus closed-loop
  executions, the same split the existing I²C evidence uses; no whole-transaction
  closed-loop theorem over all targets is claimed. The compiler correspondence is universal over input
  histories, so every closed-loop run of the reference is also one of the program.
- The rate conditions are obligations on whoever chooses `Config`; the compiler
  does not yet reject a configuration that violates them for a declared latency.
- SPI still needs `d + tco ≤ halfCycles`; capture compensation is not built.
- Everything here is digital. Metastability, thresholds, rise times and
  asynchronous arrival remain outside the model, as before.

## Reproduction

```sh
lake build Pinwheel
lake env lean -DwarningAsError=true --run test/Latency.lean
lake env lean -DwarningAsError=true --run test/UARTLink.lean
lake env lean -DwarningAsError=true --run test/I2C.lean
python3 scripts/check-reactive-core.py     # needs the pinned hardware tools
python3 scripts/check-loader.py
python3 scripts/check-sampled.py --tag NAME
```
