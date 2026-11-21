# Fractional timebase and TX replay

The timebase emits a synchronous beat enable. A programmed period is
`numerator / denominator` core clocks, with
`0 < denominator ≤ numerator`. The accumulator adds the denominator on each
edge and emits a beat when the sum reaches the numerator. It subtracts the
numerator on that edge. All registers use the existing core clock.

[Fractional.lean](../../Pinwheel/Hardware/Timebase/Fractional.lean) proves the
exact beat count after any uninterrupted prefix of `n` edges, starting at zero
phase. The count is `⌊n × denominator / numerator⌋`. Consecutive beats are
separated by the floor or ceiling of the period. At the edge that emits a beat,
the accumulated timing error is less than one core clock relative to the ideal
deadline. [Circuit.lean](../../Pinwheel/Hardware/Timebase/Circuit.lean) proves
that the widened addition, comparison and conditional subtraction implement
the source step for every representable legal period and valid phase.

## One image with two timing profiles

[Tx.lean](../../Pinwheel/Hardware/Timebase/Tx.lean) is a finite TX client for the
timebase. The synchronous START edge captures an eight-bit image and a separate
timing profile when idle. START refuses zero denominators and periods shorter
than one clock. A busy START leaves the active image and profile in use. The pin
presents the first bit after the accepted START, then consumes one LSB-first
bit at each beat. The final beat returns the line to its idle-high level.
The pre-edge `beat` output marks the bit that completes on the upcoming edge.
Synchronous reset clears the active image and phase.

The first two sessions in the replay load the same image, `0xA6`, on the same
emitted circuit. Both transmit `0,1,1,0,0,1,0,1`.

| Core clocks per bit | Bit-completion edges after START |
| --- | --- |
| 8 | 8, 16, 24, 32, 40, 48, 56, 64 |
| 15/2 | 8, 15, 23, 30, 38, 45, 53, 60 |

## Reproduce from source

With the pinned Lean and CAD tools installed, run:

```sh
python3 -B scripts/check-fractional-timebase.py --tag fresh
```

The gate builds the Lean sources, emits the typed circuit via CIRCT, and
checks both Lean simulation and Verilog replay against a Python oracle that
computes absolute rational deadlines. It also exercises the fastest legal
period, addition across the original operand width, invalid profiles, a
competing START and reset during transmission. Lean checks every imported
RTL register and output equation, then transfers reset and active timebase
refinement to the imported model. Swapping the TX and beat outputs must fail
both replay and the certificate.

Results are in `build/fractional-timebase/<tag>/report.json`. The certificate
covers the two-state synchronous RTL interpretation through the Yosys frontend.
The client marks the standalone milestone. Edge alignment, external clock
following and Ready integration are subsequent timing work.
