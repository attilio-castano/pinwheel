# Fractional UART receiver

The single-clock [receiver hierarchy](../../Pinwheel/Hardware/Uart/FractionalRx.lean)
connects three typed instances: a two-flop input sampler, an 8N1 frame sampler,
and a one-result mailbox. The flat reference binds the same leaf expressions.
The top-level sample pulse and half-beat index expose the sampling decisions in
both Lean simulation and RTL.

The receiver detects a falling edge on the sampled input while idle and latches
the supplied half-bit period. A fractional timebase counts from that edge.
Half-beats 1, 3, …, 19 sample START, eight data bits in wire order, and STOP.
A high START sample aborts. A low STOP sample marks the result as a framing
error. STOP returns the sampler to idle on the same edge that it offers the
result to the mailbox. The mailbox can hold an unread result while the sampler
starts the next frame.

The mailbox consumes its old result first when `take` is high. A simultaneous
arrival then takes the freed slot. An arrival while the slot is occupied and
`take` is low leaves the old byte intact, drops the new byte, and sets the
sticky overrun bit. Reset clears the receiver and slot. A sampled falling edge
with a zero denominator or a half-bit period below one core clock is ignored.

## Timing bound

[FractionalTiming.lean](../../Pinwheel/UART/FractionalTiming.lean) proves the
sample edge is the ceiling of the ideal center. For an admitted sender period
and detection lag, every sample lies inside its sender symbol. Admission checks
the START and STOP margins and uses the affine error between them.

For the receiver profile `half_num = 60`, `half_den = 16` (7.5 core clocks per
bit), the proved digital envelope is sender periods from 118/16 through 126/16
core clocks, inclusive, with detection lag of up to 15/16 of a clock relative
to the sender edges at the **sampled input**. A fixed digital input delay shifts
both START and the following symbol boundaries together. The proof uses the
stated delay bound for the sampled line. Electrical setup, pad timing, and
metastability require separate characterization.

[FractionalRxTiming.lean](../../Pinwheel/Hardware/Uart/FractionalRxTiming.lean)
proves the source sampler latches the rate and starts with zero phase after an
admitted START. It follows the actual phase and half-beat count until STOP,
under a validated START and ordinary reset-free frame inputs. A high STOP
sample leaves the receiver idle with a high previous sample, so a following
low sample can detect a new START. The generated RTL certificate transfers
the sample-window result through the imported hierarchy, from the aligned,
active frame state.

## Replay from source

With the pinned Lean and CAD tools installed, run:

```sh
python3 -B scripts/check-fractional-uart-rx.py --tag fresh
```

The Python oracle generates two 8N1 frames with one stop bit and no extra idle
interval. The gate varies the sender bit period (118, 120, or 126 in sixteenths
of a core clock), its initial START phase (0, 1, or 15 sixteenths), and the
consumer (drain, stalled overrun, or simultaneous take and replacement).
The same 27 scenarios drive Lean and the three-instance emitted RTL. The
certificate checks all imported next-state and output equations and audits the
RTL timing theorem. Result data, order, and overrun are tested against the
independent oracle. The two-state RTL interpretation trusts the Yosys frontend
and its JSON interpretation.

Results are under `build/fractional-uart-rx/<tag>/report.json`.
