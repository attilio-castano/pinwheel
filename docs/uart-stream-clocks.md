# Continuous UART reception with unequal clocks

Validated 2026-09-15 by `uart-stream-clocks-01`. The Lean receiver now has a
finite-stream correctness theorem for unequal TX/RX clocks and bounded,
varying digital observation age. The theorem includes enough time to rearm and
observe idle high before every next frame. It composes with the existing compiled
RX supervisor and [one-entry result buffer](uart-stream.md).

## Timing contract

This extends the [one-frame UART link](uart-link.md). Both clocks have positive,
constant tick lengths in a shared integer time quantum; their tick lengths and
initial phases may differ. Observation age may vary independently on every RX
edge within `Dmin ≤ age(n) ≤ Dmax`. The wire contains adjacent 8N1 frames with
one stop bit each. Transitions belong to the new symbol.

| Symbol | Meaning in shared time quanta |
| --- | --- |
| `P` | TX cycles per bit × TX tick length |
| `Q` | RX cycles per bit × RX tick length |
| `R` | RX tick length |
| `C` | floor(RX cycles per bit / 2) × RX tick length |
| `S` | Observation-age spread, `Dmax − Dmin` |

`UART.StreamLink.Safe` requires the existing `UART.Link.Safe` conditions and:

```text
C + 9Q + S + 3R ≤ 10P
```

The previous stop-sampling bound allowed `C + 9Q + S + R ≤ 10P`. Its `R`
reserves uncertainty about the first start observation. The extra **two RX
ticks** reserve the automatic rearm edge and an idle-high observation after it.
This gives a byte-independent sufficient condition for continuous reception.
It retains every ideal shared bit period **8–256**, including odd periods.
The general contract supports the existing TX range 1–256 and RX range 8–6656
when their physical periods meet the inequalities.

If start is detected at local RX edge `d`, completion occurs at
`d + floor(B/2) + 9B`, where `B` is RX cycles per bit. The following edge rearms
without observing the line. The new bound proves that the edge after that is
still before the earliest delayed next start, so the receiver can observe high.
No extra wire cycles are inserted to achieve this condition.

The bound is sufficient, not a claimed optimal tolerance. A known phase may work
outside the reserved margin. Clock tick lengths stay constant within the model;
arbitrary clock-frequency jitter is not inferred from varying observation age.

## How the stream proof composes

The source is the existing `Rx.Stream.wireBody`: a concatenation of one-byte TX
specifications. `StreamLink.sampled` observes that source through the earlier
integer-clock/age model. The proof establishes:

1. **Before the next frame:** the observed continuous wire agrees with the
   one-frame source through the current frame's relevant observations. Existing
   start detection and all ten sample-window proofs therefore apply.
2. **After completion:** every allowed observation has reached at least the old
   stop bit. Replacing that stop suffix with idle before the next frame preserves
   the remaining observed wire, even if observation age varies non-monotonically.
3. **At rearm:** advance TX start by `10P` and set the new local RX origin to the
   actual rearm edge in global time. The same sufficient contract still holds.
4. **Across the list:** induct over any finite byte sequence, preserving the
   original payload order and recomputing the detection interval for each frame.

`Windows` records each local detection between `firstEdge(Dmin)` and
`firstEdge(Dmax)` after that rebase. The public model theorem
`UART.StreamLink.receive_series` produces a frame sequence whose payload list
equals the source list and whose completion pulses are exact through the final
rearm edge. It requires an initially armed receiver and no reset during the run.
Consumer `take` and clear-overrun histories, and initial buffer contents, remain
unrestricted.

`Compile.UARTStreamLink.receive_series` carries the same statement through the
existing compiled RX and supervisor. It accepts arbitrary spare-input history.
Existing state/receipt correspondence and buffer accounting still apply: a late
consumer can cause an explicit drop, while receiver completion timing remains
independent of buffer fullness. Reception correctness does not promise lossless
consumer delivery under arbitrary stalls.

## Example at the strengthened boundary

TX uses 16 cycles per bit with ticks of 97 quanta; RX uses 16 cycles per bit with
ticks of 100. Observation age can vary anywhere from 20 to 40 quanta:

```lean
import Pinwheel.Compile.UARTStreamLink

open Pinwheel

def clockTiming : UART.Link.Timing :=
  { tx := ⟨15⟩
    rx := ⟨16, by decide, by decide, 0⟩
    txTick := 97
    txTickPositive := by decide
    rxTick := 100
    rxTickPositive := by decide
    txStart := 301 }

def clockLatency : UART.Link.Latency := ⟨20, 40, by decide⟩

example : UART.StreamLink.Safe clockTiming clockLatency := by decide
```

Here `P = 1552`, `Q = 1600`, `C = 800`, `R = 100`, and `S = 20`, so the
strengthened upper bound holds with equality: `800 + 14400 + 20 + 300 = 15520`.
For two bytes, the detection windows collapse to global RX edges 4 and 159;
completion occurs at edges 156 and 311, with rearm at 157 and 312. The first
post-rearm observation, edge 158, precedes the earliest delayed second start.
Each later start establishes a fresh sampling schedule. Lean checked these
concrete windows and completions, the sufficient bound, and a use of the public
compiled theorem for `[0x53, 0xa6]` with arbitrary bounded age history.

## Repository owners and implementation boundary

| Owner | Responsibility |
| --- | --- |
| [StreamLink.lean](../Pinwheel/UART/StreamLink.lean) | Sufficient contract, observed continuous source, time rebase, and detection-window sequence |
| [StreamLinkTiming.lean](../Pinwheel/UART/StreamLinkTiming.lean) | Sample/completion arithmetic, post-rearm deadline, and stop visibility for future observations |
| [StreamLinkWire.lean](../Pinwheel/UART/StreamLinkWire.lean) | One-frame prefix agreement and complete suffix agreement after stop |
| [StreamLinkProofs.lean](../Pinwheel/UART/StreamLinkProofs.lean) | Valid frame segments, preserved bounds after rearm, finite-stream event correctness, and ideal-domain inclusion |
| [Compile/UARTStreamLink.lean](../Pinwheel/Compile/UARTStreamLink.lean) | Compiled RX/supervisor theorem |
| [test/UARTStreamClocks.lean](../test/UARTStreamClocks.lean) | Independent global-time wire, detection schedule, queue oracle, timing sweep, and counterexamples |

The default import and foundation runner include the new modules and suite.
The receiver, buffer, compiler, and existing program semantics are unchanged.
E64/storage and previous hardware evidence retain their earlier source identities.

This proves the digital contract at the Lean/model level. A physical sampler must
justify the assumed age envelope; these proofs do not resolve metastability or
establish electrical timing. Concatenated TX frame specifications also leave
repeated TX launch scheduling separate. Supervisor/buffer circuitry, composition
with atomic loading and reset control, and concurrent TX/RX resource scheduling
still need their own designs and evidence. This milestone performs no CAD run.

## Validation and reproduction

The prospective brief compared against `c133af9` plus prior UART work, identified
by `build/validation/uart-stream-01/report.json`, SHA-256
`666fa5a60e9052c9d2b64322d7e5acce1d38e26c750fb6b533cc1d16fb441f66`.
All 173 recorded baseline source hashes matched before work. The only changes
to those sources are the library import and gate registration; five new library
modules and one new test file implement this milestone.

The brief selected Lean 4.33.1 proofs, the standard-axiom audit, independent
global-time wire/event schedules, consumer checks, boundary cases, and a fresh
`uart-stream-clocks-01` full foundation gate with frozen sources. The preceding
gate took 882.133 seconds; no new resource cap was specified. Local proof or
regression failures prevent a success receipt.

```sh
lake build
lake env lean -DwarningAsError=true --run test/UARTStreamClocks.lean --focused
lake env lean -DwarningAsError=true --run test/UARTStreamClocks.lean
python3 scripts/check-foundation.py --tag <fresh-tag>
```

The focused option reduces the long payload sweep from 256 values to 8 and writes
`build/uart-stream-clocks/report-focused.json`; the default writes `report.json`.
Both run 392 streams. The default coverage includes:

- Every byte at TX ticks 97 and 103 versus RX ticks 100, with 16 cycles per bit,
  both inputs, three relative clock phases, four age histories, and three
  consumer policies. TX start stays fixed while RX phase changes.
- Unequal cycles-per-bit settings, one-cycle TX symbols, odd RX periods,
  RX chunk boundaries at 257/512 cycles, maximum RX period 6656, and equality
  at the strengthened timing bound.
- Cached actual reference/compiled TX traces checked against a direct physical
  bit-index oracle. Expected detections come from delayed start visibility,
  independently of the RX state. Every RX edge checks completions, compiled
  state, released outputs, queue receipts, pending data, and overrun.
- A 2,160-configuration sweep: **960 continuous-safe**, **176 single-frame-only**,
  and **1,024 outside even the single-frame bounds**. Every candidate detection
  is checked at both age extremes for three successive frames: **13,056 windows**.
- Four failing-assumption examples: the previous rearm failure, excessive clock
  mismatch in both directions, and an observation age that misses nominal
  deadlines. A successful excluded phase demonstrates conservative bounds.

The first focused attempt failed because the exploratory successful-excluded
example used start time 301, which actually lacks an idle-high observation after
rearm. Moving that example to 300 produced the intended successful excluded
phase. The failure and source hash are retained in
`build/uart-stream-clocks/focused-attempt-01.json`. The final focused check,
including independently varied RX phase, passed **4,817,146 RX edges** and
**3,096 frames**. The numerical proof was unchanged by the test correction.

The **full unequal-clock stream suite passed**:

| Check | Result |
| --- | ---: |
| Stream/consumer/clock combinations | 392 |
| Received frames | 38,808 |
| RX edges | 10,531,120 |
| Delivered outcomes | 17,156 |
| Explicit buffer drops under consumer stalls | 21,392 |
| Outcomes pending at the end of the scenarios | 260 |

The aggregate balance is `38,808 = 17,156 + 21,392 + 260`; each scenario also
checks its own balance. Always-ready consumers receive every frame. This count
does not include the separate outside-contract examples. Stream receipt:
`build/uart-stream-clocks/report.json`, SHA-256
`95d05e147009c70b86eb297309f9f184bf340b2cc813f9b24703846dc3b2bdfd`.
The final focused receipt has SHA-256
`340d4aa40b3873e4632ce14eefdb8ffcbc5016f17d66b56984702ee10b579812`.

The **`uart-stream-clocks-01` foundation gate passed** on Lean 4.33.1:

| Check | Result |
| --- | ---: |
| Library modules reachable from the default import | 125 |
| Audited declarations | 10,058 |
| Audited theorems, including generated declarations | 5,254 |
| Executable suites | 24 |
| Independent Python oracles | PWL lookup and UART RX/E64 passed |
| Injected untrusted axiom | Rejected for the expected diagnostic |
| Source hashes, stable during validation and at closeout | 179 |
| Elapsed time | 1,012.316 s |

Foundation receipt: `build/validation/uart-stream-clocks-01/report.json`, SHA-256
`4c37c8bfffb9b7664564f58bf024172de510c044680498d9424cb63c84de22e5`.
The whole-library audit permits only `propext`, `Classical.choice`, and
`Quot.sound`. No new proof uses an untrusted axiom or an unfinished proof.

Ignored local artifacts identify these runs but are not a durable backup; source
runners reproduce the checks under fresh run identities.
