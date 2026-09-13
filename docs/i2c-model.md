# Pure Lean I²C experiment

Implementation record: **2026-09-13**. This is a finite reference controller and ideal shared-bus model. It is not yet an I²C program for the [shared engine](engine-model.md), a structural circuit, or generated RTL.

## Supported transaction

One controller writes a seven-bit address and one payload byte to one target:

```text
bus free → START → address + write bit → ACK → data → ACK → STOP
                                      NACK ─────────────→ STOP
```

Both ACK responses are independent. Address NACK skips the payload; data NACK still completes STOP. A target can stretch the clock, including the clock release used to prepare STOP. Results distinguish success, address NACK, data NACK, timeout, unexpected bus behavior, and reset abort.

I²C uses open-drain SDA/SCL with pull-ups: a participant pulls low or releases, and any low drive dominates. Bytes travel MSB first with a ninth ACK clock; the transmitter releases SDA for ACK. START/STOP change SDA while SCL is high, whereas data stays stable during high periods. Clock stretching holds SCL low after the controller releases it. These protocol rules follow [NXP UM10204, revision 7.0](https://www.nxp.com/docs/en/user-guide/UM10204.pdf), sections 3.1.1–3.1.6 and 3.1.9.

The model assumes an ideal digital bus with instantaneous pull-ups, a single controller, and a cooperating target that changes ACK drive only while SCL is low. Normal addresses `0x08`–`0x77` are exercised. `Request.address : Fin 128` can represent reserved encodings, but their special semantics are not implemented. Reads, repeated START, multiple controllers, arbitration, and bus recovery are outside this experiment.

## Commands, observations, and time

`Drive` has two constructors: `low` and `release`. `Pins` contains controller or target commands; `Bus` contains the resolved Boolean levels. Releasing a line does not establish that the observed line is high. There is no active-high command in this model.

`initial` accepts a request into a finite state. `step` consumes the resolved bus immediately before a system edge and produces commands after that edge. The state holds a request, an 18-slot bit/ACK index, a phase, two bounded counters, and an outcome. This is a reference algorithm; its Lean state is not a proposed gate-level register allocation.

The configured phase duration `H` and blocked-observation budget `W` range from 1 through 256. The reference uses a common phase duration to expose ordering before optimizing individual timing parameters:

| Phase | Behavior |
| --- | --- |
| `free` | Release both lines; qualify both high for `H` observations before START. |
| `startHold` | Pull SDA low with SCL released; hold before the first clock-low phase. |
| `setup` | Hold SCL low and establish the next bit or release SDA for ACK. |
| `rise` | Release SCL; wait until the **observed** SCL is high. |
| `high` | Start a fresh `H`-cycle timer; sample ACK on its terminal observation. |
| `fall` | Pull SCL low while retaining the old SDA command for a full phase. Then select the next bit or STOP. |
| `stopLow`, `stopRise`, `stopHigh` | Pull both low, release SCL and wait for observed high, then hold SDA low before releasing it. |
| `stopFree` | Qualify both lines high for a phase before reporting completion. |
| `finished` | Release both lines and retain the result until reset. |

Stretching consumes the wait budget without consuming the high-period timer or advancing the bit slot. A ready observation wins even when the remaining wait counter is zero. Persistent blocking times out on the `W`th blocked observation; up to `W - 1` blocked observations can precede readiness. The same bounded wait is used for bus-free qualification and STOP clock release.

The timeout is a **project policy**, not a claim that ordinary I²C mandates this deadline. During initial bus-free qualification, a high observation refreshes the wait budget; intermittent interference can therefore prevent completion indefinitely. There is no unconditional liveness claim.

Unexpected SCL low after entering `high`, `startHold`, or `stopHigh` reports `busFault`. Failure to observe both lines high during `stopFree` also faults. Reset, timeout, and bus faults release both lines. They cannot guarantee a STOP on a stuck bus, or force a line high against another participant. Reset synchronously aborts rather than completing the protocol.

The wait-to-high transition introduces an observation edge, so external high intervals can exceed `H`. The checks establish configured minima and the exact internal capture boundary. They do not establish a standard electrical speed grade, rise time, metastability behavior, or pad timing.

## Proof and executable evidence

The 19 audited theorems establish bus resolution, independent wire-order correspondence, ACK-slot release and decisions, NACK routing, high-phase data retention, exact high countdown and terminal capture, stretch retention and exact persistent-block timeout, reset release, and finished-state retention. They quantify over their stated states, inputs, and bounded parameters. Dependencies are limited to standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`); the bus-resolution proofs use none.

These are reusable local and multi-cycle theorems. A universal closed-loop transaction theorem against an independently specified target remains future work. Passing executable transactions supplies additional sampled evidence, not that missing theorem.

The target simulator and protocol monitor use pin commands and resolved wire transitions, not controller phases or its bit-selection function. The monitor checks START/STOP, pulse counts, bit order, ACK release, and minimum high/low intervals. It independently calculates the expected address byte, payload, and result.

Verified with Lean 4.33.1:

- **4,224 transactions, 822,896 observed cycles**: every payload at durations 1 and 4 with four ACK combinations and quiet/stretched clocks; all 112 normal seven-bit addresses; duration/budget 256 with four payloads and 255-cycle stretches.
- All 256 wait budgets and high durations, readiness at the deadline, persistent low SDA/SCL, unexpected clock-low faults, and reset-release checks at every transaction observation.
- Three deliberately faulty transitions rejected for the expected failure: wrong payload, shortened high period, and ignored stretching.
- Example address `0x53`, payload `0xA6`, both ACKs, `H=4`, `W=8`: **255 cycles** without stretching and **282 cycles** with per-release delays of 0–3 cycles. The additional 27 observations preserve the transmitted bits.
- `lake build` passed with 28 jobs; the existing 2,560-transfer UART/SPI engine regression and boundary/reload cases passed.

The transaction totals exclude the separate boundary checks, fault injections, and two example runs. Hardware sources were not changed or revalidated in this batch; the earlier [core receipt](core-hardware.md) identifies its own artifacts.

Reproduce without hardware tools:

```sh
python3 scripts/check-i2c.py
```

The runner builds the library, audits each named theorem, executes the bus tests and negative cases, and writes source/artifact hashes to ignored `build/i2c/report.json`. The example trace is `build/i2c/write-0x53-0xa6-stretched.csv`; it includes drive commands, observed lines, and internal state for inspection. `test/I2C.lean` and `test/I2CAxioms.lean` can also be run directly through `lake env lean -DwarningAsError=true` after building.

## Implications for the shared engine

The existing fixed-schedule core remains a useful measured baseline. This experiment exposes four missing capabilities:

1. **Separate output drive from input observation.** Preserve push-pull output values for UART/SPI while adding per-pin output enable and observing both SDA and SCL. An open-drain configuration must never actively drive high. Give idle, reset, and faults explicit release behavior.
2. **Wait for an input condition, then start timed work.** Define selected input, polarity, observation edge, finite wait budget, readiness-versus-timeout priority, and the exact continuation edge. The clock-high timer starts after observed readiness. Merely delaying a fixed action cannot implement stretching.
3. **Capture and branch.** Sample SDA at the terminal high-period boundary and select continuation from ACK/NACK. Normal NACK should execute STOP; timeout should use an abort path that releases lines. Specify branch target validation, result codes, and counter/capture retention.
4. **Revisit program capacity and payload storage.** Even a naïve expansion into two timed phases per clock needs 36 actions for 18 clocks, before START/STOP. That exceeds the existing 32-slot store. This is an expansion estimate, not a lower bound for every ISA: combined operations, loops, and reusable byte data can change it. Reference phases do not each imply a hardware instruction.

The next bounded implementation should add the two-line drive/observation contract and a wait-then-timed continuation to the abstract engine, with a one-bit stretched-clock example. First define an embedding of existing actions and prove the original UART/SPI observations unchanged. Test duration one, immediate readiness, readiness at the deadline, persistent blocking, reset, and stopped reload.

After that, add ACK capture/branch semantics and compile this complete write transaction. Prove its correspondence to an independent protocol contract under explicit target assumptions, then demonstrate UART → SPI → I²C → UART through program replacement on one machine. Measure instruction and data storage before choosing a revised binary encoding or enlarging memory.

Only then extend the structural decoder/store/scheduler and circuit refinement, regenerate RTL, rerun independent traces and fault injections, and compare synthesized cost with the current core. Translation/equivalence, physical loading, synchronizers, pad enables, and electrical timing retain their separate proof and implementation obligations in the [processor plan](processor-verification.md).
