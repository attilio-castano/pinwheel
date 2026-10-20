# Digital-session refinement: morning report

Campaign launched October 17, 2026 at 5:09 a.m. Eastern
(`2026-10-17 09:09:14 UTC`), with a twelve-hour maximum ending at
5:09 p.m. Eastern. Branch: `codex/digital-session-refinement`.
Starting commit: `18fb3d0dc43180b94c32723bba7010f13d342f26`.

**Completed.** All four proof targets and the timing extension passed their
validation gates. Receipt verification closed at 8:02 a.m. Eastern
(`2026-10-17 12:02:24 UTC`), 2 hours 53 minutes 10 seconds after launch.
The full queue and its extension closed inside the twelve-hour maximum.
Proof snapshot: `6926de39b9b4aedfce9400f70e5e9abd5e399ef2`.
Final validation-driver snapshot: `1658c56b166641a0370eaa016754f813fe46d769`.

## Result

The previous SPI milestone established one initialized transfer. This campaign
connects source execution, actual digital SRAM, repeated logical ownership and
sampled serial transport in one finite session history.

For the fixed four-byte I²C source,
`LogicalWire.Interrupted.initialized_session` starts from arbitrary digital
controller state, both SRAM arrays and their registered Q values. A physical
cold edge and all 67 source-derived wire upload transactions establish the
installed image. The theorem then composes finite admitted START, administrative
command, capture, read, retry, RELEASE, reuse and reset/reload histories. It also
allows deselected padding and repeated physical cold interruptions inside
request or response frames. Every sampled pin edge clocks the controller and
the corresponding owned source execution.

One ordinary `Transfer.State` is carried throughout. START allocates from its
current sequence; RELEASE frees that same owned result; reset acts on the exact
source buffers reached at the reset cut, advances the logical epoch and resets
the local sequence. A numeric offset relates the ordinary logical sequence to
the finite hardware transfer counter after warm reset.

The theorem takes concrete wire-frame and actual admission witnesses. It does
not assume execution agreement, successful peer behavior, preserved startup
memory, or a preinstalled image. A separate inhabited witness,
`SerialSessionWitness.initialized_two_logical_rounds`, derives two actual START
guards and retained timeouts after the full wire upload. It ends with logical
epoch `previous.epoch + 1`, next sequence `3`, hardware transfer `2`, generation
`1`, and a reusable installed/free/available state. No supplied VALID,
completion, retention or image-equality premise is needed for that witness.

## Closed proof targets

All names below are under `Pinwheel.Hardware.Buffered`.

| Target | Main checked statements | Conditions and scope |
| --- | --- | --- |
| All eight buffered operations | `GenericStart.start_related`, `Refinement.related_step`, `Refinement.RelatedSram.run` | Arbitrary certified program and raw digital history; independent static layout/encoding certificate, actual installed SRAM and admitted START. |
| Initialized reactive I²C | `I2cSimulation.initialized_run`, `I2cCanonicalUpload.cold_result`, `SerialUpload.initialized_exists` | Fixed four-byte source, 270 virtual instructions in 50 stored rows; canonical loading derives VALID from arbitrary startup arrays/Q. |
| Reuse, reset and ownership | `LogicalSession.Mixed.trace_result`, `LogicalWire.Trace.session` | Ordinary allocation/release/reset carried across finite histories; completed rounds require actual retention; arbitrary execution prefixes may instead be aborted. |
| Sampled serial composition | `LogicalWire.Interrupted.initialized_session`, `SerialSessionWitness.initialized_two_logical_rounds` | One actual pin recurrence, exact frozen receipts/read samples, retries, idle gaps, warm/cold reload, repeated interior-frame cold aborts. |
| Timing extension | `I2cTiming.initialized_run`, `I2cTiming.initialized_reuse`, `I2cTiming.Upload.cold_installed`, `.warm_installed` | All 65,536 pairs of duration/budget fields from 0–255 at the typed source/core/SRAM boundary; canonical loading, arbitrary raw histories and admitted finite reuse. |

The eight operations are DRIVE, SHIFT, KEEP, HALT, FAULT, WAIT, CHECKED and
QUALIFY. CHECKED includes sequential, jump and branch finishes. The generic
certificate contains finite encoding, geometry, coordinates and successor
conditions; it contains no step, trace or observation-agreement assumption.
It does not assert that every syntactically valid program fits the physical
64-row/16-descriptor representation.

The relation covers levels/enables, physical and virtual execution position,
nested counters, countdown/deadline state, scratch, sampler timing while running,
full shifted TX payload, consumed TX count, packed RX prefix, identity, generation,
and retained completion/fault/timeout. It includes ready-at-deadline priority,
QUALIFY blocking, terminal capture before branch, immediate faults and
consume-before-append overflow ordering.

Timing fields encode cycles minus one: field 0 means one cycle and field 255
means 256. The public Python constructor still requires phase cycles at least
3 and wait cycles at least 4. The symbolic timing extension covers the typed
core/SRAM execution and reuse; the complete sampled-wire session specializes
the original fixed timing source.

## Validation

The fresh library build passed all 470 jobs without warnings. All 468 production
modules are reachable from the default import. The whole-environment audit
checked 32,803 declarations and 18,484 theorems, including private declarations
and proof-bearing definitions; only `propext`, `Classical.choice` and
`Quot.sound` were accepted. An injected custom axiom was rejected for the
expected reason. The complete foundation gate passed all 64 executable suites,
one kernel suite and both independent Python oracles. Its 71 recorded command
outcomes were as expected, including the deliberate axiom rejection. The
snapshot driver verified all 598 listed inputs against the selected commit.
The gate took 2,554.112 seconds (2,558.076 seconds including snapshot closeout).

The new executable controls passed four independent START cases and three
rejected semantic mutations; 43,264 source/circuit prefixes across 13 fixtures
and all 256 four-sample histories; and six serial source-boundary controls over
4,309 sampled edges with three ordinary actual-package comparison boundaries.

The final Python regressions passed: 1,151 tests, six skipped, in 51.723 seconds
(52.211 seconds including receipt verification), with all 323 Python inputs
bound to the committed source before and after execution.
The six skips require unavailable pinned Icarus/Yosys/SRAM fixtures or Linux
process/thread observation. They supply no RTL evidence for this milestone.

Fresh committed producers matched the independent Python lowerer for 25
supported timing pairs across nine image fields. Four byte-field mutations
and four below-bound public timings were rejected. This took 138.979 seconds
and covered 147 committed inputs. This finite compiler check is separate from
the all-parameter symbolic Lean theorem.

The final initialized-wire control passed in 1,953.383 seconds: 56,003
sampled edges, 68 upload transactions including rejected/repaired COMMIT,
three retained outcomes with RELEASE/reuse, and six ordinary actual-package
comparison boundaries. Its fresh committed dependency closure built all 141
jobs, with 145 listed inputs verified before and after execution. The driver
records and checks Lean 4.33.1; a deliberately wrong version was rejected before
build or execution.

Independent proof review found no remaining blocker in the static certificate,
START causality, carried allocation, pre-capture receipt cut, reset epoch/offset,
or interior-frame abort composition. Review added a physical CS-high padding
event so gaps between transactions are represented explicitly.

The initialized native control starts with unrelated patterned SRAM replicas
and Q values, sends all requests as 160 sampled bits, and reads complete
192-bit MISO responses. It omits one nonzero ACK dictionary entry to check a
rejected COMMIT, repairs it, checks both live SRAM replicas, all metadata and
dictionary entries, and preserves arbitrary physical tail cells. It then
checks retained guard fault, timeout and synthetic digital completion against
ordinary source operations, including RELEASE/reuse and the full payload's
unused high bits. Its expected receipt is packed independently from the numeric
ABI at the pre-capture cut.

Review corrected the test's synthetic success stimulus: the repeated START
requires both inputs high early enough to reach the pre-edge second sampler
stage. The corrected stimulus uses only the independent source program/state;
a source-only witness completes 24 TX bits and 32 zero RX bits, and the old
stimulus fails that same outcome check. No source or circuit behavior changed.
The obsolete first full attempt was intentionally stopped with SIGINT after
that review; its failure receipt and stop reason are preserved separately.

## Immutable evidence

The [evidence manifest](evidence/digital-session-20261017/manifest.json) records
full receipt hashes, historical commit membership, local log directories and
the preserved intake patch hash. All 915 distinct inputs listed by accepted gates
matched both the working tree and committed `1658c56` at export. Every receipt's
listed inputs were also checked against its own historical commit.

| Accepted gate | Source commit | Receipt SHA-256 |
| --- | --- | --- |
| [Fresh foundation](evidence/digital-session-20261017/foundation.json) | `6926de3` | `b09696ee9de6f7e74a0cb10773344dc508f9b2cf2c23943853cdd305314c074e` |
| [Initialized native](evidence/digital-session-20261017/initialized-native.json) | `1658c56` | `ebd3b72856d3216ceafdc444b929e8fa7f5050677e9a9a8a0881a9521bdaab59` |
| [Timing conformance](evidence/digital-session-20261017/timing-conformance.json) | `6225b43` | `c310bd5dc70a7417bc9d4aadb73e70c8f85af089a684b7600909a63d4c667222` |
| [Python regressions](evidence/digital-session-20261017/python.json) | `1658c56` | `f87c2d9080a860f66eb731457e9a904a4aab26833a8515b45e98cf8095d195ed` |

The complete foundation archive was reproduced with SHA-256
`703ffef819ea773a0b3a2d46ea5818fadf9de97dda1b4198aa05145b2aca7606`.
The manifest separately identifies the obsolete stopped native attempt, the
corrected preliminary pass and the expected wrong-toolchain rejection. These
historical records retain their original bytes and are excluded from the four
accepted gate receipts above.

## Counter and interface boundaries

Hardware generation and transfer counters saturate at 65,535. Exhausted
transfer space rejects START. Warm reset preserves the wire transfer counter;
warm reset plus COMMIT consumes two generation values, so canonical warm reload
requires the previous generation at most 65,533. Exhausted warm reload remains
invalid. Cold reset clears wire counters and starts a new logical software
epoch; that epoch is a proof-level identity component and is absent from the
wire format.

Requests contain 160 bits and receipts 192. Request close, command dispatch
with rejection latching, and response capture are separate clock cuts. A receipt
freezes the pre-capture controller state while the engine advances on the
capture edge. Exact 192-bit reads release the frontend receipt. Short or
overlong reads retain it; retries restart from its most significant bit.
Accepted transport status does not imply a completed or successful I²C result.
Source receipt meaning identifies owned status, TX consumption, RX length/data,
pins, phase, scratch and identity fields. The exact 192-bit transport is tied to
the actual captured word; sampler/debug fields remain actual controller
diagnostics.

Wire OBSERVE exposes public indexed RX/status diagnostics; it does not check a
source read identity. The owned read interpretation applies to the currently
related owner, and matching RELEASE checks hardware generation/transfer.
No authorization or replay-protection property across cold reset is claimed.

Stopped-source samplers are abstracted because hardware continues sampling.
The next START is seeded causally from the actual controller's sampler stages
and old output pins. Declaring a short TX length does not erase unused high
bits of the physical 32-bit payload register.

## Remaining gaps

The fused session grammar covers well-admitted transfers, successful reloads
and owned administrative rejections. Free-state exhausted-START rejection and
failed exhausted warm reload have separate exact boundary proofs; they are not
fused events preserving an installed session. The result does not refine every
possible host request sequence or malformed frame history.

There is no universal termination theorem for arbitrary programs or raw input
histories. Complete/fault/timeout outcomes and partial results are related for
every finite execution prefix; admission of a completed round observes actual
retention. Explicit timeout and finite synthetic-success witnesses demonstrate
nonempty outcomes, without promising electrical peer progress.

The universal Python compiler, native emitter, emitted RTL, CIRCT, technology
mapping, analog timing, external-peer compliance and silicon remain separate
obligations. Native executable controls are finite compiler/evaluator checks,
not a proof of native compilation. No CAD was run.

The next priority is an artifact-specific interpretation theorem connecting the
emitted buffered serial/controller RTL to the typed recurrence, followed by
substitution into the session theorem. Acceptance should bind artifact hashes
and complete state/output/clock/memory-port inventories, check next-state and
output correspondence with an explicit projection for optimized state, compose
wrapper wiring and the digital SRAM contract, and reject mutations in dispatch,
capture, sampler, memory-port and receipt-bit behavior. The
[paired RTL interpretation](../storage/paired-rtl-interpretation.md) provides an
existing method for this separate bridge.

Existing source semantics, circuit definitions, RTL/ABI and historical physical
artifacts are unchanged. The two documentation files dirty at intake remain
untouched. All work is local; no push, PR or publication was performed.

## Review and reproduction

- [Authorized campaign and continuation rule](digital-session-refinement-plan.md)
- [Default proof entry point](../../Pinwheel/Hardware/Buffered/DigitalSession.lean)
- [Generic static certificate](../../Pinwheel/Hardware/Buffered/GenericCertificate.lean)
- [Generic actual SRAM refinement](../../Pinwheel/Hardware/Buffered/GenericSramSimulation.lean)
- [Initialized interrupted wire session](../../Pinwheel/Hardware/Buffered/LogicalWireAbort.lean)
- [Nonempty carried two-round witness](../../Pinwheel/Hardware/Buffered/SerialSessionWitnessLogical.lean)
- [Symbolic timing upload](../../Pinwheel/Hardware/Buffered/I2cTimingUpload.lean)

With Python 3.12+ and the repository Lean toolchain:

```sh
python3 -B scripts/check-foundation-snapshot.py --tag morning-foundation-review
python3 -B scripts/check-serial-initialized.py --tag morning-initialized-review
python3 -B scripts/check-buffered-i2c-timing.py --tag morning-timing-review
python3 -B -m unittest discover -s test -p 'test_*.py'
```

The snapshot drivers require their inputs to be committed. Ignored `build/`
logs and receipts remain inspectable in this worktree; use fresh tags to
preserve previous evidence when repeating these commands.
