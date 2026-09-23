# Bounded compact execution comparison

Study dated **2026-09-22**, with physical follow-up **2026-09-23**.
**Retain paired-successor execution and its timing gains after the full coarse
reroute; repair the remaining electrical groups and diagnose congestion. Retain
the current chip as the control.** The first encoding below lost admitted
capacity and operations. That result rejected an encoding, not the organization.
The [full-capacity follow-up](#full-capacity-follow-up) restores those capabilities
with a larger SRAM and an explicitly costed parameter table. The
[complete controller](#complete-controller-and-macro-timing) now retains a 22.88%
mapped area saving after signal fanout repair. The subsequent
[physical-target comparison](physical-targets.md) retains 26.46% less placed area
after clock and hold repair. The [clock and status follow-up](physical-targets.md#clock-and-status-repair)
clears the clock fanout violations and raises status setup to +1.089 ns, with
positive hold and a 25.24% area saving. The [bounded coarse route](physical-targets.md#bounded-coarse-route)
then cuts overflow from the routed control's 1,310 to 41 with unchanged area and
passing pin access. Its complete coarse estimates expose setup, hold and signal
electrical failures. The [local repair](physical-targets.md#local-repair-with-coarse-wire-estimates)
clears those measured failures with +0.071 ns slow setup, +0.073 ns fast-screen
hold and 1.03% added area. The [whole-chip reroute](physical-targets.md#whole-chip-reroute-of-local-repair)
preserves positive setup/hold (+0.430/+0.082 ns), reduces overflow to 22 and passes
pin access. It exposes electrical failures on 27 signal nets; detailed routing
remains unadmitted while those branches and Metal3 congestion are addressed.
[Research status](research/status.md) owns allocation.

The **first prototype's** [receipt](../physical/experiments/compact-execution-results.json) records
18 passing tests, two explicit Lean schedule lemmas, four detected behavioral
mutants and an axiom-audit negative control. The complete local gate took
8.881 seconds. No current hardware source, RTL or physical design was changed.

## Candidate: store the two successors in one word

The existing hybrid uses two single-port SRAM replicas to return two possible
64-bit successors. The candidate uses **one existing 64×64 single-port macro**.
Each row holds two 32-bit operations: false successor low, true successor high.
Each operation contains a five-bit pointer to the row holding *its* successors.
There is no PC-to-dictionary map. Two atomic images occupy 32 rows each; removing
a read replica does not remove the inactive image. Row zero is a boot pair.
Commit reads it, immediate start uses its returned Q, and a saved start word
supports later starts after unrelated uploads.

| Phase | Work and availability |
| --- | --- |
| Before E+1 | Old Q holds both successors. Terminal capture selects a half; that entered operation supplies its successor-row address. |
| At E+1 | Latch the entered operation, pins and captures; the SRAM port samples that row address. |
| After E+1 | New Q holds both successors for the following dispatch. |
| Hold edge | Retain current operation and payload; renew its successor-row read. |
| Accepted upload | Write one inactive row, holding Q. Busy commands are rejected, preserving execution reads. |

Consecutive dispatches need no spare clock edge in this schedule. A physical
path remains: **SRAM Q → input-dependent half selection → row bits → SRAM
address**. Setup, hold, clock-to-Q and wire delay have not been measured.

## Format and behavior

The experimental word is `kind:3, levels:3, enabled:3, durationMinusOne:8,
argument:5, successorRow:5, flags:5`, least-significant field first. Its operations
are hold, shift-on-entry, capture-on-entry, branch, bounded wait, halt and fault.

- SHIFT consumes the eight-bit payload owned by the last accepted START. It
  drives one selected output from the old low/high bit and shifts right/left
  once on entry. UART uses low bits; SPI uses high bits. Holds never shift.
- CAPTURE selects one of 16 slots and either sampled input. A three-bit mask
  preserves selected prior output levels while others change: SPI retains MOSI
  while raising SCLK and sampling MISO.
- BRANCH supports entry and terminal captures with independent input pins but
  **one shared capture/branch slot**. Terminal capture precedes selection;
  successor entry capture follows it. General checked guards are absent.
- WAIT selects an input/level and uses the duration field as its timeout.
  Qualifying waits with a second counter are absent.

The model uploads all 32 rows plus six-bit idle metadata: 33 delivered 64-bit
words. It uses existing command numbers and the START payload transaction, but
the program representation is **not E64 wire-format compatible**. There is no
implemented host API, new emitter or serial protocol revision.

## Checks and their boundary

The packed-word clocked model in `scripts/compact_execution.py` is compared with
the existing independent E64 oracle and separate pin/edge formulas. Its `None`
power-up contents detect uninitialized reads; they are verification
instrumentation, not additional hardware state.

| Workload | Checked result |
| --- | --- |
| UART | All 256 bytes on one unchanged resident image; exactly 40 execution edges each. The reference uses a byte-specialized E64 program for each byte. |
| SPI mode 0 | 256 distinct TX/RX pairs covering every TX and RX byte, 68 edges each; rising-edge capture with decoy changes elsewhere. This is not all 65,536 combinations. |
| Consecutive branches | All 4,096 histories of six two-bit samples, plus 128 consecutive edges. Terminal input chooses the successor; entry capture then replaces the same slot from the other input. |
| Waits | Both input pins; budgets 0, 1, 7 and 255; every release time through the timeout boundary. |
| Ownership | Immediate/delayed start, inactive writes, six interrupted-upload positions with abort/reset/restart, malformed pushes, absent START, reset at every UART edge, retained results, overrun and simultaneous consume/arrival. |

The boundary is **delivered commands and already-sampled inputs**. No raw serial
frames or composed package wrapper are replayed. An absent START means no command
was delivered; the existing serial receiver still needs to establish that premise
for truncated frames. Unread-result backpressure remains a host rule: raw starts
may run and overflow the mailbox. Pin comparisons across payloads are protocol
comparisons, not equivalence for identical raw host-command histories.

Four mutants are detected: shifting on holds, replacing payload on busy START,
using stale branch samples, and requesting the previous operation's row. The
last mutant initially escaped UART: four-edge holds let the read catch up. The
final negative control exposes it on the second consecutive branch, confirming
why this workload belongs in the gate.

`test/CompactSchedule.lean` proves one-step and arbitrary finite dispatch-history
correspondence, assuming `Closed`: each encoded operation's row contains its
two encoded successors. Its compiled-environment audit includes generated
equational lemmas and rejects an injected axiom. This conditional **schedule
proof** does not prove the Python compiler, encoding, capture/payload, loader or
whole-chip refinement. It is isolated from the chip imports.

## Resource accounting and rejection

| Resource | Current hybrid | Paired-32 candidate |
| --- | ---: | ---: |
| Single-port 64×64 macros | 2 | 1 |
| Physical array bits, including atomic banks | 8,192 | 4,096 |
| Index-map register bits | 2,560 | 0 |
| Declared register bits, including wrappers | 2,901 | 250 |
| Macro reads per execution edge | 2 | 1 returning both halves |
| Delivered program upload words | 322 | 33 in a different format |

The current declaration count maps to 2,895 FFs, with six bits pruned. The
candidate's **250 is a logical width budget**, not a mapped FF count or area:
65 current/start/pending bits; 41 execution/pin/capture/payload bits; 21 loader/
metadata bits; and retained 12+76+35 sampler, receiver and result-wrapper bits.
Macro Q registers are inside the macro. Validation, shifting, selection, loader
decode, distribution, clock/hold repair and wires remain unmeasured. Reusing
wrapper bit counts does not prove wrapper composition or physical fit.

Pairing duplicates operations. Resident UART uses 11 rows / 704 meaningful macro
bits; SPI uses 18 / 1,152; the two-state branch graph uses three / 192. Halving
operation width does not halve occupied bits in these linear layouts. The
current dictionary reuses one record across many different program positions.

Two classes of retained counterexample prevent replacement:

1. **Capacity:** 32 repeated 256-edge actions followed by halt use two E64
   records and 33 logical addresses. The current model completes after 8,192
   edges. This compiler requires 33 paired rows including boot and rejects it;
   31 actions fit exactly. This is a concrete compiler/layout rejection, not
   optimality over alternate loop encodings or graph minimizers.
2. **Operations:** admitted E64 qualifying waits, checked guards and independent
   entry/terminal/branch slots lack representations. Splitting them into extra
   operations would need a new edge-preservation argument.

**First-prototype decision, superseded by the follow-up below:** retain the current engine and 43-buffer physical control; resume
costing the SRAM-only bit-41 buffering boundary. This candidate earns no synthesis
or routing. Preserve paired-successor scheduling as a useful result and resident
payload as an independent proposal; the latter still needs E64 encoding, proof,
integration and its measured budget. Reopening requires a concrete solution and
complete cost for the counterexamples, including added tables or counters.

## Full-capacity follow-up

The revised model uses **one available 512×64 single-port SRAM**, split into two
256-row atomic images. A row still supplies two 32-bit possible successors.
Each token contains `kind:3, levels:3, enabled:3, durationMinusOne:8,
parameterIndex:5, successorRow:8`; the upper two bits are reserved. Each bank has
32 **20-bit parameter entries in FFs**, plus a separate 32-bit boot token. Boot
metadata leaves every SRAM row available for an executable position.

The parameter fields recover independent entry and terminal captures, the
checked guard and branch sample slot, and qualifying-wait budget/guard. Branch
targets are represented by the successor tokens stored in a row. Entry capture,
terminal capture, branch choice and successor entry keep their original order.
The cached parameter is 20 bits and the renewed qualifying budget gets its own
eight-bit counter. SHIFT and KEEP additionally support the same resident-payload
UART/SPI workloads as the first model.

The compiler assigns a row to each logical position and projects each distinct
E64 record into at most one parameter. Thus a 256-position image with at most
32 distinct records needs at most 256 rows and 32 parameters. This argument
requires no repeat pattern or recovered loop. It also handles a full 256-word
image with 32 non-HALT records; an extra HALT dictionary entry is not required.
Targets beyond the original last address become explicit fault tokens.

The Python compiler implements that construction; a universal compiler theorem
is still open. Restored operation/capacity coverage is not compatibility with
identical raw E64 upload histories. The new format delivers 32 parameter words,
256 paired rows, one boot token and one idle word: **290 words**, followed by
commit. Parameters precede rows so validation can inspect their referenced
fields. Each row push validates both halves, requiring **two parameter read
ports**. Execution uses one of those ports. Busy commands cannot steal an SRAM
access or replace the running program's parameters or payload.

| Resource | Existing hybrid | Revised paired model |
| --- | ---: | ---: |
| Atomic images | 2 | 2 |
| Logical positions per image | 256 | 256 |
| Distinct canonical E64 records supported | 32 | 32 |
| SRAM organization | 2 × 64×64 replicas | 1 × 512×64 |
| Total macro area | 100,978.2656 µm² | 150,102.4032 µm² |
| Index-map FF bits | 2,560 | 0 |
| Parameter-table FF bits | 0 | 1,280 |
| Total declared FF bits, including wrapper budgets | 2,901 | 1,592 |
| SRAM reads per execution edge | 2 | 1 |

The larger macro costs **49,124.1376 µm² more** and is 191.34 µm high, compared
with 64.36 µm for each smaller macro; all are 784.48 µm wide. One macro removes
replica distribution but creates a larger contiguous routing obstruction.
Neither the state count nor that geometric observation establishes physical fit.
The declared total includes banked boot tokens, current token/parameter, two
counters, payload, captures, idle/loader controls and the retained sampler,
receiver and result-wrapper budgets. Macro Q storage is inside the macro.

There are two execution deadlines:

1. **SRAM Q → half choice → eight row bits → SRAM address.** The next row
   address bypasses the parameter table.
2. **SRAM Q → half choice → parameter lookup → entry state/capture.** This new
   combinational path must also finish before the same execution edge.

`test/PairedSchedule.lean` proves one-step and arbitrary finite dispatch-history
correspondence, including the cached parameter, under an explicit `Closed`
image premise. It assumes combinational FF-table reads and the synchronous
SRAM response schedule. It does not establish their physical delays or prove
the Python compiler, capture logic, loader or package. The compiled axiom audit
rejects an injected axiom.

The 18 focused model tests check all canonical entry/terminal capture descriptor
combinations and guards, all qualifying budget/guard encodings, full-capacity
irregular programs, renewed timeout behavior, independent branch/capture slots,
4,096 consecutive-branch histories, atomic interruption and malformed admission.
Six behavioral mutants are rejected. The former 8,192-edge capacity counterexample
now passes, as does a full 65,536-edge image that faults at its last-address
boundary. All 256 resident UART payloads and
256 SPI TX/RX pairs retain their independent pin expectations.

The six saved compiler fixtures also fit. The largest, I²C read, uses 155 logical
positions and 19 parameter entries. Independent peer checks cover 24 I²C cases
(10,349 execution edges), including stretching and NACK paths, and nine UART
receive frames, including invalid stop and false-start cases. Actual compiled
UART TX and SPI fixtures match the E64 state oracle for 40 and 68 execution
edges. These are sampled-input/delivered-command checks, not serial package RTL.

### Matched lookup cost screen

The [follow-up receipt](../physical/experiments/paired-execution-results.json)
binds the completed **122.269-second** gate. Both table sizes use the same generic
explicit word/decode/mux implementation, with two atomic banks, two independent
read ports and one write port. These are standalone table netlists, not the
actual current map or a complete emitted candidate. No assumed one-port saving
is used to hide the upload validator's second read.

| Standalone table measurement | 2 × 256×5 index table | 2 × 32×20 parameter table |
| --- | ---: | ---: |
| Mapped FFs | 2,560 | 1,280 |
| Mapped cells | 13,688 | 5,192 |
| Mapped area, either corner | 252,384.1740 µm² | 111,557.0988 µm² |
| Worst read arrival, typical / slow | 5.74 / 6.77 ns | 5.39 / 6.17 ns |
| Setup slack, typical / slow | +10.06 / +9.03 ns | +10.41 / +9.63 ns |
| Hold slack, typical / slow | +0.10 / +0.26 ns | +0.11 / +0.27 ns |
| Fanout-limit violations, either corner | 1,166 | 569 |

Each read arrival includes **4 ns of external input delay**. Both screens use
a 20 ns clock, 4/0.2 ns max/min input and output delays, a `buf_2` input driver,
0.010 pF output load, 0.2 ns uncertainty and 0.15 ns ideal-clock transition.
Slew/capacitance and pulse/period checks report no violations in this standalone
model. **Fanout is not closed.** Repair under the current chip's local eight-load
policy must be included in the complete comparison. These timing numbers exclude
SRAM arcs, branch/entry logic, clock distribution and wire parasitics, so they
do not resolve the existing chip's timing or establish the new chip's frequency.

The measured table saving is **140,827.0752 µm²**. After the larger macro's
**49,124.1376 µm²** premium, the table-plus-macro difference favors the revised
organization by **91,702.9376 µm²**. This is a component comparison; decoder,
admission, captures, package integration, electrical repair, clock/hold and
routing costs still have to fit inside that advantage. Do not subtract it from
the retained chip area and call the result a measured new chip.

All four saved mapped netlists pass independent arbitrary-state, two-valued SAT
checks of both outputs and every next-state bit, with exact FF-to-word coverage.
A joined-reader negative control fails as intended. The first injection changed
the JSON port but not its named wire; intake restored the old port and the gate
stopped. The corrected injection changes both, was checked separately, and was
then included in the passing complete rerun. The earlier failed attempts and
first compact receipt remain preserved. All four timing containers were
independently confirmed absent. The report binds 239 source hashes and 70
artifacts; all 205 current library sources remain unchanged. Nine local macro
views also match their pinned hashes.

**Decision at the component gate:** this is enough evidence to continue the architecture investigation.
Emit the complete revised controller and check its exact saved netlist against
these semantics. Apply the existing local electrical load policy, count all
controller/validation logic, then compose the larger macro arcs with both
execution paths. That result decides whether placement is justified. Keep the
43-buffer chip and bit-41 repair hypothesis as the control and fallback. Counted
loops and smaller SRAM layouts can follow a complete baseline; they are not
premises for this one. The complete-controller gate below now supplies that
missing evidence.

## Complete controller and macro timing

The [complete-controller receipt](../physical/experiments/paired-controller-results.json)
records a **63.291-second** gate for the opt-in
[`PairedController`](../Pinwheel/Hardware/Storage/PairedController.lean).
It emits actual typed Lean control and parameter state through the existing
netlist emitter, then reuses the existing sampler, serial receiver, pin map and
result observer. The wrapper binds one actual 512×64 SRAM. All 205 preceding
library sources remain unchanged; the new module is an experimental target.

Both atomic banks, the 290-word upload/admission path, boot/current state,
cached parameters, captures, counters and resident payload are included. The
parameter table has exactly two read ports. During upload, they validate both
successor tokens; during execution, the first supplies the entering operation.
The read indices are chosen independently of the admission result, avoiding
a combinational validation loop. The next SRAM row comes from the entered
token on a transition and the held token while waiting. This preserves the
one-read schedule without adding an execution edge.

Explicit combinational sharing matters to the implementation too. The first
expression-tree emission timed out at 120 seconds before producing RTL or
running CAD. Forty-five named `Netlist.letWire` bindings avoid repeatedly
traversing shared expressions; they add no registers. Final emission takes
2.637 seconds. Construction rejects duplicate, forward and missing references;
four injected invalid graphs confirm those checks.

### Independent checks and complete cost

The emitted core passes **173,359 edges**, including 116,811 compared with the
independent E64 state oracle, all 4,096 six-input branch histories, full-capacity
execution, waits, capture/guard combinations and atomic interruption. Independent
I²C peers cover 24 cases / 10,349 edges; UART receive peers cover nine frames.
Resident UART and SPI checks cover 256 payloads or TX/RX pairs each.

The complete package passes **331,401 pin edges / 1,517 serial frames** through
the actual existing sampler, receiver and mailbox. It exercises malformed and
partial uploads, repeated resident execution, capture pages, mailbox overflow,
consume/clear, running-command rejection, reset and replacement abort. The
saved typical mapped chip repeats all 331,401 pin edges with the pinned cell
and macro models. The I²C and completed UART receive peer cases above are core
checks; the package cases do not claim those complete peer waveforms.

Both saved mapped corners pass arbitrary-state, two-valued SAT comparison of
every output and next-state bit against the emitted generic chip, with SRAM Q
as an independent input. Intake checks every macro terminal and binds every
physical FF to typed state. It records 20 unused state positions: four boot
reserved bits and sixteen current-token bits. Six reserved bits appear as
literal `x` in Yosys; only those exact unused coordinates receive fresh unconnected
identities for the state census. No functional wire is rewritten. Unknown live
logic, lost/aliased FF state, changed terminals and changed package aliases fail
eight focused intake tests. The intake/graph checks take 3.159 seconds.

An axiom injection, an inverted mapped distribution buffer, and an SRAM request
deliberately driven from the stale current row are rejected. The latter fails
with a concrete core-state mismatch at edge 296. The compiled namespace audit
finds 463 declarations using only standard axioms. These checks do not prove
the emitter, compiler, loader or complete chip refinement in Lean.

| Complete mapped measurement | Optimized existing chip | Paired controller |
| --- | ---: | ---: |
| SRAM macros | 2 × 64×64 | 1 × 512×64 |
| Physical FFs | 2,895 | 1,572 |
| Standard-cell area, typical | 290,943.9540 µm² | 152,136.8352 µm² |
| Macro area | 100,978.2656 µm² | 150,102.4032 µm² |
| Total area, typical / slow | 391,922.2196 / 391,922.2196 µm² | 302,239.2384 / 302,246.4960 µm² |
| Setup slack, typical / slow | +13.50 / +10.52 ns | +8.53 / +3.93 ns |
| Hold slack, typical / slow | −0.58 / −0.86 ns | −0.61 / −0.90 ns |
| Fanout / slew / capacitance violations | 0 / 0 / 0 | 0 / 0 / 0 |

The comparison uses the exact retained `local-load-01` mapped chip and the same
eight-load mapping policy and pinned standard-cell libraries. It includes all
signal buffering: the final whole-chip pass adds three buffers beyond ABC's
load repair. Maximum signal sink count is eight. Pulse-width and period checks
also pass at both corners. The area saving is **89,682.9812 / 89,675.7236 µm²**,
or **22.8829% / 22.8810%**. This is now a complete mapped-chip result; clocks,
placed hold repair and routed wires remain uncosted.

### What the timing result identifies

Both chips use a 20 ns ideal clock, 4/0.2 ns max/min I/O delays, 0.2 ns clock
uncertainty, 0.15 ns clock transition and 0.010 pF output load. Unlike the earlier
standalone table screen, the new check includes actual macro timing arcs.
SRAM Q → SRAM address slack is **+12.59 / +8.04 ns**; SRAM Q → entry state
slack is **+13.09 / +8.81 ns**, across 69 exact entry-state endpoints.

The slow-corner global setup path is SRAM `A_DOUT[53]` through the shared
parameter selection and admission logic to `uo_out[4]`, the combinational
rejection status. It arrives at 11.87 ns against a 15.80 ns requirement, leaving
**3.93 ns**. The following reported setup paths end in boot-state FFs. The
shared validation/entry table has created a new timing tradeoff, even though
the execution row and entry paths still have margin. No false-path exception
is used; changing or excluding this path needs its own functional evidence.

The worst hold paths run directly from serial shift-register FFs to SRAM
`A_DIN`, including bits 0, 17 and 33. The slow example has 0.33 ns of FF delay
against a 1.23 ns requirement (1.03 ns macro hold plus 0.20 ns uncertainty),
leaving **−0.90 ns**. A smaller FF count does not repair that short path.
Clock arrival differences, intentional delay cells and wires must be measured
together. These results exclude wire parasitics and do not establish 50 MHz
operation after placement.

The report binds 262 source hashes and 78 artifacts; all were rechecked.
Both two-CPU, 2 GiB, network-disabled timing containers were independently
confirmed absent. The earlier emission timeout and strict-intake failure remain
preserved alongside the passing run. No placement or routing was launched.

**Decision:** the complete area saving and positive setup/electrical screen
justify one bounded physical comparison. First admit the exact saved netlist
and the larger macro's LEF, power and pin geometry. Then include placement,
clock distribution and hold repair, measuring total repaired area and both
execution paths plus the rejection output under the retained constraints.
Compare with the control at the same physical stage; the control's repaired
area cannot be compared directly with this unplaced area. Check access and
congestion around the larger contiguous obstruction before admitting any
detailed route. Keep the 43-buffer chip as control and its bit-41 repair as
fallback. Host integration of the experimental upload format and complete
Lean refinement remain separate obligations before promotion.

That physical gate is now recorded in [physical targets](physical-targets.md).
It preserves both source organizations and the mapped evidence above; its
comparison uses actual saved layouts at the same post-CTS/hold-repair stage.

## Reproduce

```sh
python3 -B -m unittest discover -s test -p test_compact_execution.py -v
lake env lean test/CompactSchedule.lean
python3 -B scripts/check-compact-execution.py --tag NEW_COMPACT_STUDY
```

The first two commands need Python and the pinned Lean toolchain. The full gate
also checks retained architecture, received-word and 43-buffer receipt hashes;
emits three model images and explicit counterexamples; runs the axiom negative
control; and verifies unchanged source inputs. Existing tags are refused.
It invokes no CAD tool or container.

For the revised study:

```sh
python3 -B -m unittest discover -s test -p test_paired_execution.py -v
lake env lean test/PairedSchedule.lean
python3 -B scripts/check-paired-execution.py --tag NEW_PAIRED_STUDY
```

The full revised gate requires the retained compiler images and receipts, pinned
local Yosys/Liberty files, and access to the already installed pinned Docker
image. Each subprocess is capped at 120 seconds. Each STA container uses two
CPUs, 2 GiB, a read-only mount and no network; it is removed and independently
checked. The model-only tests need Python; the schedule check needs pinned Lean.
Existing tags are refused. No placement or routing is launched.

For the complete emitted controller:

```sh
python3 -B -m unittest discover -s test -p test_paired_mapping.py -v
lake env lean --run test/PairedGraph.lean
python3 -B scripts/check-paired-controller.py --tag NEW_PAIRED_CONTROLLER
```

The main gate requires the retained paired-model and local-load receipts plus
the pinned local Lean/CIRCT/Yosys/Icarus/Liberty/macro tools. It uses the same
120-second per-command cap and two-CPU/2-GiB, network-disabled STA limits as
the component study, freezes inputs and refuses existing output tags. The
first two checks are cheap construction/intake controls and require no CAD run.
