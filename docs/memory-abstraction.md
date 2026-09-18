# Memory abstraction

This record owns the memory contract, its two structural implementations, the
view of the existing storage through it, the prefetch machine — the reference
machine written against a memory of latency one — the decoupled machine with
its structural backend and evidence, and the one-port machine with its
per-program rule. The contract and the machines are Lean proofs and one
executable suite; the decoupled backend is emitted and checked with the pinned
tools (`check-prefetch.py`) and compared once after routing. The
[storage study](storage-study.md) owns the implementation candidates, the
[primitive review](storage-primitives.md) the macro and latch facts, and
[research status](research/status.md) allocation.

## Question

Storage is 6,172 of the design's 6,233 register bits, flip-flops are 41% of the
routed control's cell area and hold repair another 14%, and the alternatives
(latches, an SRAM macro) differ from flip-flops in *when* a read returns, not in
what it returns. Every proof was written against about six hundred named
registers, so no alternative could be tried without redoing them. What is the
contract a memory satisfies, which implementations satisfy it, and can the
machine be written against the contract instead of the registers?

## The contract

`Hardware/Memory.lean`. A memory has `2^a` words of `w` bits, one write port and
`p` read ports. `Request` is what it sees on an edge: the write and every read
address. `spec a w p ℓ` is a `Timed.Component` whose state is the contents plus
`ℓ` outstanding results per port; a read observes the pre-edge contents (a write
and a read of the same word on one edge see the old word), and with latency
`ℓ ≥ 1` the observation is the oldest outstanding result and does not depend on
this edge's request at all.

- `write_same`, `write_other`, `write_disabled`: the write port.
- `observe_zero`, `observe_registered`: what each latency shows.
- `registered_refines`: an output register on a memory of latency `ℓ` is a
  memory of latency `ℓ + 1`. This is the law a registered read port appeals to.
- `read_untouched`: a latency-one read of a word no write touched since it was
  issued returns that word.

## Implementations

| Implementation | Module | Refines | Structure |
| --- | --- | --- | --- |
| Flip-flops | `Memory/Flops.lean` | `spec a w p 0` | One register per word, loaded under the decoded write enable; one balanced multiplexer tree per read port. Every word is a certified `Update` (`Flops.enables`), so a [gating plan](register-enables.md) can name it. |
| Registered ports | `Memory/Registered.lean` | `spec a w p 1` | The same words with an output register per read port: the model of a synchronous macro, or of flip-flops behind a register. |
| Latches | none | `spec a w p 0` | Registered write data and an enable pulse in the clock-low phase give the flip-flop array's edge-level behaviour; what changes is electrical (a half-cycle write path, a glitch-free enable), which this model does not see. |

Both refinements are generic in address width, word width and port count and
are proved once (`Flops.refinement`, `Registered.refinement`), with trace
equality corollaries. `test/Memory.lean` runs 400 requests through both against
the specification and confirms that latency one shows exactly the previous
edge's latency-zero read.

## The storage the design has, seen through the contract

`Storage/MemoryView.lean` changes no expression, so emitted RTL and its
read-back proofs are untouched.

- The atomic loader's image is two memories, `dictionary : Contents 6 64` and
  `indexMap : Contents 8 6`, plus two metadata registers. The upload cursor is
  their decoded write port: `tick_dictionary` and `tick_index` show a push at
  cursor `c` is a `Contents.write` to the dictionary when `c < 64` and to the map
  when `64 ≤ c < 320`, and `writes_exclusive` that never both.
- The instruction read is the composition of the two (`composite`,
  `read_composite`), and the scheduler's current and successor reads are two read
  ports of the selected bank's composite memory at the current and target
  addresses (`Machine.reads_correct`).
- The selected general backend's 32 dense words per bank step as
  `Memory.Flops 5 55` under the port "bank write, cursor below 32, low cursor
  bits, compressed word" (`Backend.next_dictionary`), and its structural
  registers follow (`word_registers`).

So the machine that was routed is, in this vocabulary, the reference machine
against four memories of latency zero and two read ports.

## The prefetch machine: the machine against latency one

`Storage/Prefetch.lean`. The scheduler enters an instruction's successor on the
edge that finishes it, and which successor it is can only be known on that
edge: the branch bit is a terminal capture of the pins on that same edge. A
memory of latency one cannot serve that read, which is the
[scheduling gate](storage-primitives.md#the-scheduling-gate) the primitive
review recorded.

The prefetch machine keeps the current-word cache and two more registers,
`fetched true` and `fetched false`. On every edge it computes the two candidate
addresses of the *next* edge — taken and untaken — from the next-state values of
the core and the cache (`candidate`; `candidate_correct` relates it to the
scheduler's own `candidateAddress`), reads both from the selected bank, and
registers the words. The edge that dispatches selects one with the branch bit.
No pin value enters the addresses, and no cycle is added.

- `request`: what the machine puts to the bank each edge — no write (the loader
  owns the write port) and both candidates on two read ports. `fetched_reads`
  says the two registers hold exactly what `Memory.spec 8 64 2 1` has pending
  after that request.
- `Prefetched`: while an image is committed, the fetched words are the active
  bank's words at this edge's candidate addresses. `Valid` adds the cache
  invariant.
- `feed_eq`: with an image committed and no commit on the edge, the selected
  word is the word the reference reads (`address_choice`). `step_eq`: otherwise
  the core resets on both sides.
- `selected_memory`: the bank read on an edge is the bank active on the next
  edge, unchanged — the loader never writes the selected bank and a commit
  writes nothing. So a commit refills the fetch from the newly selected bank on
  the commit edge, and initialization owes nothing until the next commit
  (`initialize_valid`).
- `machine_next`, `valid_next`, `refinement`, `trace_correct`: the prefetch
  machine refines the atomic reference machine edge for edge, with every
  existing output, for every request and input history.

`test/Memory.lean` runs it closed-loop against the reference: the I²C write
with ACK, address NACK and data NACK, the register read for three bytes, UART
and SPI, a start on the edge right after a halt, a second image staged around a
run (pushes during the run are rejected as busy) and committed after it, resets,
rejected commands — 5,161 edges, 12 transactions, 24 taken branches, no
difference in control, core or probed outputs. Reading only the untaken
candidate would diverge at the first taken branch (the address NACK's branch to
STOP); the [one-port machine](#one-read-port-the-per-program-rule) below reads
the taken candidate on the following edge instead, under a rule on programs.

### What the review's obligations become

| Obligation in the primitive review | Here |
| --- | --- |
| Define latency, retained outputs, simultaneous read/write | `spec`: read-first, latency `ℓ`, outputs independent of the request when `ℓ ≥ 1` |
| Prefetch both branch successors before terminal capture | `Prefetch`, proved for every input history |
| Dependent map and dictionary accesses | The prefetch reads the composite once, as one latency-one read: structurally the map or the dictionary must stay combinational, not both registered |
| Ports or buffering under the same clock contract | Two read ports on the selected bank (or two copies), the same edges, no added cycle; or one port under the per-program `Ready` rule below |
| Reset and commit invalidate pending reads; atomic replacement | `initialize_valid`, `selected_memory`, `machine_next` |

## The decoupled machine and its structural backend

The prefetch machine's addresses are the canonical candidates of the next state.
Built structurally (`Storage/PrefetchBackend.lean`, first form), that puts the
fetched registers at **103** gate levels: the address waits for the next-state
decode, which includes the fetched word's validity check, so the loop is as long
as before, only moved. The fix is to compute the addresses from what the
scheduler *decides* on the current edge — whether it dispatches (`advancing`,
`dispatching`), the target — and from the fields of the word being entered,
which is a fetched register. When the machine is about to stop, the addresses
are irrelevant and may be anything. The `start` edge, on which nothing has been
fetched, is served by a **start-word register** loaded on commit with word 0 of
the newly selected bank.

`Storage/Decoupled.lean` is that machine. Its invariant asks the fetched words
to be the canonical candidates only while running, and the start word to be
word 0 while an image is committed. The crux is `step_structure`: on an edge
that keeps the machine running, a dispatch enters the successor at the target
with a mode of 3 exactly for a `checked` word, and no dispatch keeps the address
and the mode; `candidate_correct` then says the decoupled candidates equal the
canonical ones of the next state whenever the machine keeps running.
`refinement`, `trace_correct` and `initialize_valid` are as for the prefetch
machine. The decision and the candidates also exist as scheduler expressions
(`dispatchingExpr`, `candidateExpr`, with `_correct` lemmas) for the netlist.

`Storage/PrefetchBackend.lean` is its netlist on the selected general backend:
the same dense dictionaries, index maps, loader and scheduler, plus two
fetched-word registers and the start word (610 fields, 6,425 bits). Three
shared wires — the fed successor (a fetched word chosen by the branch bit while
running, the start word at rest), and the two candidates — and each dictionary
read addressed by a wire. `netlist_next` and `netlist_output` prove every
register and output step equals the functional dense machine; `reference_next`
projects it onto the decoupled machine; `completeRefinement` and `trace_correct`
reach the atomic reference with the capacity contract. `PrefetchEmit.lean`
emits it alone and behind the [pin sampler](pin-sampler-study.md)
(`sampled_trace_correct`).

### Structural levels

`structure_report` (`test/Structure.lean`, variant `prefetch`), `Cost.gates`,
register launch family, latest arrival:

| Endpoint | Composed control | Prefetch, next-state candidates | Decoupled |
| --- | ---: | ---: | ---: |
| Core state | 91 | 57 | 59 |
| Cached word enable | 99 | 65 | 36 |
| Cached word | 101 | 67 | 38 |
| Fetched words | — | 103 | **63** |
| Start word | — | — | 56 |
| Deepest register endpoint | **101** | 103 | **63** |

Stages of the decoupled loop, register family: fed successor 18, dispatch
decision 33, target 22, candidates 35, fetched words 63. From the `incoming`
family the deepest endpoint falls from 99 (cached word) to 60 (fetched words);
from `command`, from 87 to 50. Levels are ordinal: about a third of a routed
path is wire and buffering, and equivalent RTLs differ by 0.6–2 ns after
place-and-route. The model says the recurrence is shorter by roughly a third;
only a routed run says by how many nanoseconds.

### Evidence on the emitted netlist

`test/Memory.lean` runs the decoupled machine on the same closed-loop scenario
as the prefetch machine, plus a start on the edge right after a halt: 5,161
edges, 12 transactions, 24 taken branches, no difference. `scripts/check-prefetch.py` emits the backend, exports RTL
for both emissions, proves RTL/generic-gate equivalence of each, runs the
independent atomic-loader oracle on both — pins presented two edges early for
the sampled one, and rejected otherwise — and maps both corners. Receipt
`build/prefetch/prefetch-03/report.json`: 6,373 and 6,377 gate-equivalence
points, 35,824 oracle edges on each emission, 6,415 and 6,419 mapped flip-flops.
No Yosys sequential equivalence to the composed RTL is claimed: the register
sets differ and the equivalence rests on the Lean refinement.

Mapped screen, same recipe as the [sampled candidate](pin-sampler-study.md):

| Typical corner | Sampled candidate | Decoupled prefetch, sampled |
| --- | ---: | ---: |
| Standard-cell area | 547,995 µm² | 654,086 µm² (+19.4%) |
| ABC combinational delay | 6,803 ps | 5,815 ps (−14.5%) |
| Flip-flops / cells | 6,236 / 27,306 | 6,419 / 33,684 |

Slow corner: delay 9,945 → 9,269 ps (−6.8%). The area is the price of the
second read tree and the three registers: the cached backend reads the
dictionary once per edge (the successor at the target), the prefetch backend
reads it at both candidates and holds the words. Whether the shorter recurrence
survives placement and routing is the routed comparison below.

### Routed comparison

Two attempts under the [sampled candidate's](pin-sampler-study.md) fixed
contract — 20 ns clock, diagnostic 6×4 floorplan, four CPUs, 90-minute cap —
recorded in `physical/experiments/prefetch-physical-results.json`. Neither
reached routing:

| | `prefetch-sampled-01` | `prefetch-sampled-02` | Control under each overlay |
| --- | --- | --- | --- |
| Overlay | calibrated tolerant | calibrated, sampler, width-8 clock gating | `pin-sampled-02` / `combined-02` |
| Synthesized instances, area | 36,930, 663,713 µm² | 32,182, 618,435 µm² | 29,731, 568,196 µm² / 24,346, 507,042 µm² |
| After clock tree and repair | placement failed: 157 instances, 81.1% utilization | 40,878 instances, 728,416 µm², 80.7% | — / 31,482, 604,090 µm², 66.9% |
| Global routing | — | 858 congestion iterations in 84 min, no convergence, wall-time limit | — / 29 iterations |
| Extracted timing | none | none | +0.090 ns / −2.251 ns slow setup |

The second read tree and the three registers are the difference: about a
quarter to a third more instances at synthesis, a fifth more cell area after
repair, and at this floorplan that moves utilization from 67% to 81%, past
where the flow places and routes. The levels model said the recurrence is
shorter by a third; after routing that is neither confirmed nor refuted,
because at this floorplan area binds before logic depth does. The physical
question that follows is area — the one-port machine below returns the read
tree, a larger floorplan returns room — not the RTL's depth. The mid-PnR
typical setup slack of attempt 2 after repair (+5.92 ns) is a placement
estimate at one corner and is not used.

## One read port: the per-program rule

The two candidates of a word differ only for a branching `checked` record — a
record with mode 3 whose finish field is neither "continue" nor "always yes"
(`candidate_nonbranching`). So one port can serve both, on two edges:
`Storage/SinglePort.lean` reads the untaken candidate on the edge that enters a
word and the taken one on the following edge, unless that edge dispatches
again (`readTaken`, the `second` flag). The fed successor is the taken word only
for a branching current word with the branch bit set (`choose`); commit, start
word and the rest are the decoupled machine's.

What the machine cannot do is serve a branch on the edge right after entry:
the taken word is being read on that edge. A branching `checked` record with a
zero duration field could dispatch exactly then. The rule is on programs, not on
the machine:

```
Ready word := ¬(kind = 2 ∧ finish = 2 ∧ duration = 0)
```

checkable per word. `ReadyImages` says every word pushed so far is ready
(`PrefixReady`, kept by `ready_push`, `ready_commit`, `ready_next`), and
`read_ready` that every read of a committed image returns a ready word. The
invariant `Prefetched` holds the untaken word always, the taken word once
`second` is false, and when `second` is true and the current word is branching,
its duration has not been counted down, so it does not dispatch
(`branching_dispatch`). `valid_next` needs `Ready i.data` for the edge, and
`trace_correct` gives the edge-for-edge trace equality of the reference on every
input history whose data words are all ready — a refinement conditional on the
inputs, so it is stated on the traces (`trace_cons`) rather than as a
`Timed.Refinement`. The hypothesis is on every input word, addresses included;
that is stronger than the machine needs and the simplest thing to check, and
addresses, the idle word and the last-address word zero-extend below the finish
field, so only records can fail it.

Per program (`test/Memory.lean`, `readiness`): the I²C write and register read
at four-cycle phases, UART and SPI have no unready word; the I²C write at
one-cycle phases (`⟨0, 7⟩`) has one, the read three, the UART receiver
(`Compile.UARTRx.program`, any bit period) two. The one-port machine runs the
full closed-loop scenario with no difference — 5,161 edges, 12 transactions, 24
taken branches — and on the one-cycle-phase write it agrees while the address is
acknowledged and diverges on the edge the address NACK takes the unready branch
(`unreadyDiverges`).

What it buys: one read tree instead of two. The decoupled backend's extra area
is mostly the second read tree (the mapped table above); a one-port structural
backend has not been built, so no level or area figure is claimed for it — the
port's address would be a choice between the two candidates by `second`, one
more level on the candidate path. The rule is a compile-time obligation: the
compiled I²C programs satisfy it whenever a phase lasts at least two cycles, and
the receiver's two zero-duration branching records are a compiler question, not
a machine one.

## What the abstraction buys

A storage implementation is now a refinement of `spec`, proved once, generic in
size, and the machine's correctness against the reference is proved once against
a latency. Trying a registered dictionary — a macro, or flip-flops behind a
register to cut the successor loop — means implementing `spec 8 64 2 1`
structurally and building the prefetch machine's circuit, not re-proving the
loader, the cache or the scheduler. Clock-gating plans read enables off `Flops`
directly. The price of latency one is visible in the same model: the addresses
come from next-state values, so the path into the memory's address port grows by
the next-address decode, and the dictionary needs two read ports.

## Boundary

- The structural backend is flip-flop storage with two fetched registers: it is
  the reorganized loop, not a macro. No macro timing claim. The `Registered`
  model is not the vendor macro: read enables, bit masks, BIST and power modes
  are outside the contract. Two routed attempts reached no extracted timing —
  a placement failure at 81% utilization, then a global-routing wall-time
  limit at 81% — so the levels result has no routed confirmation; the
  comparison is negative by capacity at the diagnostic floorplan, not a timing
  result.
- The one-port machine is a Lean machine and proof; it has no structural backend
  or netlist yet. Its refinement is conditional on the `Ready` rule for every
  pushed word: programs that violate it — the UART receiver as compiled — are
  outside the claim, and the rule is checked per program, not enforced by the
  loader.
- The contract has no reset, no read enable and no write-first option. Each
  would be an addition, not a change.
- The composite read is latency one only if the address map or the dictionary
  stays combinational.
- The loader's write port is unchanged; a latch array still needs the write-phase
  obligation the primitive review states.

## Reproduction

```sh
lake build Pinwheel prefetch_emit structure_report
lake env lean -DwarningAsError=true --run test/Memory.lean
.lake/build/bin/structure_report build/structure/NAME      # prefetch.json
python3 scripts/check-prefetch.py --tag NAME               # needs the pinned hardware tools
```
