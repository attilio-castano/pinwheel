# Memory abstraction

This record owns the memory contract, its two structural implementations, the
view of the existing storage through it, the prefetch machine — the reference
machine written against a memory of latency one — and the theory of **fetch
organizations** that grew out of it: a policy with a number of read ports as a
parameter, its correctness proved once, and the decoupled (three-port), two-port
and one-port organizations as instances, two of them with structural backends.
The contract, the theory and the machines are Lean proofs and one executable
suite; the backends are emitted and checked with the pinned tools
(`check-prefetch.py`), and the decoupled one was compared once after routing. The
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

`Storage/Dispatch.lean` holds what the scheduler decides on an edge, separated
from the decode of the word it enters. The crux is `step_structure`: on an edge
that keeps the machine running, a dispatch enters the successor at the target
with a mode of 3 exactly for a `checked` word, and no dispatch keeps the address
and the mode; `candidate_correct` then says the decision-based candidates equal
the canonical ones of the next state whenever the machine keeps running. The
decision and the candidates also exist as scheduler expressions
(`dispatchingExpr`, `candidateExpr` — an entered and a held half — with
`_correct` lemmas) for netlists. `Storage/Decoupled.lean` is the organization
itself: its invariant asks the fetched words to be the canonical candidates only
while running, and the start word to be word 0 while an image is committed. Its
refinement of the reference is an instance of the
[generic theory](#fetch-organizations-as-a-parameter) below.

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

## Fetch organizations as a parameter

Three machines had been proved against the same reference by the same chain of
lemmas, differing in three places: where the read addresses come from, what is
read on which edge, and why what the scheduler consumes is something already
read. `Storage/FetchPolicy.lean` makes that the definition.

A `Policy p σ` has registers `σ` and `p` read ports. It supplies the word fed to
the scheduler (`fed`, from the scheduler's inputs, its state and the policy's
registers — never the memory: that is latency one), the `p` addresses of an edge
(`address`) and its register update given the `p` words behind them (`step`).
The generic machine keeps the reference's control, core, memory and cached word,
and issues `request` — no write, the policy's addresses — to the selected bank's
composite memory; `reads` are its read ports (`Memory.Contents.reads`). The
number of read trees is `p` by construction: a policy cannot read what it has
not put on a port.

A policy is correct (`Correct`) when it supplies an invariant, possibly a rule on
inputs, and three facts:

| Obligation | Statement |
| --- | --- |
| `covers` | on a dispatching edge, with an image committed and no commit, the fed word is the word the reference reads |
| `preserved` | the invariant survives an edge whose input satisfies the rule |
| `initial` | initialization establishes the invariant |

From these, once: the scheduler steps as the reference's (`step_eq` — a dispatch
is covered, and without one the successor is not consulted,
`Dispatch.step_successor_irrelevant`), control, core and memory follow the
reference (`machine_next`), the cached word stays valid (`cache_valid_next`),
and the machine refines the atomic reference edge for edge on every history
satisfying the rule (`ruleRefinement`, `trace_correct`; `refinement` when there
is no rule). `Hardware/TimedRule.lean` is the general notion: a
`RuleRefinement` asks the rule of the step only — observations agree whenever
states are related — composes below an unconditional refinement (`transRule`),
and gives trace and pair-trace equality on histories whose consumed inputs
satisfy the rule.

Two-candidate policies share more. `canonical m current b` is the word consumed
at the next dispatch if the branch bit is `b` (word 0 at rest), and
`reference_word` says the reference reads `canonical … (branch bit)`; `read_next`
says a read at a decision-based candidate is the next state's canonical word,
`stay` that the canonical words do not move without a dispatch, and
`start_word_next` carries a start word loaded on commit. A rule on program
words is carried by the loader, generically in the rule (`Storage/ImageRule.lean`:
every word of a committed image, and every word pushed so far, satisfies it).

| Organization | Ports | Rule | Obligations | Backend |
| --- | ---: | --- | --- | --- |
| `Decoupled` | 3: both candidates, word 0 | none | about 40 lines (the hand-written proof was about 190) | `PrefetchBackend`, routed attempts above |
| `TwoPort` | 2: word 0 shares port 0 on commit edges | none | 63-line file; `covers` is `Decoupled`'s | none yet |
| `SinglePort` | 1: untaken on entry, taken on the next edge, word 0 on commit | `Ready` | below | `OnePortBackend`, below |

Making the ports a parameter showed what the routed backend spends: its start
word is a *third* read tree. A commit edge resets the scheduler, so nothing read
on it is consumed as a candidate, and the start word can use a candidate's port
then; `TwoPort` is that organization, written as the test of the abstraction — a
new organization should be an instantiation, not a rewrite. `Decoupled` keeps
its flat `State` and `next`, the form its backend is proved against;
`next_toPolicy` identifies them with the generic machine, and the emitted
backend is byte-identical to the validated one. `test/Memory.lean` runs all four
machines on the closed-loop scenario: 5,161 edges, 12 transactions, 24 taken
branches each, no difference.

The theory's edge: it is edge-for-edge. An organization that adds a cycle — a
stall on a taken branch — is not an instance; `Timed.Refinement` has no
stuttering. A memory of latency two is a different `fed` discipline, not
attempted.

### One read port: the per-program rule

The two candidates of a word differ only for a branching `checked` record — a
record with mode 3 whose finish field is neither "continue" nor "always yes"
(`Dispatch.candidate_nonbranching`). So one port can serve both, on two edges:
`Storage/SinglePort.lean` reads the untaken candidate on the edge that enters a
word and the taken one on the following edge, unless that edge dispatches
again (`readTaken`, the `second` flag), and word 0 on a commit edge. The fed
successor is the taken word only for a branching current word with the branch
bit set (`choose`).

What the organization cannot do is serve a branch on the edge right after entry:
the taken word is being read on that edge. A branching `checked` record with a
zero duration field could dispatch exactly then. The rule is on programs, not on
the machine:

```
Ready word := ¬(kind = 2 ∧ finish = 2 ∧ duration = 0)
```

checkable per word, the policy's `Rule`, carried as `ImageRule.Images Ready`.
The invariant holds the untaken word always, the taken word once `second` is
false, and when `second` is true and the current word is branching, its duration
has not been counted down, so it does not dispatch (`Dispatch.branching_dispatch`,
`dispatch_entered`). `covers` is where the rule is used, and nowhere else: a
dispatch out of a branching word happens with its taken word fetched. The
hypothesis of `trace_correct` is on every input word, addresses included; that
is stronger than the machine needs and the simplest thing to check, and
addresses, the idle word and the last-address word zero-extend below the finish
field, so only records can fail it.

Per program (`test/Memory.lean`, `readiness`): the I²C write and register read
at four-cycle phases, UART and SPI have no unready word; the I²C write at
one-cycle phases (`⟨0, 7⟩`) has one, the read three, the UART receiver
(`Compile.UARTRx.program`, any bit period) two. On the one-cycle-phase write the
machine agrees while the address is acknowledged and diverges on the edge the
address NACK takes the unready branch (`unreadyDiverges`). The rule is a
compile-time obligation: the compiled I²C programs satisfy it whenever a phase
lasts at least two cycles, and the receiver's two zero-duration branching
records are a compiler question, not a machine one — or the loader could reject
unready words at push, which would make the refinement unconditional again.

### The one-port backend

`Storage/OnePortBackend.lean` is the netlist on the selected general backend:
two fetched-word registers, the start word and the `second` flag (611 fields,
6,426 bits) behind **one** composite read of the selected bank. Three shared
wires: the fed successor, the port's address, and the word behind it, which
three registers load under their enables. The address is the entered word's
untaken candidate on a dispatch; else word 0 on a commit; else the current
word's taken candidate on the edge after an entry and its untaken one otherwise
— a commit edge does not dispatch (`FetchPolicy.dispatch_no_commit`), so the
dispatch decision, the deepest select, comes last and the address is no deeper
than the decoupled candidates. `netlist_next`, `netlist_output` and
`reference_next` are as for the decoupled backend; `completeRefinement` is a
`RuleRefinement`, and `trace_correct` reaches the atomic reference with the
capacity contract on ready programs. `OnePortEmit.lean` emits it alone and
behind the pin sampler; `sampled_trace_correct` uses `PinSampler.delayed_data` —
the pipeline never touches host ports, so the delayed history is as ready as the
original.

`structure_report`, variant `oneport` (`build/structure/oneport-01`),
`Cost.gates`, register launch family:

| Endpoint | Composed control | Decoupled, 3 ports | One port |
| --- | ---: | ---: | ---: |
| Core state | 91 | 59 | 60 |
| Cached word | 101 | 38 | 38 |
| Candidate / port address | — | 35 | 35 |
| Fetched words | — | 63 | 65 |
| Start word | — | 56 | 65 |
| Deepest register endpoint | **101** | **63** | **65** |

The two levels are the enable muxes of the word registers. The start word moves
to the port's depth, where nothing waits for it.

`check-prefetch.py --variant oneport`, receipt `build/oneport/oneport-03/report.json`,
identities in `physical/experiments/oneport-results.json`: RTL/generic-gate
equivalence of both emissions, 6,508 and 6,506 points, with three-step induction
— the untaken-word register can skip a load for one edge, never two in a row,
and two steps leave 107 points unproven; the independent oracle on both
emissions, 29,898 edges each, in *ready mode* — the same generator with the UART
receiver exercise replaced by a register read and the terminal-capture branch
record given one cycle, and a check that no pushed word violates the rule. Two
rejections are required: the sampled RTL with unshifted pins, and the inner RTL
on the **unrestricted** vectors, whose programs include zero-duration branching
records — the rule is not vacuous at the RTL level.

Mapped screen, same recipe:

| Typical corner | Sampled candidate | Decoupled, 3 ports, sampled | One port, sampled |
| --- | ---: | ---: | ---: |
| Standard-cell area | 547,995 µm² | 654,086 µm² (+19.4%) | 576,805 µm² (**+5.3%**) |
| ABC combinational delay | 6,803 ps | 5,815 ps (−14.5%) | 5,272 ps (**−22.5%**) |
| Flip-flops / cells | 6,236 / 27,306 | 6,419 / 33,684 | 6,420 / 30,690 |

Slow corner: 9,945 → 8,343 ps (−16.1%). Two read trees are about 77,000 µm²; what
remains over the candidate is the three word registers, the address select and
the enables. Mapped figures are a screen: no placement, no wires. Under the
clock-gating overlay the sampled candidate stood at 67% utilization after
repair; five percent more cells would put this backend near 71%, inside the
range this flow has placed and routed (67–81%), where the decoupled backend's
81% before repair was not. No routed run of this backend exists yet.

## What the abstraction buys

A fetch organization is now a `Policy` with three obligations, proved against
a machine that is proved once: the decoupled organization's obligations are
about forty lines where the hand-written refinement was about a hundred and
ninety, and a new organization was a sixty-line file. The read ports are a
parameter the policy cannot cheat, so area accounting starts in Lean — which is
how the third read tree of the routed backend was found — and a condition on
programs has one place where it is used (`covers`) and one generic carrier
(`ImageRule`).

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
- The one-port backend is proved, emitted, checked at RTL level and mapped; it
  has no routed run. Its refinement is conditional on the `Ready` rule for every
  pushed word: programs that violate it — the UART receiver as compiled — are
  outside the claim, the rule is checked per program, not enforced by the
  loader, and its RTL regression runs on ready-mode vectors. `TwoPort` has no
  backend. The fetch-policy theory is edge-for-edge and latency one.
- The contract has no reset, no read enable and no write-first option. Each
  would be an addition, not a change.
- The composite read is latency one only if the address map or the dictionary
  stays combinational.
- The loader's write port is unchanged; a latch array still needs the write-phase
  obligation the primitive review states.

## Reproduction

```sh
lake build Pinwheel prefetch_emit oneport_emit structure_report
lake env lean -DwarningAsError=true --run test/Memory.lean
.lake/build/bin/structure_report build/structure/NAME          # prefetch.json, oneport.json
python3 scripts/check-prefetch.py --tag NAME                    # decoupled backend; needs the pinned hardware tools
python3 scripts/check-prefetch.py --variant oneport --tag NAME  # one-port backend, ready-mode vectors
```
