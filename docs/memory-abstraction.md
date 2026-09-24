# Memory abstraction

This record owns the memory contract, its two structural implementations, the
view of the existing storage through it, the prefetch machine — the reference
machine written against a memory of latency one — and the theory of **fetch
organizations** that grew out of it: a policy with a number of read ports as a
parameter, its correctness proved once; a backend parametric in the policy; the
decoupled (three-port), two-port and one-port organizations as instances, each
with a structural backend; and a rule on programs that can be assumed, enforced
by the loader, or proved of a compiler. The contract, the theory and the
machines are Lean proofs and one executable suite; the backends are emitted and
checked with the pinned tools (`check-prefetch.py`), and the decoupled one was
compared once after routing. The
[storage study](storage/storage-study.md) owns the implementation candidates, the
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
| Flip-flops | `Memory/Flops.lean` | `spec a w p 0` | One register per word, loaded under the decoded write enable; one balanced multiplexer tree per read port. Every word is a certified `Update` (`Flops.enables`), so a [gating plan](physical/register-enables.md) can name it. |
| Registered ports | `Memory/Registered.lean` | `spec a w p 1` | The same words with an output register per read port: the model of a synchronous macro, or of flip-flops behind a register. |
| Latches | none | `spec a w p 0` | Registered write data and an enable pulse in the clock-low phase give the flip-flop array's edge-level behaviour; what changes is electrical (a half-cycle write path, a glitch-free enable), which this model does not see. |

Both refinements are generic in address width, word width and port count and
are proved once (`Flops.refinement`, `Registered.refinement`), with trace
equality corollaries. `test/Memory.lean` runs 400 requests through both against
the specification and confirms that latency one shows exactly the previous
edge's latency-zero read.

The experimental SRAM binding uses mutually exclusive reads and writes and
holds Q during writes. `Memory/Sram.lean` gives this behavior its own contract,
reusing `Memory.Write`, `Memory.Request` and the word-update laws. Its replicated
physical states refine a partial model: a cell becomes defined when written,
and a registered response becomes defined when a read of such a cell completes.
The copies may have unrelated initial contents. `related_step` and `related_run`
preserve agreement on every defined value; `broadcast_write`, `write_holds_q`
and `read_defined` describe the interface. `bankAddress_ne` and
`inactive_write_preserves_active` establish bank separation for either address
width. These facts are independent of hybrid index maps and direct upload
expansion. `Storage/SramController.lean` now owns the expressions used by the
experimental emitter. Its hybrid request bridge proves accepted write enables,
address-port selection/truncation, selected-bank index reads, commit read enable,
broadcast initialization and active-bank preservation using this array contract.
These statements are about the core's actual expressions, with explicit input
and register interpretations. `Storage/SramCoverage.lean` now proves that the
accepted cursor covers the inactive dictionary before commit and preserves
initializedness through every command history after reset. Actual controller
control/request bridges connect that invariant to selected-bank read addresses
and defined physical responses. `Model.Defined` belongs to the generic memory
contract; the accepted-cursor invariant belongs to the storage adapter.
`Storage/SramContents.lean` strengthens initializedness with equality to the
existing loader image, preserved by accepted writes. `Storage/SramExecution.lean`
then closes the feedback loop: actual array Q feeds the shared controller,
its selected addresses return the expected program words, and its register
transitions and observations refine the capacity-adapted atomic machine after
one initializing edge. Arbitrary initial arrays and Q are allowed. The proof
reuses `Storage.Sram` and `TwoPort`; it adds no instruction semantics or duration
rule. Full chip-wrapper/Verilog binding and translation correspondence remain
separate. The direct controller does not inherit these hybrid-specific proofs.

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
read addressed by a wire. It is an instance of the
[policy-parametric backend](#the-policy-parametric-backend) below: the file
holds the fed word, the two wires and the three register updates, each proved
to mean the policy's, and every register and output step, the projection onto
the policy machine and the refinement of the atomic reference with the capacity
contract are the generic backend's. `PrefetchEmit.lean` emits it alone and
behind the [pin sampler](pin-sampler-study.md) (`sampled_trace_correct`).

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
| `TwoPort` | 2: word 0 shares port 0 on commit edges | none | 63 lines; `covers` is `Decoupled`'s | `TwoPortBackend`, below |
| `SinglePort` | 1: untaken on entry, taken on the next edge, word 0 on commit | `Ready` | below | `OnePortBackend`, below |

Making the ports a parameter showed what the routed backend spends: its start
word is a *third* read tree. A commit edge resets the scheduler, so nothing read
on it is consumed as a candidate, and the start word can use a candidate's port
then; `TwoPort` is that organization, written as the test of the abstraction — a
new organization should be an instantiation, not a rewrite. `test/Memory.lean`
runs all four machines on the closed-loop scenario: 5,161 edges, 12
transactions, 24 taken branches each, no difference.

The theory's edge: it is edge-for-edge. An organization that adds a cycle — a
stall on a taken branch — is not an instance; `Timed.Refinement` has no
stuttering. A memory of latency two is a different `fed` discipline, not
attempted.

### The policy-parametric backend

A fetch policy changes one thing about the backend: where the scheduler's
successor word comes from. `Storage/PolicyBackend.lean` makes that an input.
`core` is the selected general backend with the successor as a wire — dense
dictionaries, index maps, loader, scheduler, and the cached word, which loads
the fed word on a dispatch or at rest — proved once against the functional step
(`core_step`, `core_observe`: no output reads the fed word). A policy's
structural part is then a `Realization`: a netlist over the backend's registers
and the policy's that steps the backend as `core` fed the policy's word, steps
the policy's registers as the policy does, and shows `core`'s outputs.
`Realization.twoWires` builds one from the expression for the fed word, two
shared wires below it and the policy registers' next-state expressions, given
that the fed expression means the policy's `fed` and each register expression
means the policy's `step`. From a realization and the policy's `Correct`, once:
every register and output step (`netlist_next`, `netlist_output`), the
projection onto the policy machine (`reference_next`), the refinement of the
atomic reference with the capacity contract under the policy's rule
(`completeRefinement`, a `RuleRefinement`; the rule has to survive the capacity
check, `Rules.adapted`), the trace theorems, and — `Storage/PolicyEmit.lean` —
emission and the pin-sampler theorem for any rule the pipeline cannot disturb
(`sampled_trace_correct`, `PinSampler.delayed_rule`).

| Backend | Before | On the generic backend |
| --- | ---: | ---: |
| `PrefetchBackend` + emit | 379 + 48 lines | 135 + 38 |
| `OnePortBackend` + emit | 473 + 51 lines | 226 + 42 |
| `TwoPortBackend` + emit | — | 148 + 39, compiled at the first attempt |
| `PolicyBackend` + `PolicyEmit` | — | 515 + 62, once |

The re-based decoupled and one-port backends emit byte-identical MLIR to the
validated `prefetch-03` and `oneport-03`, alone and sampled, and their level
reports are unchanged (`build/structure/policy-01`).

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

checkable per word, carried as `ImageRule.Images Ready`. The policy's `Rule`
asks it of push commands only (`i.command = 2 → Ready i.data`), which is what
the loader's invariant needs (`ImageRule.push_command`). The invariant holds the
untaken word always, the taken word once `second` is false, and when `second` is
true and the current word is branching, its duration has not been counted down,
so it does not dispatch (`Dispatch.branching_dispatch`, `dispatch_entered`).
`covers` is where the rule is used, and nowhere else: a dispatch out of a
branching word happens with its taken word fetched.

**Assumed or enforced.** A rule on pushed words can be discharged the way the
small backend already discharges its capacity: by turning an inadmissible push
into a rejection. `Storage/Admission.lean`: `admit A` is that filter on the
command port, `admit_rule` says what survives it as a push is admissible, and
`discharge` turns any refinement conditional on "every push carries an
admissible word" into an unconditional one behind the filter
(`Timed.RuleRefinement.precompose`), against the reference behind the same
filter; on inputs that satisfy the rule the filter is the identity
(`admit_of_rule`). `SinglePort.admitted` and `Backend.OnePort.admitted` are the
instances. The backend's capacity check *is* such a filter, by definition
(`adapt i b = admit (Small.capacity cursor) i`, by `rfl`), which is how the
rule is shown to survive it. Since the 2026-09-19 consolidation,
`AdmissionNetlist` realizes the generic filter and `OnePortAdmission` supplies
the readiness predicate in the result-enabled chip. The historical core
emissions and measurements below remain conditional on ready programs.

**Proved for the compilers.** `Storage/Readiness.lean` restates the rule on
instructions (`ready`), shows it is the word-level rule through the record
encoding (`ready_encode`, `ready_widen`), and carries it to every word the host
pushes for an image — dictionary, addresses, idle pins, last address
(`upload_ready`; `Loader.ProgramImage` owns the stream and `test/Memory.lean`
loads it). `Compile/Readiness.lean` now owns the compiler certificates: for every
request and configuration the compiled I²C write and register read are ready
whenever a phase lasts at least two cycles (`i2c_write`, `i2c_read`); programs
of the original engine — UART and SPI transmission — always (`embedded`); the
UART receiver never (`uart_receiver`): it polls for the start bit with
one-cycle branching records, so under this organization it needs a two-cycle
poll, a different organization, or the filter's rejection. `readiness` in the
suite keeps the counts as a cross-check — no unready word in the four fixtures,
one and three in the one-cycle-phase I²C programs, two in the receiver — and
`unreadyDiverges` shows the machine leaving the reference exactly on an unready
taken branch.

### The one-port backend

`Storage/OnePortBackend.lean` is the realization on the selected general backend:
two fetched-word registers, the start word and the `second` flag (611 fields,
6,426 bits) behind **one** composite read of the selected bank. Three shared
wires: the fed successor, the port's address, and the word behind it, which
three registers load under their enables. The address is the entered word's
untaken candidate on a dispatch; else word 0 on a commit; else the current
word's taken candidate on the edge after an entry and its untaken one otherwise
— a commit edge does not dispatch (`FetchPolicy.dispatch_no_commit`), so the
dispatch decision, the deepest select, comes last and the address is no deeper
than the decoupled candidates. The file proves the fed word, the address, the
word and the four register updates mean the policy's; the rest is the generic
backend's, with the rule `i.command = 2 → Ready i.data`. `OnePortEmit.lean`
emits it alone and behind the pin sampler.

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
— two steps leave 107 points unproven, three and five prove all, and the cause
was not isolated; the independent oracle on both
emissions, 29,898 edges each, in *ready mode* — the same generator with the UART
receiver exercise replaced by a register read and the terminal-capture branch
record given one cycle, and a check that no pushed word violates the rule. Two
rejections are required: the sampled RTL with unshifted pins, and the inner RTL
on the **unrestricted** vectors, whose programs include zero-duration branching
records — the rule is not vacuous at the RTL level.

Mapped screen, same recipe, all three organizations:

| Typical corner | Sampled candidate | Decoupled, 3 ports | Two ports | One port |
| --- | ---: | ---: | ---: | ---: |
| Standard-cell area | 547,995 µm² | 654,086 (+19.4%) | 618,244 (+12.8%) | 576,805 (**+5.3%**) |
| ABC combinational delay | 6,803 ps | 5,815 (−14.5%) | 5,027 (**−26.1%**) | 5,272 (−22.5%) |
| Slow-corner delay | 9,945 ps | 9,269 (−6.8%) | 8,150 (−18.1%) | 8,343 (−16.1%) |
| Flip-flops / cells | 6,236 / 27,306 | 6,419 / 33,684 | 6,419 / 32,705 | 6,420 / 30,690 |
| Rule on programs | none | none | none | `Ready` |

A read tree is about 36,000–41,000 µm²; what remains over the candidate for one
port is the three word registers, the address select and the enables. Mapped
figures are a screen: no placement, no wires. Under the clock-gating overlay the
sampled candidate stood at 67% utilization after repair; five percent more cells
would put the one-port backend near 71% and thirteen percent the two-port one
near 75%, both inside the range this flow has placed and routed (67–81%), where
the decoupled backend's 81% before repair was not. The one-port backend then
routed at 69.2%.

### The one-port backend, routed

One run, `oneport-sampled-01`: the one-port backend behind the sampler under
`physical/experiments/combined.json` (calibrated RC, width-8 clock gating), the
overlay of the same-overlay control `combined-03`; 20 ns clock, unchanged I/O
constraints, diagnostic 6×4 floorplan, four CPUs. Two departures from the
earlier contract, neither touching the result: a 150-minute cap instead of 90
(the control needed about 105 minutes of flow in two runs), and no stop after
`OpenROAD.STAPostPNR`, so the flow went on into layout checks. Identities and
numbers in `physical/experiments/oneport-physical-results.json`.

| Slow corner, extracted | `combined-03` (control, same overlay) | `pin-sampled-02` (no gating) | `oneport-sampled-01` |
| --- | ---: | ---: | ---: |
| Worst setup slack | −2.251 ns, 40 endpoints | +0.090 ns | **−0.187 ns**, 9 endpoints |
| Register-launched family | −2.054 ns | +0.090 ns | **−0.053 ns**, 3 paths |
| Loader command family | −2.251 ns | +0.175 ns | +0.473 ns |
| Loader data family | +0.116 ns | +1.996 ns | −0.187 ns |
| Protocol pins | +14.496 ns | +14.354 ns | +14.506 ns |
| Hold, slow / typical / fast | +0.539 / +0.232 / +0.059 | +0.422 / +0.194 / +0.052 | +0.361 / +0.168 / +0.054 |
| Functional cell area, utilization | 608,058 µm², 67.4% | 732,103 µm², 81.1% | 624,825 µm², 69.2% |
| Routed wire | 1,753,794 µm | 1,792,141 µm | 1,663,828 µm |

Routing finished with zero violations after 51 passes, and the flow ran to
its end: Magic DRC, LVS and the antenna check pass with no error — the first run
of this design to finish them — and its only deferred error is the slow-corner
setup miss. Typical and fast setup are met (+5.730, +8.602 ns); 10 slew and 20
fanout limit violations remain. The routed netlist passes the implemented-netlist regression on the
ready-mode vectors (29,898 edges, 4,903,194 output-bit comparisons, mutant
rejected).

What it says. Against the control under the same overlay, the shorter
recurrence survives routing: the register-launched family gains 2.0 ns and the
worst slack 2.06 ns for 2.8% more cell area and 5% less wire, and the path that
limited `combined-03` — the cached word's clock-gate enable, launched from the
command decode — is no longer limiting (+0.473 ns), as its fall from 99 gate
levels to 36 predicted. The worst register-launched path runs from `mode[2]`
through the dispatch decision, the port's address and the read tree into
`fetched_taken[52]` and `start_word[52]`: the endpoint the level model ranks
deepest (65). Against the ungated sampled candidate, this design is 0.28 ns
short of its slack with 14.7% less cell area at 69% utilization instead of 81%.

What it does not say. The slow corner is not closed: −0.187 ns. All nine
violating endpoints launch from `data[35]`, the loader's data port: the capacity
check rewrites the command from the data word, the commit decode reads that
command, and the commit select sits in the port's address. The
[command-split](storage/successor-fetch-study.md#command-decoder-experiment) form —
decode predicates the capacity check cannot change from the raw command —
removes that dependency and is not applied in `Backend.Policy.core` yet. One
run: equivalent RTLs have differed by 0.6 ns under this flow, so −0.053 ns and
+0.090 ns on the register family are not distinguishable, and no repeat was made.

### The two-port backend

`Storage/TwoPortBackend.lean`: the decoupled organization's registers and fed
word behind **two** composite reads. Port 0 reads word 0 on a commit and the
untaken candidate otherwise — the commit select sits beside the held candidate,
so the dispatch decision still comes last — and its word is a shared wire,
loaded by the untaken register on every edge and by the start word on a commit;
port 1 reads the taken candidate. No rule on programs: the refinement holds for
every input history. Levels (`build/structure/policy-02`): fetched words 63,
start word 65, core state 59 — the decoupled backend's.

`check-prefetch.py --variant twoport`, receipt `build/twoport/twoport-02/report.json`,
identities in `physical/experiments/twoport-results.json`: RTL/generic-gate
equivalence 6,501 and 6,511 points with two-step induction, and the independent
oracle on the **unrestricted** vectors, 35,824 edges on both emissions, the UART
receiver included. The first attempt (`twoport-01`) left 148 points unproven at
any depth, and showed a gap in the harness: synthesis narrows a word register
whose top bit is constant to 63 bits, Yosys then matches it to nothing, and a
start word that loads on commits alone cannot be recovered by induction. The
check now re-exposes narrowed registers at full width, constant zero on top, in
a copy of the gate netlist used only for the comparison. In `prefetch-03` the
two fetched registers had been left out the same way (6,373 points are 6,501
less their 128 bits); they reload every edge, so that comparison was sound, and
`prefetch-05` repeats it with every register matched.

### The command split in the generic backend

The routed one-port run named its own next step: every violating endpoint
launched from the loader's data port. The capacity check reads the pushed word
and turns an oversized push into a rejection, and `Backend.lift` puts that
rewritten command at every command leaf — so the commit decode, the start
decode and the bank selection behind them all wait for a 64-bit comparison on
the data port, although the check cannot change any of them
(`Small.adapt_command_predicate`). The
[command-split](storage/successor-fetch-study.md#command-decoder-experiment) form
decodes those predicates from the raw command. The composed control has had it
since that study (`BankSelect.lift`, proved equal to the plain lift at every
valuation); the policy backends had not.

`Backend.Policy` now lifts with `BankSelect.lift`: in the scheduler's inputs
(`feedW`), in the loader's own registers and outputs (`BankSelect.circuit`),
and in everything a policy builds its wires from (`liftC`: the commit decode,
the branch bit, the selected bank's registers). Three lemmas carry the proofs
over — `BankSelect.lift_correct`, `circuit_next_eq`, `circuit_output_eq` — and
none of the three policy files changed: all three backends inherit the form,
with their register layouts, ports and contracts as they were.

**The level model had said so.** The report for the backend that was routed
(`build/structure/policy-02`) ranked the data port into the fetched words at 71
gate levels, above the register-launched family at 65. That row was not read
before the run; the run then measured −0.187 ns from the data port and
−0.053 ns from registers. `check-structure.py` now prints, for every policy
backend, what the data port reaches and the deepest family and endpoint, and
fails if the data port reaches the fetch path (`build/structure/split-02`).

| One-port backend behind the sampler, latest arrival in gate levels | before | after |
| --- | ---: | ---: |
| data port → fetched words | 71 | no path |
| data port → core state, cached word | 61, 44 | no path |
| data port → loader control, dictionaries and index maps | 42, 32 | 41, 31 |
| loader cursor → fetched words | 65 | 50 |
| command → fetched words | 52 | 47 |
| registers → dispatch decision | 33 | 20 |
| registers → cached word, its enable | 38, 36 | 25, 23 |
| registers → fetched words | 65 | 64 |

The dispatch decision, and with it the cached word and its clock-gate enable,
lose thirteen levels: their deepest path had been the loader cursor through the
capacity check. The register family's deepest path into the fetched words —
branch bit, fed word, the entered word's candidate, the read — loses one. The
two-port and decoupled backends move the same way (fetched words 64 and 62).

**As a theorem** (`Storage/DataPort.lean`). With only the data port launching,
`Expr.arrival … = none` says an expression has no structural path from it. The
leaves hold by computation: each scheduler input of the loader in the split
form, the commit decode, the branch bit and the selected bank's registers
(`base_data_free`, `commit_lift_data_free`, `branch_lift_data_free`,
`chosen_data_free`); `plain_commit_sees_data` records that the plain lift does
not have the property. The rest is generic: any scheduler expression fed a
data-free successor (`sched_data_free`), the composite read at a data-free
address (`readAt_data_free`), and the generic backend's scheduler registers,
cached word and scheduler outputs (`core_data_free`, `core_output_data_free`).
For a two-wire realization whose four pieces are data-free (`DataFree`), no
register of the fetch path — scheduler, cached word, policy registers — has a
path from the data port (`DataFree.next`), so its next value is the same
whatever word the host presents (`DataFree.step_independent`, through
`Netlist.step_congr_of_arrival_none`). Each organization is an instance in a
few lines (`Prefetch.dataFree`, `TwoPort.dataFree`, `OnePort.dataFree`). A port
with its own arrival budget can no longer reach the loop by accident: a policy
that routed the data port into its wires would fail to prove `DataFree`.

Validation, `check-prefetch.py`, receipts `build/oneport/oneport-04`,
`build/twoport/twoport-04`, `build/prefetch/prefetch-06`; identities in
`physical/experiments/{oneport,twoport,prefetch}-split-results.json`. RTL/
generic-gate equivalence at the same induction depths as before (6,508 and
6,506 points for one port, 6,507 and 6,505 for two, 6,501 and 6,511 for the
decoupled backend; the counts move with the bits synthesis removes), the independent oracle on
both emissions of each (29,898 edges in ready mode for one port, 35,824
unrestricted for the others), and the same required rejections. One mapped
flip-flop count changed: the sampled two-port mapping keeps bits 3–8 of the
cached word, which synthesis had deleted as unread before (6,425 instead of
6,419; `twoport-03` stopped on that assertion with everything else passed, and
`twoport-04` records the new count). The register layout is unchanged; what
synthesis can show unread depends on the shape of the logic around it.

| Typical corner, sampled emission | Sampled candidate | Decoupled, 3 ports | Two ports | One port |
| --- | ---: | ---: | ---: | ---: |
| Standard-cell area, before | 547,995 µm² | 654,086 (+19.4%) | 618,244 (+12.8%) | 576,805 (+5.3%) |
| Standard-cell area, split | | 637,827 (+16.4%) | 628,939 (+14.8%) | 557,736 (**+1.8%**) |
| ABC combinational delay, before | 6,803 ps | 5,815 (−14.5%) | 5,027 (−26.1%) | 5,272 (−22.5%) |
| ABC combinational delay, split | | 5,601 (−17.7%) | 5,431 (−20.2%) | 5,167 (−24.0%) |
| Slow-corner delay, split | 9,945 ps | 8,609 (−13.4%) | 8,526 (−14.3%) | 8,381 (−15.7%) |

The mapped screen moves by a few percent in either direction between these
emissions — the one-port area falls 3.3%, the two-port area rises 1.7% — which
is the recipe's noise more than the change: the split removes a 64-bit compare
from a handful of cones and adds nothing.

### The command-split backends, routed

Same contract as `oneport-sampled-01`, stated before the runs: behind the
sampler, `physical/experiments/combined.json` (calibrated RC, width-8 clock
gating), 20 ns clock, unchanged I/O constraints, diagnostic 6×4 floorplan, four
CPUs, 150-minute cap, the whole flow including layout checks. The model's
prediction was written into the identity manifest before the first run: the
data-launched violations disappear; the register family, one level shallower,
stays where it was. Identities and numbers in
`physical/experiments/oneport-split-physical-results.json` and
`twoport-split-physical-results.json`.

| Slow corner, extracted | `combined-03` (control) | `oneport-sampled-01` (before) | `oneport-split-01` | `twoport-split-01` |
| --- | ---: | ---: | ---: | ---: |
| Worst setup slack | −2.251 ns, 40 endpoints | −0.187 ns, 9 endpoints | **+0.602 ns**, none | did not finish |
| Register-launched family | −2.054 ns | −0.053 ns | **+1.100 ns** | — |
| Loader command family | −2.251 ns | +0.473 ns | +0.602 ns | — |
| Loader data family | +0.116 ns | −0.187 ns | **+4.383 ns** | — |
| Reset family | | +0.228 ns | +0.874 ns | — |
| Protocol pins | +14.496 ns | +14.506 ns | +14.459 ns | — |
| Typical / fast setup | | +5.730 / +8.602 | +6.325 / +8.815 | — |
| Hold, slow / typical / fast | +0.539 / +0.232 / +0.059 | +0.361 / +0.168 / +0.054 | +0.379 / +0.152 / +0.060 | — |
| Functional cell area, utilization | 608,058 µm², 67.4% | 624,825 µm², 69.2% | 625,727 µm², 69.3% | 678,368 µm², **75.2%** at global routing |
| Routed wire | 1,753,794 µm | 1,663,828 µm | 1,617,478 µm | 3,386,282 µm estimated at global routing (one port: 2,156,400) |
| Detailed-routing passes to zero violations | | 51 | 17 | not reached |
| Magic DRC / LVS / antenna | not run | 0 / 0 / 0 | 0 / 0 / 0 | not reached |
| Flow exit | 0 (stopped after timing) | 2 (slow setup) | **0** | 124, wall-time limit |

**One port.** `oneport-split-01` meets setup at all three extracted corners
with clock gating — the first run of this design to do so — and finishes the
whole flow with no deferred error in 55 minutes instead of about 100. The data
port behaves as the theorem says: its worst path now ends at the loader's
`rejected` output, 4.4 ns clear, and nothing data-launched reaches the word
registers. Every other family's worst path ends in the port's word registers
(`command[0]`, `init` and `cached_word[39]` into `start_word[1]`), the endpoint
class the level model ranks deepest. 5 slew and 15 fanout limit violations
remain. The routed netlist passes the implemented-netlist regression on the
ready-mode vectors (29,898 edges, 4,903,194 output-bit comparisons, mutant
rejected).

What is not explained: the register family moved from −0.053 to +1.100 ns while
its depth in the model changed by one level of 65. That is more than the 0.6 ns
seen between equivalent RTLs under this flow. The repair steps no longer had
data-launched violations to work on, routing converged in a third of the
passes, and wire fell 3%; which of these carried the register paths was not
isolated. Two samples of this organization now exist, −0.187 and +0.602 ns, and
they differ by a change the model ranks as decisive for one family only.

**Two ports.** `twoport-split-01` did not finish. It entered global routing at
75.2% utilization — the one-port design at 69.1%, the decoupled backend that
failed earlier at 80.7% — and global routing could not remove its overflow in the
first pass: it spent 2 h 3 min disabling the wide-spacing rule of one clock net
per round, 71 rounds, where neither one-port run needed any. It did complete,
with 57% more estimated wire than the one-port design at the same step; the
repair step after it re-entered the same loop, and the 150-minute limit ended
the run before detailed routing. No extracted timing exists for this design.

What the pair says. Under this overlay and time budget the one-port core
completed routing and met setup/hold, while the two-port core did not complete.
The result supports advancing one port; it does not establish a universal
utilization cutoff or impossibility of routing two ports. Since 2026-09-18 the
official outline is the same 6×4 die area used here. The old 8×4/56% estimate is
inapplicable. A [whole-chip run](engine/whole-chip.md#the-outline) must still use the
official pin template and include the serial interface.

## What the abstraction buys

A fetch organization is now a `Policy` with three obligations, proved against
a machine that is proved once: the decoupled organization's obligations are
about forty lines where the hand-written refinement was about a hundred and
ninety, and a new organization was a sixty-line file. Its structural backend is
a `Realization` on a backend proved once: a new one was a hundred and fifty
lines and compiled at the first attempt, and the two existing ones shrank by
more than half with byte-identical output. The read ports are a parameter the
policy cannot cheat, so area accounting starts in Lean — which is how the third
read tree of the routed backend was found — and the two- and one-port
organizations were then *measured* rather than estimated. A condition on
programs has one place where it is used (`covers`), one generic carrier
(`ImageRule`), a filter that discharges it (`Admission`) and a statement at the
level of instructions that compilers prove (`Readiness`).

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
- The one-port and two-port backends are proved, emitted, checked at RTL level
  and mapped. The one-port core has two routed results: −0.187 ns slow setup
  before the command split and +0.602 ns afterward, one run of each version;
  the latter meets setup/hold but retains electrical-limit violations. The
  two-port attempt timed out before detailed routing and has no extracted
  timing. The one-port refinement is conditional on the
  `Ready` rule for every pushed word: programs that violate it — the UART
  receiver, proved never ready — are outside the claim, and its RTL regression
  runs on ready-mode vectors. The admission filter that would make it
  unconditional is a Lean construction; no emitted netlist includes it. The
  fetch-policy theory is edge-for-edge and latency one, and
  `Realization.twoWires` fixes the shape to two policy wires.
- Gate equivalence matches registers by name. Registers that synthesis narrows
  are re-exposed at full width for the comparison only; the one-port backend's
  need for three induction steps is unexplained.
- The contract has no reset, no read enable and no write-first option. Each
  would be an addition, not a change.
- The composite read is latency one only if the address map or the dictionary
  stays combinational.
- The loader's write port is unchanged; a latch array still needs the write-phase
  obligation the primitive review states.

## Reproduction

```sh
lake build Pinwheel prefetch_emit twoport_emit oneport_emit structure_report
lake env lean -DwarningAsError=true --run test/Memory.lean
.lake/build/bin/structure_report build/structure/NAME          # prefetch.json, twoport.json, oneport.json
python3 scripts/check-prefetch.py --tag NAME                    # decoupled backend; needs the pinned hardware tools
python3 scripts/check-prefetch.py --variant twoport --tag NAME  # two-port backend, unrestricted vectors
python3 scripts/check-prefetch.py --variant oneport --tag NAME  # one-port backend, ready-mode vectors
```
