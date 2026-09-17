# Memory abstraction

This record owns the memory contract, its two structural implementations, the
view of the existing storage through it, and the prefetch machine: the reference
machine written against a memory of latency one. It is Lean proofs and one
executable suite; no CAD tool runs and no RTL changes. The
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
and SPI, a second image staged around a run (pushes during the run are
rejected as busy) and committed after it, resets, rejected commands — 4,754
edges, 10 transactions, 24 taken branches, no difference in control, core or
probed outputs. A variant that reads only the
untaken candidate (one read port) agrees until the first taken branch and then
diverges: the address NACK's branch to STOP.

### What the review's obligations become

| Obligation in the primitive review | Here |
| --- | --- |
| Define latency, retained outputs, simultaneous read/write | `spec`: read-first, latency `ℓ`, outputs independent of the request when `ℓ ≥ 1` |
| Prefetch both branch successors before terminal capture | `Prefetch`, proved for every input history |
| Dependent map and dictionary accesses | The prefetch reads the composite once, as one latency-one read: structurally the map or the dictionary must stay combinational, not both registered |
| Ports or buffering under the same clock contract | Two read ports on the selected bank (or two copies), the same edges, no added cycle |
| Reset and commit invalidate pending reads; atomic replacement | `initialize_valid`, `selected_memory`, `machine_next` |

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

- Functional level only. No structural prefetch circuit, no emission, no RTL,
  no macro timing or physical claim. The `Registered` model is not the vendor
  macro: read enables, bit masks, BIST and power modes are outside the contract.
- The contract has no reset, no read enable and no write-first option. Each
  would be an addition, not a change.
- The composite read is latency one only if the address map or the dictionary
  stays combinational.
- The loader's write port is unchanged; a latch array still needs the write-phase
  obligation the primitive review states.

## Reproduction

```sh
lake build Pinwheel
lake env lean -DwarningAsError=true --run test/Memory.lean
```
