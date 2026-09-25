# Timed component contracts

Implemented 2026-09-14. This first library refinement makes the existing cache and
successor-fetch assumptions explicit while preserving the generated circuit.

## The abstraction

`Hardware/Timed.lean` defines a component by its state transition and observation
function. An observation may depend on both inputs and registers. For each input
snapshot, `edge` observes the circuit before and after its register update, holding
that input snapshot fixed. `trace` retains both observations for every clock edge.
This describes settled digital values; it does not model propagation delay or glitches.

A `Refinement` relates implementation state to specification state. It requires
equal observations and preservation of the relation after **one edge on each
side**. Refinements compose through an intermediate state. `edge_eq` and
`trace_eq` then establish exact observation equality without allowing extra cycles.
That matters for a protocol engine: a delayed output can carry the right value and
still violate the required waveform.

## Fetch and capture order

`Hardware/Reactive/Fetch.lean` names the request context, core registers, address,
reader, current-word invariant, and resolution operation. Both the reference atomic
machine and the cached machine now use `Fetch.resolve`.

The reader returns the E64 word at the selected address from the selected pre-edge
program image. It is a **combinational read contract**. `resolve_congr` says readers
that agree at this address supply identical scheduler inputs; `address_resolved`
proves the fetched successor cannot feed back into its own address selection.

For a checked branch, the order is:

1. Use the current execution record and the current input snapshot to perform the
   terminal capture logically.
2. Select the successor address using that updated sample slot.
3. Read the successor record and use its entry capture when computing next state.

These are dependencies within one modeled clock cycle, not three execution cycles.
`branch_uses_terminal_capture` proves the address rule. The executable check uses
an old false sample, a terminal capture of true, and a successor entry capture of
false: it must take the yes branch and finish with a false sample.

`Hardware/Reactive/FetchChoice.lean` supplies the pure foundation for speculative
reads. `candidateAddress` prepares both possible addresses independently of
incoming pins; `address_choice` preserves sequential, jump, branch and idle
selection. `readCandidates_eq` permits selection after either address-map reads
or complete-record reads. Both resolution theorems establish equality of all
scheduler inputs with the existing `resolve`. They add no execution cycles or
effects for the unselected read. `Hardware/Storage/FetchChoice.lean` binds these
expressions to writable stores, proves equality of every register update and
output, and composes the result with the existing cache refinement. Its
`trace_correct` covers complete pre/post-edge traces of the structural E64
machine from the existing cache invariant. Dense encoding and emitted RTL retain
the separate translation evidence described below.

`branchExpr_correct` and `candidateExpr_correct` connect the corresponding
structural expressions to those values. `selectionExpr_correct` accepts the
parent's register/input namespaces and a proved combinational reader, allowing
the late selector to compose with writable stores. The focused check evaluates
both structural lookup arrangements as well as the value-level functions.

The focused `FetchChoice` check runs 128 consecutive one-cycle branches, including
self branches and entry capture overwriting the branch slot. Both lookup forms
match the reference state. A stale-selection mutation differs on 63 edges.

`CurrentValid` requires the cached word to equal the active image at the current PC
while the core is running. Idle cache contents are unrestricted. The existing
atomic-loader rules still own image selection, commit, and write exclusion; the
reader abstraction does not replace those rules.

## Capacity-independent command decoding

`Hardware/Storage/CommandSplit.lean` supplies a narrow expression transformation
for the small-store experiment. Capacity rejection changes push command 2 into
reject command 6. Comparisons to every other command can use the raw command;
commit/start decisions therefore need no capacity/data input. The original
adapter remains on the command uses that need it.

`expression_correct` proves evaluation equality for arbitrary input/register
values. `adapted_small` identifies the original small-store semantics, while
`component_same` and `trace_correct` preserve all updates and pre/post-edge outputs
of any transformed circuit for every finite input history. There are no new
cycles, state invariants, or scheduling assumptions. As elsewhere, these are
settled two-state values; glitches and propagation delays belong to physical
validation. The optional dense emitter is checked separately against the unchanged
baseline. See the [decoder experiment](../storage/successor-fetch-study.md#command-decoder-experiment)
for mapping, connectivity, and independent trace results.

## Concrete proof composition

`Hardware/Storage/CacheContract.lean` supplies three components:

| Component | State and execution |
| --- | --- |
| Structural cache | Register valuation evaluated by `Cache.circuit.step` |
| Cache model | `Cache.State` updated by `Cache.next` |
| Reference machine | `Machine.State` updated by `Machine.next` |

`structuralRefinement` uses the existing register-update correctness theorem.
`refinement` uses cache validity, preservation, and machine-state correspondence,
plus a new proof covering **every machine output**, including loader responses,
core state, and both diagnostic read addresses. `completeRefinement` composes them;
`structural_trace_correct` preserves every pre/post-edge observation for any finite
input history from a valid cache state.

`initialize_valid` establishes cache validity after initialization without assuming
initial cache bits or memory contents. `initialize_machine_next` also establishes
reference-state agreement on that update. The trace guarantee applies from the
initialized states; arbitrary pre-initialization observations are not claimed equal.

The original state/run proofs remain available. Cache and dense-record semantics
now import semantic contracts instead of emitters; emission modules import their
own emission dependencies explicitly.

## Checked interfaces and named observations

The Hardcaml-inspired interface layer is implemented in `Hardware/Interface.lean`.
A descriptor contains an ordered signal enumeration, a typed position lookup,
and external names. Its proofs establish that every signal is present and that
names identify distinct slots. Widths remain part of the existing Lean signal
types. This checks the enumeration against those types; adding a constructor
requires updating the descriptor and its coverage proof.

`Hardware/Reactive/Interface.lean` owns the scheduler's eight inputs, 22 registers,
and 25 outputs. Existing register/output arrays and names moved out of the emitter
without changing their order or public identifiers. The functional `Inputs` and
`State` records and their value conversions remain explicit.

`Interface.mapM` performs an operation on each declared signal in order, then
returns a function indexed by typed signal identity. Both `CacheEmit` and
`DenseEmit` now retrieve the PC expression with `nextValues .pc`. The old
string-label comparison and empty-string fallback are removed. `rename_mapM`
proves that changing descriptor names leaves this traversal and lookup unchanged
for the same callback; `mapM_pure` proves the pure lookup round trip.

`namedComponent` reuses the timed component's transition and records each
observation's name, width, and value. `namedRefinement` carries an existing timed
refinement through this observation adapter. `edgeDifferences` compares both
phases and includes the cycle and component supplied by the caller. An injected
post-edge PC error in `test/Interfaces.lean` produces:

```text
cycle 42 after cache.core.pc (8 bits): expected 0, got 1
```

`differences_empty_iff` proves that an empty comparison means every typed signal
agrees. The executable checks also exercise renamed PC lookup, effect order,
named observations of the cache component, and a pre-edge error in sample slot 15.

This is a bounded migration of the scheduler interface and its cache consumers.
Loader/store interfaces and other emitter adapters retain their existing wiring.
It does not add RTL module hierarchy, generate all simulator bindings, or prove
the serializer. Strings are still used at the emission boundary; they no longer
select the PC result in these two adapters.

## Evidence and limits

Run `python3 scripts/check-timed-contracts.py` with the pinned Lean toolchain on
`PATH`. It requires the hardware tools and generated oracle fixtures from the
completed [storage study](../storage/storage-study.md); it reports missing or changed fixtures
instead of silently replacing them. For a Lean-only check, run `lake build` and
`lake env lean --run test/TimedContracts.lean`. Run
`lake env lean --run test/Interfaces.lean` for the interface regression.

The runner audits the timed/interface contracts, checked descriptors, and existing
storage theorems for standard Lean axioms, runs the focused timing/interface
checks and existing cache/codec regressions,
re-emits five storage MLIR modules, and compares them against the hashes recorded
before this refactor at commit `7dcd064`. It exports the general 32-entry dense
cached candidate to SystemVerilog and requires the prior RTL hash:

```text
1664dc719bff05307e3f17a6a8c611aba520917d49be132f1bf164bf1c53548b
```

It then compiles that freshly exported RTL, replays the independent atomic-loader
oracle, and requires a deliberately corrupted cache update to fail. Logs, source
and fixture hashes, and the final receipt live under `build/contracts/`. Mapping
and physical-flow receipts are retained separately.

The completed checks audited **102 declarations**, matched **21,342** independent
oracle edges in the Lean cache components and **104,642** codec vectors, and passed
**21,409** generated-RTL edges with **13,151,052** storage observations. All five
MLIR hashes and the RTL hash matched; the held-cache mutation was rejected.

The new composed theorem covers the structural E64 cache and reference machine.
The dense codec and bounded store retain their existing individual proofs; the
combined emitted candidate has regression and byte-identity evidence here. This
does not add a proof of the emitter or CIRCT translation, nor new area/frequency
evidence. The [physical timing failure](../physical/physical-validation.md) remains open.

## Sources and next application

The useful lessons from other hardware libraries are narrow and concrete:

- [Hardcaml interfaces](https://docs.hardcaml.org/hardcaml-docs/using-interfaces/module_interfaces/)
  encourage one declared interface across construction and simulation. Its
  [simulation model](https://docs.hardcaml.org/hardcaml-docs/simulating-circuits/simulation/)
  makes the clock observation phase explicit.
- [Kôika](https://github.com/mit-plv/koika) makes scheduling and forwarding within a
  cycle explicit. Pinwheel needs the capture/branch/entry order above.
- [Kami](https://adam.chlipala.net/papers/KamiICFP17/KamiICFP17.pdf) motivates modular
  refinement and replacement. Pinwheel's contract deliberately requires exact
  cycles for its timing-sensitive observations.
- [Calyx static control](https://docs.calyxir.org/lang/static.html) makes latency a
  component contract. A synchronous SRAM cannot implement our current reader API
  merely by returning the same word later.

These are design influences, not new dependencies or claims that the libraries
share identical semantics.

A future memory replacement must describe the proposed backend's availability
schedule and prove that prefetch supplies each successor by its existing execution
edge. If it cannot, that is an architectural timing change. This contract gives us
a precise way to expose that change before attempting physical optimization.
This is a conditional application; [research status](../research/status.md) owns
the current experiment and priority.
