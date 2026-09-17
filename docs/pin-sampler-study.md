# Pin-sampler study

This record owns the structural two-register input pipeline, its Lean
correspondence, the emitted-artifact checks and the matched physical comparison.
The [external interface contract](external-interface.md) owns the digital boundary
it implements; [research status](research/status.md) owns allocation. The reference
instruction, loader and timing semantics of the inner core are unchanged.

## Question

After [calibrated wire estimates](physical-correlation-study.md#result-calibrated-estimates-rc-calibrated-01),
the remaining slow-corner setup miss (−0.153 ns) launches from the `incoming[1]`
input port, inside the 4 ns external input-delay budget, and ends in the
current-word cache. The interface contract already proposes two sampling
registers in front of `incoming`. Does inserting them, with every inner
expression unchanged, remove that path family, and what exactly does the wrapped
circuit then implement?

## Construction

`Hardware/NetlistExtend.lean` defines `Netlist.extend`: every inner input leaf
becomes an expression over outer inputs and an extended register set
(`Extended R X`: all inner registers plus wrapper-owned ones), and the wrapper
registers receive their own next-state expressions. Shared `letWire` bindings
keep their order, so no combinational sharing is lost and no expression tree is
re-expanded. Three theorems (`extend_inner`, `extend_extra`, `extend_observe`)
state, for every netlist, input map and wrapper state, that inner registers and
outputs evaluate exactly as the inner netlist does on the substituted inputs.

`Hardware/PinSampler.lean` instantiates it for any netlist with the loader
machine's ports:

- two 2-bit registers, `first ← incoming` and `second ← first`;
- the engine-side `incoming` leaf is `second`; `init`, `reset`, `command` and
  `data` pass through untouched;
- **no reset**. Nothing sits between the stages, only `second` reaches engine
  logic, and after two edges both stages hold real pin samples. This ties the
  contract's reset argument low (`advance_contract`), so
  `PinBoundary.two_edge_latency` applies to every pair of edges without a
  no-reset side condition. A board-specific reset profile can be added later as
  a separate contract change.

`Hardware/Storage/SampledBackend.lean` wraps the three proved composed backends
(`Backend.netlist`, `BankSelect.netlist`, `CacheEnable.netlist`) and supplies the
609-register layout and labels. Ports and the module name are unchanged.

## What Lean proves

All statements hold for arbitrary power-up contents of the pipeline and arbitrary
host-command and pin histories.

1. **`PinSampler.trace_eq`** — every edge of the wrapped netlist is one edge of
   the inner netlist on the delayed history: no edge is added, removed or
   reordered. `delayed_two_edges` states that the inner netlist consumes on edge
   n+2 the pin value presented on edge n; `delayed_host` that host ports are
   never delayed.
2. **Post-edge observations.** The project's trace records each output before
   and after the register update under the same input. Behind input registers
   that is no longer the right specification: after the edge, `second` already
   holds its next value. `read_b` (the successor-read address) depends
   combinationally on `incoming` through terminal capture, so its post-edge value
   reflects the advanced pipeline. `Hardware/TimedPairs.lean` therefore adds
   `Component.pairTrace`, whose post-edge observation takes its own input, proves
   that the ordinary trace is the special case with both inputs equal
   (`pairTrace_same`), and proves that every `Timed.Refinement` preserves pair
   traces (`Refinement.pairTrace_eq`). The wrapped trace equals the inner **pair**
   trace with post-edge input `engineInputs i (advance i p)`.
   `Sampled.reference_registered` proves that the distinction is invisible on
   every registered output — all state views including pin levels and enables,
   the current address and `busy`. Only the loader handshakes (functions of host
   ports, which are not delayed) and `read_b` are combinational.
3. **`Sampled.trace_correct` / `Sampled.initialized_trace`** — composing (1)–(2)
   with each backend's existing complete refinement: from any valid state, and
   from the initializing edge with no prior cache invariant, every pre/post-edge
   observation of the wrapped netlist equals the reference machine's on the
   delayed pin history.
4. **Protocol composition (`UART/LinkPipeline.lean`).** `Link.Safe` and
   `StreamLink.Safe` constrain the earliest observation age only from below and
   otherwise only the age spread. `Safe.delayed` shows both survive any uniform
   added delay. `pipelined_observe` shows that if every stage holds the idle level
   when receiver cycle zero begins, the engine-side history
   (`true` for the first `stages` cycles, then the direct observation `stages`
   cycles earlier) **is** an ordinary observation history with age
   `age (n − stages) + stages · rxTick`, contained in the bounds delayed by
   `stages` RX ticks. The existing single-frame and continuous link theorems then
   apply unchanged to those delayed bounds. The idle precondition is an explicit
   obligation on when a receiver program is started.

The environment audit passes with standard axioms only (10,902 declarations,
5,664 theorems on this branch). `test/PinSampler.lean` executes a small wrapped
netlist against hand-computed registered and combinational observations,
checks the pair-trace equality, shows that a held input differs only in
combinational post-edge observations, and rejects a one-stage pipeline.
`test/UARTLink.lean` additionally delivers 144 frames through the compiled RX
program on explicit two-stage pipelined histories under the delayed bounds, and
rejects a one-stage age claim.

Not proved: anything about asynchronous arrival, metastability resolution,
thresholds, or that a physical flip-flop pair meets an age bound; and no bridge
theorem yet connects `PinSampler.delayed` on loader-machine input lists to the
`Nat → Bool` histories of the UART link model. I²C stretching/timeout contracts
have not been rechecked against the added two edges.

## Emitted artifact

`sampled_emit` writes the selected backend twice from one build: `inner.mlir`
unchanged, and `sampled.mlir` behind the pipeline. For the command-split base:

- `inner.sv` is **byte-identical** (SHA-256 `31893069…c6c6f764`) to the composed
  command-split control whose full Lean read-back is recorded in the
  [bank-selection](bank-selection-study.md) and [cache-enable](cache-enable-study.md)
  manifests.
- `sampled.mlir` differs from `inner.mlir` in eight lines: three operands
  `%incoming` → `%r_pin_second` and two added `seq.compreg` lines. `sampled.sv`
  (SHA-256 `3e6cf6be…4a9442a1`) differs from `inner.sv` by the same substitution at
  four expression sites, two declarations and two `always_ff` blocks.

`scripts/check-sampled.py --tag NAME --variant command-split` retains a fresh
receipt. Completed run `build/sampled/cs-02/report.json` (157.967 s on this host):

| Check | Result |
| --- | --- |
| Inner emission equals the read-back-proved RTL | identical SHA-256 |
| Sampled RTL ≡ proved inner RTL behind a hand-written two-register pipeline (Yosys `equiv_make`/`equiv_simple`/`equiv_induct`) | all **6,319** points proved |
| One-stage and bypass reference pipelines | both rejected (177 unproven points each) |
| Sampled RTL ≡ synthesized generic gates | all **6,313** points proved |
| Independent Python oracle, pins presented two edges early | **28,165** loader edges, **17,501,916** storage observations pass; held-cache mutation rejected |
| Same oracle, pins not shifted (sampled RTL) | rejected at edge 8,299 |
| Same oracle, pins shifted (inner RTL) | rejected at edge 8,301 |

The reference pipeline is six lines of hand-written SystemVerilog around the
unmodified proved module; it is not emitted from Lean, which is what makes the
comparison informative. State correspondence equates same-named registers; it
does not equate independent power-up values. The oracle's first two engine-side
samples precede any running program, so uninitialized pipeline contents are not
observed by the regression.

| Matched mapping screen | Inner (command split) | Sampled |
| --- | ---: | ---: |
| Typical cell area (µm²) | 546,109.9 | 547,995.2 (+0.35%) |
| Slow cell area (µm²) | 546,547.2 | 548,114.9 (+0.29%) |
| Typical / slow ABC delay (ns) | 7.106 / 9.956 | 6.803 / 9.945 |
| Mapped flip-flops | 6,226 | 6,236 |

State grows by exactly four bits (6,233 → 6,237 declared; generic synthesis
6,204 → 6,208). The mapped count grows by ten because `r_cached_word[8:3]` feeds
only the canonical-halt comparison, which is masked wherever it is consumed: ABC
removes those readers in the inner mapping and keeps them here. That is a mapping
heuristic, not a state difference; it also identifies six cache bits that a
future structural cleanup could drop. The mapping screen has no I/O delay
model, so it cannot show the effect this study is about.

## Trust boundary

Lean covers the wrapped netlist. The emitted sampled RTL has **no direct Lean
read-back**; its link to proved RTL is the tool-checked sequential equivalence
above plus the independent regression. CIRCT, the Yosys frontend and equivalence
engine, and the hand-written reference pipeline are trusted there. Extending the
full read-back to 609 registers is possible with the existing generator and is
left open. Technology-mapped equivalence remains open as before.

## Physical comparison

Pending: matched runs of the composed command-split control and the sampled
candidate under the [calibrated flow](physical-correlation-study.md), unchanged
20 ns clock, I/O constraints and diagnostic floorplan, stopping after final
extracted timing.

## Reproduction

```sh
lake build Pinwheel sampled_emit
lake env lean -DwarningAsError=true test/ProofAudit.lean
lake env lean -DwarningAsError=true --run test/PinSampler.lean
lake env lean -DwarningAsError=true --run test/UARTLink.lean
python3 scripts/check-sampled.py --tag NAME --variant command-split
```

The last command needs the pinned CIRCT/OSS CAD tools and technology libraries
described in the [development record](development.md).
