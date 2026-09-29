# Conditional paired correspondence

On 2026-09-27, the first conditional proof gate connects the **actual retained
paired graph and package composition** to an explicit synchronous SRAM model.
The generated circuit is unchanged. This is a foundation for the complete
design iteration, not yet a theorem that a loaded E64 program executes correctly.
[Research status](../research/status.md) owns the next gate.

**September 28 follow-up:** [upload coverage](paired-upload-coverage.md) now
connects accepted words to the complete stored image and proves enabled-read
responses. This page preserves the first gate's receipt and scope; timed E64
execution remains open.

## What this gate proves

| Layer | Kernel-checked result | Source |
| --- | --- | --- |
| Shared graph construction | A successful `construct` evaluates each named wire in order using one pre-edge register snapshot; both next state and observation match the graph interpreter. | [`construct_correct`](../../Pinwheel/Hardware/Storage/PairedSemantics.lean) |
| Graph equations | Fresh names and backward references establish every node equation. Both actual 45-node binding lists satisfy those conditions. | `evaluate_equations`, `bindings_ordered`, `validation_bindings_ordered` in the same file |
| Validation optimization | The seven upstream equations required by the earlier local proof are derived from the actual graph. The retained isolated-validation variant and original paired variant agree for all inputs and register states. | `upstream_equations`, `validation_inputs_eq`, `validation_core_eq` |
| Package composition | Input sampling, serial reception, pin mapping and result observation compose with the graph interpretation without inserting or removing edges. | [`retained_package_correct`](../../Pinwheel/Hardware/Storage/PairedComposition.lean) |
| Memory modes | The retained package never asserts read and write together, even before initialization. Converting its output pins to a contract command preserves both enable values. | [`retained_package_exclusive`, `command_enables`](../../Pinwheel/Hardware/Storage/PairedClosed.lean) |
| Memory behavior | Idle holds contents and Q; writes update one word and hold Q; enabled reads update Q on the edge. A partial model tracks established values from arbitrary initial contents. A defined read returns its promised value. | [`SinglePort`](../../Pinwheel/Hardware/Memory/SinglePort.lean) |
| Closed package traces | Given a memory implementation satisfying that contract, the retained typed package and graph-based model agree before and after every edge of every finite package input history. Both use the old Q to compute the next state. | `contract_refinement`, `retained_package_trace` |
| Active SRAM bank | Every write targets the bank opposite the current active bit and preserves every word of the previously active bank. This does not require a complete upload. | `write_address_bank`, `active_words_preserved` |

The package trace theorem permits arbitrary initial controller registers,
memory contents and Q. It relates both sides to the **same arbitrary initial
state**, rather than claiming meaningful program behavior before initialization.
Histories may contain reset, incomplete uploads, malformed commands and rejected
operations; agreement with the graph still holds.

## The premise and the remaining gap

`SinglePort.Contract` is a theorem parameter containing a memory state view,
transition function and proof that each allowed operation follows the digital
law. No global axiom asserts that the physical macro satisfies it. Applying the
theorem to the supplied SRAM still needs the fixed full-mask/normal-mode binding,
qualified power and clock timing, and component evidence described in the
[original contract proposal](../../physical/fixtures/sram-trust/contract.json).
The new mode-exclusion theorem discharges one controller obligation; it does not
qualify macro internals or electrical behavior.

The partial memory model starts with every cell and response **unspecified**.
`initialized_read` promises a value only when its address is already defined.
This first gate does not prove that the paired loader establishes that premise.
The [subsequent upload gate](paired-upload-coverage.md) establishes the stored
image and enabled-read response, while usable Q on every execution edge remains
open. Graph interpretation also preserves the implemented behavior without
establishing the required timed E64 behavior. The existing
[image certificate](paired-image-certificate.md) proves successor correspondence
for chosen branches, without proving when the real controller dispatches or
which branch its captures select.

This checkpoint identified the following obligations. The September 28 upload
gate closes the first two; the remaining execution obligations are current:

1. Track the accepted upload prefix through reset, begin, rejection, abort and
   interruption. Establish all 32 parameter words, 256 SRAM rows, boot and idle
   metadata before commit; arbitrary power-up contents must remain allowed.
2. Prove commit selects that complete image and later inactive-bank updates
   preserve its SRAM contents and parameter/metadata state.
3. Maintain the response invariant while running: usable Q belongs to the
   current token's paired row, and parameters belong to the active image.
4. Connect actual dispatch, capture, wait, timeout and terminal cycles to the
   E64 reference using `PairedImage.Corresponds`; then reuse the proved package
   composition above.

There is no new physical acceptance, competition admission, clean-source chip
replay or source-to-GDS theorem. RTL string emission, CIRCT, synthesis and the
physical implementation remain separate evidence layers.

## Verification and reproduction

The [checker](../../scripts/check-paired-formal.py) runs the default Lean build,
checks library import reachability, audits all library axioms, rejects an injected
axiom and checks concrete memory/graph boundary controls. Its executable witness
constructs both actual cores and checks that the package used by the theorem
emits exactly the same hardware IR as `PairedValidation.chipText`.

```sh
python3 scripts/check-paired-formal.py --tag paired-formal-fresh
```

With the retained local mapping artifacts available, also compare their hashes:

```sh
python3 scripts/check-paired-formal.py --tag paired-formal-retained-fresh \
  --retained-manifest physical/experiments/paired-validation-mapping.json
```

The recorded `paired-formal-01` run passes in **9.191 seconds**, with **212
reachable modules**, **15,843 audited declarations / 8,001 theorems**, and only
the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`). All nine
kernel-checked contract/ordering examples and the four existing invalid-graph
controls pass. The separate schedule proof still checks. This is a focused proof
gate; the full protocol executable suite was not rerun for these additive proof
and model files.

Fresh `core.mlir`, `chip.mlir` and `assembly.json` exactly match the retained
`paired-validation-check-06` artifacts. The proof's package emission also matches
the independent existing emitter entry point. This is an executable binding
check, not a formal proof of the string emitter or Verilog lowering.

The [manifest](../../physical/experiments/paired-formal-results.json) binds the
full report, new sources, retained identities and open obligations. The report
records UTC September 28, which is still September 27 in the project timezone.
All frozen validation inputs are unchanged. There are **zero CAD invocations**;
campaign usage remains 8,412.163 seconds, with three A routing attempts used and
two B attempts reserved. Historical physical receipts and the proposed SRAM
contract remain unchanged.

This is a new source freeze: adding the proof imports changes `Pinwheel.lean`.
Earlier source hashes retain their historical meaning; byte identity is checked
for the retained emitted artifacts, not asserted for every old source input.
