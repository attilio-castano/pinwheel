# Checked controller reference for artifact sessions

This stage supplies a kernel-checked semantic reference for the buffered SRAM
controller without changing its circuit, storage representation, emitted RTL or
public interface. The complete source-to-RTL session certificate remains a later
integration target.

The direct conversion proof exceeded its resource budget because the typed
expression tree repeats large subexpressions, while the native emitter retains
a small DAG. The new generators keep those boundaries explicit:

1. `buffered_reactive_reference.py` emits the existing Reactive helper expressions,
   scalar transitions, observations and both candidate addresses. Generated Lean
   proves all 138 roots against the original typed expressions, using previously
   checked helper equations as cuts.
2. `buffered_sram_reference.py` emits 203 leaf-environment and control roots.
   Generated Lean proves each against the existing SRAM expressions or the
   equivalent `SramArtifactReference` definitions. That reference is connected to
   `Sram.circuit` by general binding and storage-rewrite theorems.
3. The generator substitutes the checked leaf DAG into the checked Reactive DAG.
   A theorem for every substituted node reconstructs the composition in Lean.
   A second, small substitution applies the candidate-address expressions to
   the prospective core transition.
4. The resulting 5,502-node description has exactly the controller's 117 physical
   next-register endpoints and 31 observations. Every root is proved equal to
   `Sram.circuit.step` or `Sram.circuit.observe` for arbitrary two-state inputs
   and register values. There is no initialized-state or valid-program premise.

The represented physical state is 3,151 bits. The typed SRAM register family also
contains phantom word coordinates, which the emitted controller omits; total
interpreters extend those coordinates with the existing zero transition. No
extra physical storage or equality between the two SRAM Q inputs is assumed.

The Python parsers and graph choices supply proof hints. The generated root
proofs, rather than a source-text inventory or sampled comparison, establish the
semantic equations. Source parsing may fail when definitions change; it cannot
turn a failed kernel proof into a certificate.

Development validation on 2026-10-17 checked the generated modules under
`build/buffered-sram-artifact/{environment-expanded,named-reactive-expanded,complete-reference-spike}`.
The module-ownership axiom audit covered 21,547 declarations and 9,143 theorems,
including generated private declarations; only `propext`, `Classical.choice` and
`Quot.sound` occurred. Six refusal controls passed normally and with Python
optimization enabled. These development outputs are not a fresh committed-source
qualification receipt. The campaign gate must regenerate and check them from a
retained Git archive before claiming that stronger provenance result.

A separate development pipeline has checked all 1,881 local equations from the
actual emitted controller MLIR to the reimported RTL, including 503 stronger
comparison-atom lemmas, and the complete 117/31 graph correspondence. Connecting
this semantic reference to that actual emitted graph is still required. Wrapper,
memory feedback, initialized session and Tiny Tapeout claims must use the final
connected component certificate. Yosys SystemVerilog/process interpretation and
the restricted word-level reader remain explicit interpretation boundaries;
this work does not qualify synthesis mapping, electrical timing or SRAM macros.
