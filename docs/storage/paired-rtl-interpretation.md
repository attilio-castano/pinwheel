# Interpreting the retained paired RTL

The retained controller and package now have Lean interpretations connected to
their typed components and the certified upload/E64 session theorem. The
connection covers every represented register update and output for arbitrary
two-state inputs and state. It is specific to the retained artifacts; it is not
a proof of every program accepted by the Verilog or CIRCT toolchains.

[Research status](../research/status.md) owns the current decision. The
[admission study](paired-upload-admission.md) owns the digital session premises;
the [acceptance report](../research/implementation-acceptance.md) joins these
artifacts to the physical candidate. SRAM qualification, compatible fast timing
conditions and package power qualification remain independent requirements.

## What is connected

Previously, the session proof described the typed circuit and generation
checks identified its emitted files. SAT comparisons then connected emitted
variants and mapped implementations. The missing connection was the meaning
of the actual emitted circuit.

The new certificate interprets the raw retained RTL as register-update and
output functions. It proves equality with the typed controller and package
components, including unreachable represented states. Substituting the package
equality into `PairedSession.retained_initialized_session` gives
`Pinwheel.Artifact.Paired.Package.rtl_initialized_session`: reset/release,
qualified upload of a certified image, accepted commit, and E64 package
observations without another reset.

| Interpreted module | Register fields / bits | Output fields / bits | Shared equations | Local equivalences |
| --- | --- | --- | --- | --- |
| `pinwheel_paired_core_controller` | 81 / 1,469 | 37 / 157 | 45 | 521 |
| `pinwheel_paired_controller` | 110 / 1,592 | 7 / 99 | 45 | 561 |

All raw state is retained, including bits later removed by implementation
optimization. SRAM Q is an independent 64-bit input at this boundary. The
session theorem closes memory feedback using the explicit single-port memory
contract; the readback certificate does not qualify a physical SRAM macro.

## Proof and trust boundary

1. A private instance of the existing restricted backend importer enforces the
   paired module's complete input, register, output and clock contract. Yosys
   reads SystemVerilog and runs `proc`, `pmuxtree`, `opt_clean`, and `check` before
   exporting JSON. The frontend/lowering and the Python adapter remain trusted
   interpretation boundaries. The adapter rejects unknown values, hidden state
   or memories, unsupported cells, implicit initialization and incompatible
   clocking. No technology mapping or physical-design run is performed.
2. MLIR supplies untrusted proof hints. Each of the 45 shared values is checked
   against its typed binding. Ordered-graph uniqueness then connects every
   hinted register update and output to the typed component. Labels and matching
   generated files alone do not discharge this step.
3. Sampling and Z3 suggest local equivalences. Bit slices and comparison
   predicates stay connected where independent cuts would lose correlations.
   At difficult endpoints, an untrusted selection of actual RTL gate equations
   is expanded into the expressions. These equations introduce no new premises.
4. Lean reconstructs every local equality and its connection to the raw graph.
   Explicit lemmas handle cursor comparisons, adjacent bit slices and subtraction
   across the nine-to-eight-bit address boundary. Total case coverage establishes
   component equality; the package theorem composes with the existing session
   proof. The compiled-environment audit allows only `propext`, `Classical.choice`
   and `Quot.sound`, including dependencies and private declarations.

The default `bv_decide` reconstruction was rejected during development because
it introduced native-evaluation axioms. The accepted generator uses explicit
proofs and retains the existing axiom policy. No compiler-equivalence axiom is introduced. The frontend and adapter retain
the explicitly stated interpretation boundary.

The two-state interpretation does not model metastability, analog reset or
sampling, electrical timing, power delivery, manufacturing, or unspecified SRAM
behavior. The final implementation still relies on the separately scoped mapping,
physical equivalence, cell-function and connectivity checks documented in the
acceptance report.

## Reproduce and inspect

Use the pinned Lean toolchain and the local Yosys/Z3 tools in
`build/tools/oss-cad-suite/bin/`. The retained mapping and admission artifacts
must be present. Every run requires a fresh tag:

```sh
python3 scripts/check-paired-readback.py --tag paired-readback-fresh
python3 -m unittest discover -s test -p test_paired_readback.py -v
```

The runner freezes sources, tool binaries and selected artifacts; checks fresh
emission identity; regenerates and compiles both interpretations; audits their
axioms; and composes the package session theorem. Its receipt retains command
logs, generated proof sources, exact input hashes and negative fixtures. A
missing premise, failed proof, changed input or incomplete check prevents a
passing receipt. Ignored build artifacts remain dependencies for replay; this
does not establish a clean-source physical rebuild.

The six independently reimported RTL corruptions change the upload cursor,
parameter bank, SRAM write enable, input sampler, mailbox-valid bit and package
output. Each must fail when given the original checked certificate. Unchanged
reimports of both modules must pass. Injected axioms must fail both audits.
Python controls also delete every register and output independently and test
invalid clocks, state, memory, interface metadata and hint shapes, including
execution with Python optimization enabled.

The first packaged run, `build/validation/paired-readback-01/report.json`, is
retained as a failure: a broad interface adaptation incorrectly changed the
package-to-core projection types. Lean rejected it; the corrected generator
adapts only the reused graph/link code. Exploratory probes are not acceptance
evidence. The final receipt and hashes are recorded in
[`paired-readback-results.json`](../../physical/experiments/paired-readback-results.json).

The passing `paired-readback-02` run took **315.149 seconds**, froze **264 inputs**,
and retained **160 source/log artifacts** across **69 recorded validation commands**. The controller
audit covers **18,645 theorems**; the package/session audit covers **19,542**.
These include the shared library and must not be added together as a unique
count. The report SHA-256 is
`666c1a75e56cc8d1a6ab598e1038338d708e5010f77d802b8c68c27d4abe16cd`.
The [refreshed acceptance assessment](../research/implementation-acceptance.md)
checks 740 files and 75 evidence connections; its formal row passes and its
three physical refusals remain.

## Consequence for the design iteration

The emitted interpretation now participates in the same conditional digital
argument as the source certificate, upload admission and package execution.
This removes the formal artifact-interpretation blocker for these retained
modules. It does not accept design A or spend another route slot. The next
acceptance decisions concern exact-version SRAM qualification, compatible fast
conditions and package power assumptions; the declared capacity-B experiment
still waits for A's required gates.
