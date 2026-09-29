# Certified paired upload admission

A correctly delivered certified paired image now **necessarily passes the
actual controller's upload checks and reaches commit**. The resulting package
execution agrees with E64 without an extra reset after commit. Acceptance and
the accepted transcript are conclusions of the proof, replacing the success
premises of the earlier [host lifecycle gate](paired-host-lifecycle.md).

This completes the conditional digital path from a certified image, through
serial delivery and actual storage, to execution and host observation. It does
not qualify the physical SRAM or establish the whole source-to-GDS chain.
[Research status](../research/status.md) owns the next decision; the
[manifest](../../physical/experiments/paired-admission-results.json) binds this
gate's source and validation receipt.

## Exact claim and mechanism

[`PairedSession.retained_initialized_session`](../../Pinwheel/Hardware/Storage/PairedSession.lean)
starts with arbitrary represented controller registers, sampler/receiver state,
mailbox contents, SRAM contents and Q. Three reset-low samples followed by two
reset-released, deselected samples initialize the controller and prepare the
serial adapters. The two release edges are before upload; they are not an extra
reset or delay between commit and start.

A qualified `Serial.Session` then delivers begin, the image's 290 words and
commit. Two trailing pin samples drain the existing sampler pipeline. The source
certificate checks the actual image against canonical E64. The theorem derives
the complete accepted transcript, valid selected image, and ready E64 state.
Every before/after observation of all three package output ports then agrees
with the composed reference for the subsequent execution segment.

The central dependency is the parameter table. Row validation reads the
inactive bank, not a separate ideal table:

1. Begin empties the staged transcript and sets the cursor to zero.
2. Each of the first 32 words fits the 20-bit parameter register. Accepted-prefix
   ownership proves that these registers contain the certified table.
3. Every row token is canonical for its source operation, or a canonical HALT
   or fault token. Its actual parameter lookup therefore passes the real mask
   and capture checks. Padding rows are checked as well.
4. Boot and idle metadata pass their width and token checks. The accepted cursor
   reaches 290; commit switches banks and establishes ready E64 state.

[`PairedAdmission`](../../Pinwheel/Hardware/Storage/PairedAdmission.lean) proves
the token, lookup and per-word validation facts. `PairedSession` composes them
over any delivered history, with arbitrary quiet gaps before, between and after
commands. Quiet data need not be zero. The certificate permits producer-chosen
parameter locations and arbitrary unused 20-bit table entries.

`upload_admitted` and `retained_upload_segment` also apply to replacement from
any stopped initialized controller. The old bank and mailbox need not be empty;
the earlier storage and lifecycle theorems retain their guarantees. A running
controller or a malformed/interrupted session is outside this success theorem,
and remains covered by the existing arbitrary-command ownership invariant.

## Explicit boundaries

The SRAM behavior law remains a theorem parameter, not a new global axiom.
`Serial.Session` is a digital delivery contract. The subsequent execution
segment retains `init = 0` and `command != 3`; a replacement starts another
certified segment. E64 supplies execution state and busy, while loader status
and speculative addresses retain the actual graph's interpretation. This is
not an independent E64 specification of loader status.

Resident SHIFT/KEEP extensions, analog sampling, RTL-emitter correctness,
CIRCT/synthesis, and complete source-to-GDS correspondence remain separate.
The [SRAM proposal](../../physical/fixtures/sram-trust/contract.json) is unchanged:
the 0.260/0.200 µm resistor-width disagreement and incompatible delivered fast
operating conditions remain unqualified. Neither A nor B is accepted.

## Validation and reproduction

```sh
python3 scripts/check-paired-formal.py --tag paired-admission-fresh \
  --retained-manifest physical/experiments/paired-validation-mapping.json
```

Use a fresh tag. Schema 6 adds admission controls and the complete session
theorem while preserving all older report identities. The runner checks the
default library build, import reachability, the whole-library axiom audit, an
injected unapproved axiom, prior graph/upload/runtime/timed/package controls,
and fresh emission identity against the retained mapping artifacts.

The new [finite controls](../../test/PairedAdmission.lean) run the retained core
with two certified parameter permutations and initially dirty storage. They
check **580 accepted pushes**, **168 quiet edges**, complete stored image contents
in both banks, and ready E64 state immediately after commit. Four executed
refusals cover a corrupted inactive capture parameter and premature commit in
each bank. Two canonical but wrong source guards fail the image certificate;
they are not claimed as hardware syntax rejections. The previous active image
survives replacement. The test does not replay all 290 words bit by bit; full
qualified serial admission is the universal theorem above.

The `paired-admission-01` receipt passes in **235.829 seconds**. It covers
**231 reachable modules** and audits **16,808 declarations / 8,757 theorems**
with standard Lean axioms only. The injected unapproved axiom rejects. All
existing graph, memory, upload, runtime, timed, package and schedule controls
pass; the new admission controls take 28.409 seconds.

Fresh core/package MLIR and assembly metadata remain byte-identical to the
retained mapping artifacts. The report freezes **253 source inputs / 18
artifacts** and confirms unchanged inputs during validation. The predecessor
host manifest/report, its 26 proof/test sources, and the SRAM proposal retain
their identities. Root imports and the runner have a new source freeze. The
full protocol executable suite was not rerun. All work remains local.

There are no hardware edits or CAD calls. Campaign usage remains **8,412.163
CAD seconds**, with three A routes used and two B routes reserved. The subsequent
integration gate is recorded in the
[combined acceptance report](../research/implementation-acceptance.md). It binds
this proof, eight actual host certificates, retained emitted implementation and
physical candidate by identity, with missing qualification explicitly refusing
acceptance. [Status](../research/status.md) owns the next formal and physical
obligations.
