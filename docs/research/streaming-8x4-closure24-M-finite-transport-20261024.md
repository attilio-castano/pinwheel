# Complete-M finite projection transport repair

The opaque-state execution reached the first mathematical failure at index3463,
`PhysicalGRTCanonicalDevice`: line8837 cannot transport the boundedness witness
from `nextTable (0 + (index.val - 0))` to `nextTable index.val`. The report
66b1910b8c9e96955febfd6040650af0fd05b0f6afe39b8797811bf2b352a8a1
and resource69bb242ef14d7ca1754d6637200687e0f929aabd90128e54b74e1f62ad1a723b
remain failed1, with3463 successful prefix modules, the failed module and502
unrun modules. This is an elaboration/transport failure, not an exhibited
counterexample to the device's boundedness proposition. No prefix is accepted.

The source is `streaming_tt_finite.finite_forall`, invoked by the unchanged
graph device/correspondence, clock and composition generators. Its correct
local equality `same : (⟨start + (index.val - start), ...⟩ : Fin count) = index`
does not rewrite a proposition whose Fin projection has already reduced to a
Nat argument. The single tactic becomes:

```lean
simpa only [same, show start + (index.val - start) = index.val from congrArg Fin.val same] using witness
```

The first rewrite retains Fin-argument propositions; the projected equality
handles Nat-argument propositions. Every public statement, concrete kernel
chunk lemma, domain, partition and arithmetic bound remains unchanged. The
`lean-proof` skill's one-tactic/error-first method applies; no `sorry`, new
axiom, skipped module or weakened audit is introduced.

Root's separate diagnostic02 checked original expected failure and this exact
single-tactic candidate on Nat and Fin propositions with257 indices,128-wide
chunks and the actual100000 recursion/8000000 heartbeat settings. Root then
compiled the entire corrected CanonicalDevice diagnostic in34.433s under the
original180s module allowance, with a fresh sibling object and sealed old
imports/runtime. Those are diagnostic results only; they cannot substitute for
the fresh complete generation, proof, whole audit and separate private pair.

The new `m_finite_transport` helper pins the original finite producer at
97e0f1f9b1f5d00331201ad9e439da9fd74a6735023bbc2086699eaba2499032.
It compiles an exact function copy with only the terminal template line changed.
For each complete finite theorem it reconstructs the entire original block from
that pinned producer and requires an exact byte match before replacing it with
the corrected copy. It requires exactly547 transport lines in seven modules:
Canonical/Original/ActualDevice49 each; ClockDAGProof192; ClockInventory16;
Original/ActualProof96 each. Every remaining module must remain byte-identical.
An unknown, omitted, shifted, duplicated or foreign finite block rejects.

The new GEN04 adapter calls that transformation before `source_layout`, where
fresh source hashes are computed. Both `_generate` and independent `derive`
take this same path and bind the transformation certificate, source pins and
all changed/unchanged module identities. No generated file or historical
manifest is patched after staging. The original formal interpreter source
closure and its historical commit remain separate from the new proof-transport
producer; new adapter bytes are explicitly sealed in fresh adaptation inputs.

`finite_m` is a new typed generation/preparation authority. The new
`m_finite_isolation` and `finite_m_execute` compile the previous opaque-observer
operational bodies into fresh namespaces with every M binding pointing to
`finite_m`, including the child complete `M.verify(True)`, parent verification,
positive/private and independent readback functions. The previous modules'
globals remain unchanged. A fresh3966-source owner with zero cached objects,
395 immutable N imports, all6039 states/24 outputs/actual clock-reset/CTS and
packing contracts,14923-file runtime before/after, exact imports and complete
whole-owner/private-axiom checks are still mandatory.

The new budget schema honestly records `mathematical_sources_unchanged=False`,
`mathematical_statements_domains_chunks_unchanged=True` and
`proof_transport_tactics_changed=True`. Exact180s/default, six600s named modules,
4h whole-job,4GiB aggregate, one-thread and private/wire reserves are unchanged.
The opaque scheduling telemetry observer and canonical compiler body are exact
aliases/copies of their frozen predecessors. All prior source, objects, receipts
and diagnostic outputs remain immutable and outside fresh acceptance imports.

Portable HOST controls cover both projected and Fin propositions, all indices
and tails, exact547/7 membership, one-line-only source differences, refusal of
typos/omission/duplication/shift/foreign proof, generation hook ordering, new
M/global/source ownership, complete execution-body equality after new context
and budget metadata normalization, and unchanged Native/private/timeout gates.
HOST controls do not execute Lean, CAD or full mathematical source generation.
