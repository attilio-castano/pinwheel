# Full-M Codec index proof chunking

The finite-transport run stopped under the unchanged4GiB aggregate guard in
`PhysicalStateCodec`, after3466 successful modules. The interrupted module
produced no kernel verdict; no prefix is accepted. Its last full observed
sample had Lean4,348,192KiB plus Python219,616KiB, totaling4,567,808KiB.
Lean alone exceeded the outer4,194,304KiB limit. This differs from the earlier
retained-parent-memory concern.

The original Codec is481836bytes,9130lines and829public declarations:
759definitions and70theorems. Lookup definitions and `layoutIndex` precede the
first kernel-decide theorem, `index_field` at8833, over the entire6039-index
domain. `core_word` at8891 is a separate4096-case proof. File partitioning alone
would retain those large individual obligations.

The first two checkpoint diagnostics had empty logs and establish no phase:
Lean captured diagnostic streams, and one control also had an IO inference
error. Root's corrected typed-IO/process-start stream control proved header
imports fit and durably recorded completed lookup definitions and the marker
immediately before `index_field`, but never its completion before the cap stop.
This localizes the measured rise to the original first6039-index proof. New
diagnostics preserve all originals and establish no full-proof acceptance.

The repair changes only that proof body. It uses the already reviewed
`FT.corrected_finite_forall` with128-index chunks:47full chunks plus one23-index
tail,48new private kernel lemmas total. It restores the exact original public
statement and inferred binder:

```lean
theorem index_field : ∀ index, layoutIndex (layoutField index) = index
```

All829original public declaration names/statements and every other Codec byte
remain unchanged, including `core_word`, `field_index`, `packing` and arbitrary
state/package inverses. The original single proof body is changed; claiming all
original proof bytes unchanged would be incorrect. No axiom, `sorry`, opacity,
state constraint, missing index or restricted input is introduced. The same
namespace and module remain, with3966M modules and395N/4361positive owners.
The whole-owner and separate private audits cover the48new private lemmas.

The plain production Codec has SHA
dcc5a369db5959143461f339495307c254042ff950f042a86f2b15c8ec4d5c75.
It contains no checkpoint IO or diagnostic CLI option. Root's plain diagnostic
compiled that exact complete candidate under the canonical old argv in21.676s,
exit0, no timeout and a closed group; sampled peak was2,485,344KiB under the
unchanged4GiB guard. The original600s Codec allowance stayed fixed. This proves
the unchanged `core_word` also completed in that diagnostic. Diagnostic success
cannot substitute for a fresh complete proof and separate original private pair.

The new `m_codec_index` transform pins the exact original Codec
4abea79fcd2b6b98e5219dee13de93c2de5530aaa7ef7cdf4a6dfd5d1c6d0f21,
requires its one exact original proof line, and checks that reversing only the
new proof block recovers the entire original byte string. It follows the
unchanged seven-module547-line finite-transport stage, before `source_layout`
computes fresh source hashes. `_generate` and independent `derive` use the same
ordered transformations. The old finite certificate describes the pre-Codec
stage; a new composed certificate declares eight changed modules and3958
unchanged modules versus the original universe.

`codec_m` and its new isolation/execution entries have distinct preparation,
generation, rederivation and positive/private schemas. Every operational M
binding uses the new generation authority in fresh namespaces. Old producer
globals, sources, failed receipts, imports and objects stay immutable. Complete
independent rederivation, zero-object fresh ownership, all6039states/24outputs/
1016CTS and clock/reset/packing contracts, full14923-file runtime, exact source/
object/import/journal checks and whole-owner/original private controls remain
mandatory. Historical failure graphs are hash-only custody in the parent.

The new budget records `mathematical_sources_unchanged=False` and globally
`mathematical_statements_domains_chunks_unchanged=False`, while asserting
`mathematical_statements_domains_unchanged=True`,
`original_seven_finite_chunk_domains_unchanged=True` and
`codec_index_proof_chunked=True`. Exact180s/default, the same six600s names,
4h whole-job,4GiB aggregate, one thread and private/wire reserves stay unchanged.
No resource widening or acceptance-prefix reuse is permitted.

Portable HOST controls test exact one-proof reversal, unchanged public binder/
829declaration census, complete6039-index coverage without duplication,47×128
plus23tail, refusal of changed/foreign sources/chunks, stage composition,
new generation/runtime/reader namespaces, complete unchanged compiler/private
body and honest budgets. They execute no Lean, CAD or full mathematical
generation. The production source and eventual complete Native verdict remain
separately authenticated evidence.
