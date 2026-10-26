# Fresh actual-M adapter scope repair

The first context-generation attempt reached GEN04's final dependency check,
then failed normally before returning or staging complete M sources. No Lean
ran. The preserved producer at `final24-M-context-01/producer/generate.py`
captures the introduced outer dependency dictionary at line168, but the original
import-validation loop at line282 assigns each imported module string to the
same Python local `dependency`. At line291 the adapter compares a freshly
derived dictionary with the final imported module string. This is an adapter
scope bug, not a mathematical counterexample or a resource stop. The original
M01, context-generation01 and all their producers/requests/receipts stay intact.

The new adapter renames only the introduced context binding and its references
to `source_dependency_context`:

```diff
-dependency=D.dependency_context(config)
+source_dependency_context=D.dependency_context(config)
 ... introduced prepared/plan/config/worker lookups use the same dictionary ...
-bound_path(dependency['source_worker_config'])
+bound_path(source_dependency_context['source_worker_config'])
 ... original import-validation loop remains unchanged ...
-F.require(D.dependency_context(config)==dependency, ...)
+F.require(D.dependency_context(config)==source_dependency_context, ...)
```

Seven exact anchored substitutions affect the introduced capture, its ten
prefix field reads, explicit original-worker-config custody use and final
equality. The original `for dependency in line[7:].split()` and its complete
missing/later-import checks remain byte-identical. AST admission requires exactly
one assignment to the new descriptive name and no unresolved generator names.

The new entry points are `streaming_8x4_closure24_scope_m.py` and
`streaming_8x4_closure24_scope_m_execute.py`, backed by
`streaming_8x4_closure24_m_scope.py`. They adapt the exact prior isolated
controllers into another isolated namespace and use new
`pinwheel.closure24-scope-...` generation/preparation/positive/private schemas.
The three prior context producer hashes are mandatory, as are the existing
immutable base-controller hashes. All15 unique generation-producer source
seals include the new helper/entries, prior helper/entries and original bases.
`controller_source(kind)` returns the complete deterministic source and unified
diff for inspection without running generation.

The verified original→restored N worker-config authority is reused unchanged:
original prepared receipt `9205b15a...`, original/restored configuration
`d43a1ead636a48c3a42a60010b4f5f93e7969b24f20966c4b18a677bebf73adb`,
archive metadata `76c52229...` and relocated N02 `f97c0046...`. Both the new
preparation and manifest reopening retain the typed context checks. No dummy
configuration, historical receipt rewrite or removed custody seal is involved.

All6039 state transitions, all24 public outputs, clock/reset DAGs, packing,
initialization, source partitions/order, full rederivation, imports, ownership,
runtime observation, positive owner audit and separate private-control pair
remain unchanged. So do the default180s/exact600s compiler allowances,
4GiB/one-thread limits and four-hour positive job cap. Partial generation or
proof prefixes cannot pass.

Seven portable HOST controls pass normally and with `python3 -O`. The regression
extracts and executes the actual context-capture statement, original complete
import-validation loop and final equality as a tiny standalone AST probe. It
reproduces the prior failure, preserves the new dictionary while the loop still
finishes with module string `Std`, rejects a changed context, and still rejects
a missing import. Other controls compare the whole generated source after only
the introduced-name/typed-scope normalization, preserve the original loop AST,
check unique assignment, Native positive/private AST and helper/budget identity,
and reject prior-producer drift. No actual generator, Lean, CAD or ignored build
fixture is executed by these controls.

This packet is source-only. Root must independently review and commit it before
a fresh guarded generation owner such as `final24-M-scope-01`. Use the matching
new scope executor for any later positive/private/verify-private operation.
Neither previous failed directory may be reused. No generation, Root GO, Native
proof pass, physical acceptance or qualified timing is created by this repair.
