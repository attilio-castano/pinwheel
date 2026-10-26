# Expanded-domain reference proposal

**Historical proposal:** its unchanged-kernel E64 wording below was superseded
by corrected proposal02. The old kernel has an explicit16/32 domain guard.
Read [the new bound kernel and prepared authority](streaming-8x4-rc-reference-expanded-20261023.md) for the current source admission and strict budget gates.

This is proposal only. No source implementation, new field solve, Native call
or consumer comparison is authorized by this document. It preserves the current
reference-only02 experiment and its failed TopMetal1 domain gate.

The four actual closed TopMetal1 self children are numerically/resource-valid.
Their .02um fine values are 87.3079980pF/m at E16 and 83.1065083pF/m at E32.
Mesh change at E32 is .0416577%, while the E16→32 domain change is **5.0555484%**,
which fails the unchanged 2% gate. The field kernel grounds x=±E and y=0,E;
TopMetal1 reaches 7.4um, leaving 8.6um to the E16 upper boundary. Fine mesh
stability does not establish domain stability. This causal failure motivates
moving the physical far boundary while retaining the same acceptance tolerance.
These four closed children supply failure provenance, not complete-reference
or outer-resource authority while the original packet is still running.

Propose a distinct fresh full 32-grid experiment: all eight original nominal TYP
cases at h=.04/.02um and E32/64um. Recompute every E32 grid; reuse no numerical
prefix, cache, matrix or receipt. Keep every conductor rectangle, full material
stack, interface anchor, excitation, discretization equation and solver control
unchanged. The exact frozen `streaming_8x4_rc_all_layers_reference.solve` and
axis builder can be reused with explicit `maximum_nodes=70000`; no kernel or
axis edit is needed. Its solve-body SHA256 is
`a01b8ac269355e2e29d9f023258483ae72e312095c2a2f1d11b88996b82b3476`.

Independent HOST dry grids reproduce **68,817 maximum nodes** and 1,045,176 nodes
across 32 calls, with exact conductor/material anchors and positive spacing.
A proposed 70,000-node admission covers that fixed universe before any new solve.
The unchanged reviewed structural estimate gives:

```
70,000 × 4,096 bytes/node × 4 transient/allocator factor
+ 268,435,456 interpreter/worker reserve
+ 134,217,728 scratch
= 1,549,533,184 bytes
```

That leaves 597,950,464 bytes below 2GiB and 490,576,281 bytes below the 95% memory
guard. The estimate derives from the same nearest-neighbor operator/object/
CG-vector source counts as the reviewed 65k policy. It is neither measured RSS
nor a formal memory bound. Actual one CPU/2GiB/no-extra-swap/128PIDs,
128MiB scratch, cumulative cgroup peak, 95% preemption and zero max/OOM counter
deltas remain mandatory. A memory/resource/custody failure stops the suffix
and cannot confer complete numerical authority.

Keep 120s per leaf, 1800s work and 1860s outer, residual 1e-9, energy/flux 1e-7,
reciprocity 1e-7 and 6000 CG iterations. Empty child logs remain mandatory. Closed
numerical failures may be preserved while finishing the fixed universe; no
resource failure, incomplete prefix or failed reference may become a pass.
Complete full-matrix/ground mesh comparison at E64 and domain comparison
E32→64 must both meet 2% for all eight cases. Enlargement is a hypothesis, not
a guaranteed repair; any remaining failure stays failed without adaptive
E128 escalation or tolerance changes inside this experiment.

The old reference-only plan
`bd24cf673c33be53a2a83a1d4c27d3c14ea989208cfb8689a09d861baec69e32`
and every old producer/receipt remain intact. Its Top child leaves 20–23 and
their exact hashes are included in the immutable proposal. Original M1 FVM25
controls remain prerequisites. This new nominal 2D empirical experiment supplies
no finite BEM, rigorous continuum, full-model, process-corner, timing or foundry
qualification and does not admit the historical gated all-layer plan.

Consumer C commit `00e4d8a` remains frozen. It may measure its declared packet
while the old reference gate is blocked. A future comparison to an actually
passing expanded reference needs a **new separately typed HOST join** binding
both actual authorities, exact physical cases and all unchanged gates. It may
not edit the old consumer producer/reader or promote its old result.

The proposal is
`build/campaigns/8x4-20261022-01/rc-reference-expanded-proposal-01.json`, SHA256
`49b93e1a0d5225dbcb11a469d72ce2966600c418d55c4d74e40438c06c63b9a6`.
Its reproducible HOST-only builder is `propose-rc-reference-expanded-01.py` in
the same folder; it constructs dry axes and reparses already closed children,
without calling the field operator, CG, Native or a subprocess. Independent
review and explicit Root implementation/Native decisions remain separate.
