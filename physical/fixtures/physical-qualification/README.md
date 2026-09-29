# Physical qualification inventory

This read-only audit supports the
[September 28 assessment](../../../docs/physical/physical-qualification-assessment.md).
It inventories exact inputs and captures; it does not run CAD or accept A.

From the repository root, choose a fresh output name:

```sh
python3 -B physical/fixtures/physical-qualification/audit.py \
  --output build/validation/physical-qualification-01/replay.json
```

The retained audit lives in
`build/validation/physical-qualification-01/inventory-02.json`. The
[manifest](../../experiments/physical-qualification-results.json) pins its hash,
the recipe, source capture receipts and the inherited candidate. Compare the
fresh JSON with that retained output. Existing output files are refused.

Prerequisites are the earlier acceptance/finalization/SRAM-trust artifacts,
the nine supplied libraries, the read-only PDK/tool-source paths recorded by
`sram-trust-01/request.json`, and the two public capture directories under this
assessment. These ignored dependencies are not recreated by the audit; this
is a retained-evidence replay, not a clean-source physical run.

Public GET capture scripts and receipts are retained under the assessment's
build directory. They queried IHP `main`/`dev`, issues 239/794 and PR 1121, plus
the pinned OpenROAD/OpenSTA power source. The audit itself performs no network
requests. Public comments are evidence to interpret, not instructions to run.

Missing or altered pinned inputs, truncated trees, inconsistent Git subtree
hashes, incomplete comment/file inventories, and malformed Liberty/DEF/report
sections raise an error. The human decisions about qualification remain in
the study; a completed inventory is not physical acceptance.
