# Clean-source validation admission

`clean-v1` is an explicit source-identity mode for the repacked branch. It admits
the hash-pinned projection in `physical/validation/clean-source-v1.json`, including
exact Lean, test-Lean, Python generator/producer and physical/tool membership.
The manifest records original commit `99f75b65`, its tree and bundle SHA-256,
and clean commit `31a8f62` as provenance. Those commits need not exist in a fresh
clone after a squash merge. Identical admitted source in rewritten Git history
can pass this identity check; a changed or extra scoped input cannot.

The original source-input rows come from `99f75b65`. The local archive helper
introduced at `31a8f62`, artifact-policy additions and recipe fixtures are listed
separately as admitted additions. The manifest pins the approved adapter replacements.
The new checker pins the manifest and verifies that its executed bytes match the
selected committed checker. Its execution source is recorded separately to avoid
a self-hash cycle. Future semantic/generator changes require a reviewed manifest
version; committing an arbitrary descendant does not admit its source.
The checker implementation is itself a trusted, reviewed validator. Recording
its committed bytes is provenance, not a mechanism that proves a malicious
rewrite of the checker correct or prevents it from disabling its own checks.
Checker changes therefore require code review as well.

Historical mode remains the default and keeps the original ancestry requirement.
Historical exporters and receipts remain unchanged and belong to the preserved
branch. To request the separate mode on a **fresh** raw/optimized operation:

```sh
python3 -B scripts/streaming_tt_opt_intake.py \
  --raw-gate /absolute/fresh-raw/report.json \
  --worker-config /absolute/fresh-optimized/config.json \
  --worker-report /absolute/fresh-optimized/report.json \
  --tag NEW_TAG --source-mode clean-v1
```

This command retains every existing committed archive, actual worker, native
kernel, private-axiom audit, runtime, generated-source, complete state/pin and
physical-Verilog reimport check. A manifest, a `passed` Boolean or a matching
6,039-state count cannot substitute for those checks. No old result is relabelled
as a new execution.

Clean recipe comparison uses two exact historical JSON fixtures and the existing
`bcfd…` SDC identity. The recipe ledger and permitted settings are unchanged.
The manifest and both fixtures are explicit producer dependencies, copied into
the read-only producer snapshot, included in its input hashes and consumed from
that snapshot. Candidate preparation and reopen bind the selected mode; there is
no fallback selected by file presence.

A foundation executed at `31a8f62` retains that execution identity. Reuse at a
later selected source requires the existing exact consumed-input and library
checks; the separate runtime companion and fresh raw/optimized proofs remain
required. This migration supplies no new Lean execution, runtime qualification,
CAD result, final-target correspondence, extracted timing or physical acceptance.
Machine-specific PDK/archive dependencies remain outside this portability change.

The synthetic controls use independent Git history without original commit
objects. Their positive result is source identity only. They also exercise
source/policy/adapter/manifest/membership drift, parent-repository leakage,
archive mismatch, fake pass, explicit staged-data use and historical refusals.
