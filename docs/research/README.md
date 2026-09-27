# Research workflow

Start at [status](status.md). Research should reduce a named uncertainty and leave
an evidence-backed decision that another person or agent can recover without the
conversation. This workflow applies to interpretation, literature review, Lean
proofs, RTL experiments, and physical validation; it does not launch work or grant
authority beyond the user's approved scope.

## Record ownership

| Record | Owns | Update when |
| --- | --- | --- |
| [Status](status.md) | Active question, current belief, next discriminator, scope | A result changes the next decision; rewrite rather than accumulate history |
| [Results](results.md) | Completed conclusions, limitations, reopening conditions | A study reaches an interpretable conclusion |
| [Journal](journal.md) | Dated decisive receipts and interrupted-attempt references | A milestone or attempt needs a durable reconstruction path |
| [Technical studies](../README.md) | Detailed models, experiments, measurements, reproduction | The corresponding implementation or evidence changes |
| This workflow | Durable research rules | Experience demonstrates a rule needs changing |

Current priorities have one owner: status. Old plans describe their historical
context. Results link to detailed studies rather than copying their tables. A
negative result remains useful even if its implementation is never adopted.

## The bounded loop

1. Recover the active question, strongest relevant evidence, baseline, and actual
   checkout state. Read only the technical owners needed for the decision. Check
   for work already in progress before changing shared files or starting a run.
2. Name competing explanations and the smallest useful discriminator. For an
   attribution claim, change one primary factor; a multi-factor search must say so.
3. Before execution, record the comparison, correctness contract, evaluation
   identity, expected cost, resource limits, and stop conditions. Reuse authority
   already granted. An absent budget is unknown, and a new run tag does not reset
   cumulative resource use or authorize external work.
4. Implement and verify within that scope using the existing domain runners. For
   a replacement backend, establish the relevant correspondence before advancing
   to expensive measurements. Preserve unsuccessful and interrupted attempts.
5. Interpret what the result supports and what remains unresolved. Separate a
   broken tool or invalid comparison from evidence against a hardware hypothesis.
6. Write back the result, evidence location, changed belief, and next allocation.
   Continue within the approved bounds when there is a useful next question.
   Stop when the scope, budget, or evidence prevents valid continuation.

For interpretation or reading alone, use a short note in the relevant study;
there is no requirement to invent a campaign, trial, or implementation task.
Local edits and commits, remote execution, publication, and changes to defaults
retain their actual task authority. A record describes permission; it cannot issue it.

## Exploration with temporary size overages

User direction on **2026-09-25** permits temporary size/area overages while
exploring architectural ideas, provided they are recorded. An early candidate
may exceed a repair experiment's area allowance or the eventual chip size target.
Size alone should not eliminate an idea before its benefit can be understood;
the first useful implementation may become smaller through later optimization.

For such an experiment, record the idea being tested, the original target and
reference, candidate size, and the absolute and percentage overage. Distinguish
estimates from measurements; mark unknown costs until measured. Record the
observed benefit, other regressions, and possible reductions or the next
optimization question. A complete shrinking plan is not required in advance.
Keep a reproducible baseline and the original acceptance results alongside the
exploratory result. If the floorplan or other comparison conditions change,
record those changes as well.

An oversized candidate can establish a useful architectural result while still
failing final size qualification. Final acceptance retains its applicable size,
behavioral and physical requirements. This standing direction removes size-only
approval stops within the authorized exploratory work; CAD runtime and resource
budgets remain separately recorded. Progress is judged by what the experiment
teaches and whether further development is justified.

## Experiment record

Use this small template in the owning study or a retained run-local brief. Link it
from status rather than keeping another live plan. Existing runner receipts supply
hashes and counts; do not duplicate them by hand unnecessarily.

```text
Study / run identity; date; planned, running, interrupted, or closed:
Question and decision this experiment could change:
Hypothesis, competing explanation, and decisive prior evidence:
Baseline and candidate source identities; intended change:
Fixed semantics, workload/capacity, timing/area boundary, and controls:
Evaluator, toolchain, library/PDK, configuration, and seed identities:
Proof obligations, independent checks, metrics, and acceptance gates:
Approved effects; attempt/time/memory/concurrency limits; cumulative use:
Artifact location, progress/cancel method, and stop conditions:
Observed result and exact receipt identity:
Evidence verdict: supported / unsupported / inconclusive / invalid:
Allocation: continue / revise / defer / retire / await authority:
Limitations, reopening condition, and next discriminator:
```

These are descriptive fields, not a new schema or runner. A semantic proof can
pass while a performance hypothesis fails. A correct candidate can be deferred
because its measured gain does not justify another routing run.

## Evidence standards for hardware

- **Lean:** name the theorem, modeled inputs/states, invariants, and axiom audit.
  Exact pin/capture edges and atomic loading remain part of the current contract.
- **RTL simulation:** name the independent oracle, coverage, defined-bit boundary,
  and detected mutations. Finite regression is not universal translation proof.
- **Mapping:** record full-core scope and constraints. Cell sums and ABC estimates
  do not establish routed area or clock frequency.
- **Physical validation:** identify final netlist, parasitics, libraries/corners,
  SDC, floorplan, and flow settings. Compare fresh extracted setup/hold, electrical
  limits, layout checks, and implemented-netlist behavior. Partial states may
  inherit stale metrics; distinguish them from final extracted evidence.

Keep baseline and candidate comparable. Do not hide a timing failure by changing
clock/I/O constraints, declaring an unproved false path, narrowing accepted
programs, or inserting protocol cycles. A deliberate contract change is a new
comparison. Corrections to the evaluator or constraints require a new identity
and reconsideration of affected results, not relabeling the old measurements.

## Outside research

Record the question, primary source and revision/access date when known, relevant
idea, assumptions, applicability, and adoption decision in the owning study. Name
what we implemented versus what merely inspired it, and what evidence could
justify further work. The [timed-component sources](../engine/timed-components.md#sources-and-next-application)
and [storage primitive review](../storage-primitives.md) are existing examples.
Do not fabricate missing historical access dates or imply that a source was
rechecked online during a documentation consolidation.

## Artifacts and closeout

Keep generated logs, traces, MLIR, RTL, netlists, reports, and intermediate state
under their existing ignored `build/` owners. Source, tests, concise conclusions,
and selected compact manifests such as [fetch-results.json](../../physical/experiments/fetch-results.json)
belong in Git. This workflow adds no archive service or retention/deletion policy.
Ignored local artifacts are not a durable backup; a digest identifies evidence
but cannot recover a missing file. Report missing evidence rather than recreate
it under the old run identity.

Use fresh run tags where runners support them. Some older runners overwrite their
success receipt; inspect that behavior before rerunning and preserve any evidence
needed for an existing comparison in an approved separate location first. Keep
failed attempts and retries distinct. Record measured resource use when available;
otherwise label it unrecorded. Historical commit dates are not experiment timestamps.

At closeout update the technical study, results, a concise journal receipt, and
status as applicable. Change this workflow only for a durable lesson. For docs-only
work, check relative links, source/commit references, contradictory status, and
`git diff --check`; avoid rerunning physical or proof suites solely for prose edits.
