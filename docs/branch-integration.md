# Chip-contract integration record

Recorded 2026-09-23; integrated on local main in `f0be558` on 2026-09-24.
This is the review record for `codex/chip-contract-consolidation`, not a live
work queue. [Research status](research/status.md) owns the current decision.
The sections below preserve the dependency order and the separation of reusable
infrastructure from experimental implementations at integration time.

The objective is a reloadable protocol engine with specified pin timing,
capture, branching and atomic program replacement. The integration connected
that behavior to storage schedules, emitted hardware, mapped ownership and measured
physical distribution. Physical closure remains open.

## Review in dependency order

| Milestone | Main owners | What to review |
| --- | --- | --- |
| Shared composition, admission and results | `Loader/ProgramImage`, `Compile/Readiness`, `NetlistInputs`, `NetlistTools`, `Feeder`, `Observer`, `HostResult`; shared validation and host helpers | Separate program encoding from storage rules; preserve core behavior while defining retained result ownership and generic composition. |
| SRAM and fetch organizations | `Memory/Sram`, `Storage/Sram*`, `MapTile`, `TiledMap`, `TiledController`, `FetchContract`, `UploadPipeline`; SRAM/tile checkers and host CLI | Separate memory behavior, controller refinement, actual emission and electrical cost. Keep the upload stage and tiled candidates explicit. |
| Paired execution | `Storage/PairedController`, compact/paired Python models, compiler, mapping and vector checks | One SRAM response supplies both possible successors. Preserve the modeled E64 operation/capacity contract while identifying the changed upload format and incomplete proof chain. |
| Physical tooling | `physical_target`, `physical_route_intake`, connection/distribution/path/organization helpers, bounded runners and independent checks | Bind semantic owners to actual artifacts; check permitted edits, complete affected scope, source identity and numerical budgets. |
| Experiment records | `physical/targets/` and `physical/experiments/` | Keep target inputs, exact edit recipes and result summaries distinct. A passed collection or local check does not mean the candidate passed whole-chip qualification. |
| Documentation | This guide, architecture, validation, status, results and journal | Give each decision one current owner; retain historical evidence without treating its next-step text as a current instruction. |

The hardware modules above live under `Pinwheel/Hardware/` unless qualified
with `Compile/`; Python tools live under `scripts/`. The portable audit now
includes `PairedController` through `Pinwheel.lean`. Auditing that module does
not select it as the host default or complete its missing refinement proofs.

## What is retained and what is experimental

**Retained interfaces:** shared composition, storage admission boundaries,
host result ownership, validation receipts, typed physical ownership and
independent edit checks. Their guarantees have the scope of their proofs and
tests, rather than an implied guarantee about every implementation using them.

**Reference and comparisons:** the unrestricted two-port flip-flop chip remains
the logical reference. The one-port chip enforces readiness and cannot run the
current UART receiver. Hybrid SRAM and the earlier repaired physical chip remain
comparisons. The host CLI continues to default to the hybrid backend.

**Active experimental architecture:** the full-capacity paired controller uses
one 512×64 SRAM and banked parameters. Conditional schedule lemmas, finite
model/RTL traces and mapped equivalence support it. A universal compiler theorem
and composed admission/package refinement are still open. Its 290-word upload
is distinct from the host's E64 upload protocol; adding it to the default Lean
audit is not host integration.

**Other experimental alternatives:** the restricted compact encoding, direct
SRAM comparison, map tiles and upload pipeline retain their individual
dispositions in [results](research/results.md). A rejected configuration stays
useful evidence; it is not a blanket rejection of its underlying idea.

**Physical result at integration:** the locality candidate improves its six
targeted connections, but fails whole-chip timing/electrical qualification and
has 33 coarse-routing overflow units. The saved-chip comparison separates
control data delay, SRAM launch-clock delay and input capture-clock delay.
The diagnosis proposed expanding the inventory to 1,152 connections; it did not
change production admission or select another repair. The subsequent
[organization study](physical-organization-study.md) verifies those 1,152
connections and finds no complete candidate within the bounded exchange policy.
It adds reusable timing obligations and replica costs, retaining regional
decoding for an explicit structural comparison.

## Evidence and reproduction

Source, tests, selected summaries and exact experiment recipes belong in Git.
Generated netlists, physical databases, raw logs, local study scripts and large
receipts remain under ignored `build/`. Tracked manifests bind those local
artifacts by identity; committing a manifest does not distribute its evidence.
A fresh checkout can run the portable gate, but cannot replay every physical
study without regenerating or obtaining its matching artifacts and pinned tools.

Run the [portable Python and Lean checks](validation.md#local-pre-push-checks)
before integrating code. Run affected emitted-hardware checks when circuit
behavior changes. Physical execution needs its own bounded, identity-bound
recipe. Keep model proof, RTL equivalence, local physical estimates, whole-chip
global routing, extracted timing and silicon results separate.

Historical source hashes remain historical. This consolidation preserves the
experiment manifests and recipes; it does not rewrite their receipts to claim
that a newly audited import or updated document was present in an earlier run.
The consolidation's isolated Git-index snapshots and validation receipts live
under `build/validation/branch-consolidation-01/`.

## Open gates identified at integration

Two independent gaps were identified at integration. Consult
[research status](research/status.md#next-discriminators) before allocating work:

1. **Complete the paired behavioral correspondence.** Connect the encoder and
   accepted uploaded image to the controller's execution and package contract.
   Existing conditional lemmas and finite traces identify useful intermediate
   obligations; they do not finish this chain.
2. **Compare complete physical organizations.** The bounded grouping screen is
   complete. Obtain the missing decoder-parent measurements and opposite timing
   checks, then cost regional tree replacement/reuse and local decoding with
   explicit clock-delivery obligations. Preserve passing neighbors and global
   capacity checks before selecting a bounded physical candidate.

The physical experiments' 0.3% incremental area allowance, timing floors and
20% electrical reserve are comparison-specific contracts, not universal chip
design rules. Do not relax them silently or reuse them as guarantees for a new
organization. A screen that finds no supported candidate should record that
result and reopen the organization choice rather than automatically launching
another detailed route.

Detailed routing, antenna/layout checks, extracted timing, physical power
qualification, board validation and submission completion remain separate
obligations. Licensing remains pending. This consolidation changes neither the
hardware defaults nor the execution contract.

## Consolidation validation

The code and experiment-record milestones were committed in this order:

- `fe6abab` — shared contracts
- `7d3dc27` — sram and fetch
- `c9e7391` — paired execution
- `551b071` — physical tooling
- `e927b77` — experiment records

This guide and the indexed research documentation form the final milestone.
Each code milestone was checked as an isolated staged-source snapshot; the
physical-tooling snapshot was checked before staging and then matched against
all staged source blobs. The first Lean build was clean; later snapshots copied
only a previous validated build cache and rebuilt their current sources.

The complete Python suite ran **408 tests: 406 passed, two Linux-specific checks
were skipped on macOS**. The final Lean library includes **206 modules**;
its audit found **15,395 declarations and 7,706 theorems**, including generated
ones, with standard axioms only. The injected custom axiom was rejected.
Paired graph rejection controls and both conditional schedule studies passed.

All **32 foundation model suites** completed across bounded runs. The original
aggregate invocation reached its **1,200-second** wrapper limit during Memory
after 29 suites passed. Its runner reported unconfirmed termination; an
independent process-table and process-group probe then confirmed the exact
group absent. Memory, SerialUpload and HostResult subsequently passed with
separate **600-second** limits. The interrupted aggregate invocation retains
its timeout receipt and has no success receipt; `foundation-completion.json`
records the combined integration result and unchanged source identities.

All **76** new experiment JSON records parse, and all **39** manifests carrying
a local report hash match their original reports. All 88 records in that
milestone retain their initial bytes. These checks preserve historical evidence;
they do not rerun emitted-hardware equivalence or qualify physical closure.
The initial 283 pending paths, per-milestone trees, commands, timeout, completion
and commit records are retained under `build/validation/branch-consolidation-01/`.
