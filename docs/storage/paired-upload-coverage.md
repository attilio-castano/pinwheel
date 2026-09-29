# Paired upload coverage

On **2026-09-28**, the paired loader acquires a checked connection between
**accepted host words and the image actually stored in the active bank**.
This closes the upload and committed-image obligations from the
[first graph/package gate](paired-formal-correspondence.md). The retained
controller and emitted hardware are unchanged.

For the complete design iteration, this removes a specific assumption: we no
longer need to assume that an upload somehow produced the certified image in
memory. After initialization, the controller can mark an image valid only when
its storage agrees with a complete accepted transcript. Execution timing and
physical SRAM qualification remain separate gates. [Research status](../research/status.md)
owns the next decision.

## What is proved

The upload contains exactly **290 words**:

| Accepted offset | Destination in the inactive bank |
| --- | --- |
| 0–31 | 32 parameter registers, 20 bits each |
| 32–287 | 256 SRAM rows, 64 bits each |
| 288 | Boot token, 32 bits |
| 289 | Idle configuration, 6 bits |

The proof maintains a **ledger of accepted words**. This is mathematical state,
with no extra hardware storage. Its staged length equals the accepted cursor;
every slot below that cursor contains the corresponding word's low bits. A
valid active bank matches a complete 290-word transcript. Begin, abort and reset
discard the staged transcript without claiming to clear physical contents.
Rejected words do not advance it, and commit selects the completed transcript.

| Connection | Proof owner |
| --- | --- |
| Accepted prefix, complete commit and preservation through arbitrary commands | [`PairedLoader.invariant_next`](../../Pinwheel/Hardware/Storage/PairedLoader.lean) |
| Actual acceptance/commit signals and next control state match that protocol | [`PairedUpload.push_value`, `commit_value`, `control_next`](../../Pinwheel/Hardware/Storage/PairedUpload.lean) |
| Actual parameter, SRAM, boot and idle updates match transcript offsets | `PairedUpload.banks_next` |
| Every write preserves the previously active bank, including metadata | `PairedUpload.active_storage_preserved` |
| Every finite decoded-command history after initialization satisfies the invariant, from arbitrary registers, contents and Q | [`PairedCoverage.initialized_run`](../../Pinwheel/Hardware/Storage/PairedCoverage.lean) |
| Erasing the ledger recovers exactly the existing closed graph/SRAM model | `PairedCoverage.physical_run` |
| The retained typed controller has the same invariant under an explicit SRAM contract | `PairedCoverage.retained_initialized_history` |
| An E64 certificate for the accepted transcript describes the actual resident image | `PairedCoverage.certified_image` |
| An enabled read, given a valid active image, returns that image's row for the token installed on the edge | `PairedCoverage.read_response` |

Acceptance is derived from the actual graph, including its word validation.
The proof does not assume that every supplied word is good. The recorded data
is also tied to the actual command input, rather than a free internal wire.
The SRAM response theorem distinguishes the old Q consumed before an edge from
the new Q produced by the read. Idle and write edges retain their existing
hold behavior.

## Boundary and next gate

**Follow-up:** the [running-state gate](paired-runtime-ownership.md) now closes
item 1 below. Its proof finds that every edge whose result is running performs
a read; Q-hold behavior occurs outside that running guarantee. It also connects
actual successor selection to the source instruction. The dated obligations
below explain this checkpoint; full timed control refinement remains open.

These history theorems start at the **decoded command boundary**, after an
initialization edge. The earlier package composition theorem remains available;
a claim about successful host delivery still needs its delivery conditions.
Arbitrary power-up registers, SRAM contents and Q remain allowed.

The memory behavior law is a parameter, not a new global axiom. Its application
to the supplied macro still requires the physical component evidence described
in the [contract proposal](../../physical/fixtures/sram-trust/contract.json).

The next formal gate is the controller's timed execution of the certified image:

1. Maintain the running-state invariant: active image validity, current token,
   cached parameter, and usable Q belong together on every execution edge,
   including edges when memory holds Q.
2. Derive the actual dispatch edge and branch choice from capture, guard,
   countdown and wait behavior; connect those choices to `PairedImage.Corresponds`.
3. Prove start, halt, fault, timeout and reset preserve the required pin timing,
   then compose with the existing package proof and host-delivery conditions.

An enabled-read theorem does not establish all-cycle Q availability or timed
E64 execution. RTL emission, synthesis, physical macro behavior, fast-corner
compatibility, accepted A/B and clean-source physical replay remain outside
this result.

## Validation and reproduction

```sh
python3 scripts/check-paired-formal.py --tag paired-upload-fresh \
  --retained-manifest physical/experiments/paired-validation-mapping.json
```

Omit the optional manifest argument when the historical local artifacts are
unavailable. Each run requires a fresh tag and records all proof/test source
hashes. The [manifest](../../physical/experiments/paired-upload-results.json)
binds the current receipt and the earlier gate without rewriting old receipts.

The runner builds the complete library, audits every library declaration's
axioms, rejects an injected axiom, and checks the existing graph/package and
memory controls. The new [retained-controller controls](../../test/PairedUpload.lean)
exercise two complete images, all storage slots, malformed words in every
region, short and extra uploads, busy commands, abort, both reset forms,
restart, replacement, reinitialization, row 255 and old-Q dispatch.

The first attempted receipt, `paired-upload-01`, correctly failed the axiom
audit: a bit-vector tactic introduced a compiled-check assumption. The proofs
were rewritten with explicit finite cases, bit-vector lemmas and arithmetic.
The audit policy is unchanged; the failed receipt is retained. The subsequent
`paired-upload-02` receipt records the passing build, whole-library audit,
controls and emitted-artifact identity check in **26.192 seconds**. The library has **215 reachable
modules**, **16,152 audited declarations / 8,219 theorems**, with only the standard
Lean axioms. The full protocol executable suite was not rerun.

There are **zero CAD calls**. The chip, installed PDK, proposed SRAM contract
and earlier physical evidence are unchanged. Campaign usage remains
8,412.163 CAD seconds, with three A routes used and two B routes reserved.
