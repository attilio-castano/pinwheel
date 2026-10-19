# SPI source-to-circuit proof session

Authorized 2026-10-16. Started 2026-10-17 00:00:31 UTC (October 16,
8:00:31 p.m. Eastern). Hard stop: 2026-10-17 12:00:31 UTC (October 17,
8:00:31 a.m. Eastern). Branch: `codex/spi-source-circuit-proof`.

## Target

Connect the existing typed mode-0 SPI interpreter to the packed Reactive
circuit and compose with initialized digital SRAM execution. The source family
has one through four bytes and half-periods of three through 256 clocks. The
execution boundary is one admitted START followed by command-zero clocks with
arbitrary raw inputs. Include insufficient TX/RX fault prefixes, sampler
alignment at START, terminal state abstraction, counters and packed buffers.

The state relation must derive observable agreement rather than assume it.
No RTL, serial ABI, physical artifacts or historical receipts are changed.
Serial packet delivery, repeated START/RELEASE/reset lifecycle, universal Python
compiler correctness, RTL refinement and physical qualification remain separate.

## Work and evidence gates

1. Specify the relation and challenge the hardest START, loop and fault cases.
2. Kernel-check buffer representation and initialized loaded-geometry lemmas.
3. Prove START and one-edge preservation, induct over arbitrary prefixes, and
   compose with the existing initialized SRAM theorem where justified.
4. Run focused meaningful controls, the whole-library axiom audit including
   injected-axiom rejection, and the full foundation gate. Preserve source
   identities and validation logs in a fresh session output directory.
5. Commit validated stages. Reserve the final two hours for validation,
   independent review and a morning report with exact remaining gaps.

The session stops early on completion. At the deadline, incomplete obligations
remain explicitly open; partial lemmas are not reported as the complete bridge.
Only local development and commits are authorized; no CAD, push, pull request,
external publication or paid service is part of this session.

## Session state

Initial checkout `a2bbdb122d2212ef0221fea6179ba83cc616eb9d` was clean.
The pinned Lean toolchain is `leanprover/lean4:v4.33.1` and is installed locally.
The initial library build establishes the local dependency cache. Parallel work
owns separate packing and loaded-geometry modules; the main bridge and final
integration stay with the session owner.

## Closeout

All required gates had passed by `2026-10-17 01:08:06 UTC`, about 68 minutes
after launch. The initialized SPI theorem is checked, locally committed and
independently reviewed; the focused gate, full foundation gate and Python suite
pass. The twelve-hour limit is a maximum, so work stops on completion.

The [morning report](spi-source-circuit-morning-report.md) owns the exact scope,
validation receipts and hashes, commit entry points and remaining gaps. The
local proof milestone is `9721a91`; validation tooling is `5014bb2`. No CAD,
push, pull request or external publication was performed.
