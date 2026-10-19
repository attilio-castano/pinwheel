# Local evidence cleanup — 19 October 2026

The local `codex/streaming-tt-clean` branch assembles the accumulated implementation from preserved commit `99f75b65fe524f266aa21654dc3d7f7054dd1aa8` directly on the recorded main commit `a2bbdb122d2212ef0221fea6179ba83cc616eb9d`. It excludes bulky execution archives from its new history. This changes storage and review scope; it adds no hardware, proof or physical qualification result.

The original `codex/streaming-tt-candidate` branch remains at `99f75b65`, with its two inherited uncommitted documentation edits unchanged. Safety branch `codex/streaming-tt-evidence-20261019` pins the same commit. The original ignored build artifacts remain in place and have not been deleted or rewritten by this cleanup. Their preservation in place is separate from the tracked-history bundle.

A self-contained Git bundle preserves the original committed history at:

`/Users/attiliocastano/.codex/worktrees/1373/pinwheel/build/local-cleanup/streaming-tt-clean-20261019-01/streaming-tt-original-99f75b65.bundle`

The bundle has **148,580,352 bytes**, SHA-256 `05a2be07f33ec5a401f87876336b2e7fb31c62ad7e6cb1a6e73822ca4fa7bf8a`. Exact copies of both dirty documents and their 1,588-byte patch are preserved separately in the same local owner. The bundle does not include ignored build artifacts or uncommitted documents.

## Selection

| Excluded tree under `docs/research/` | Files | Original bytes |
|---|---:|---:|
| `streaming-tt-routing-rc-tooling-20261019/` | 2,209 | 1,029,165,061 |
| `streaming-tt-renewal-tooling-20261018/` | 339 | 7,049,088 |
| `evidence/streaming-tt-20261018/` | 6,062 | 114,635,420 |
| **Total** | **8,610** | **1,150,849,569** |

All excluded files remain recoverable through their original Git paths, modes, blob IDs, lengths and SHA-256 identities. The [catalog and recovery guide](local-evidence/README.md) describe the explicit local verification and restoration commands. The generated index is bound by SHA-256 `2d4207e8627d06941e3747ddfaa599b06a9af64885685aa9fa52ce5b1ff30f25`.

The remaining original tree contains 3,157 files and 67,257,326 bytes before cleanup metadata and link edits. Existing design, Lean, generator and test source bytes are preserved. All October 17 compact evidence packages and existing regression fixtures remain. Three reports change only 20 link destinations to the recovery guide; their original complete bytes remain in the bundle. Cleanup also adds the retrieval tool and its tests, archive metadata, this report, scoped ignore rules and an attribute marking the generated index.

## Validation

- A fresh isolated bare import of the bundle passed Git object integrity checks. A separate reviewer verified all 8,610 indexed paths and all 5,363 unique blobs, including Git identity, raw SHA-256, size and tree mode.
- The installed retrieval helper independently imported the actual bundle into another fresh bare repository and verified every indexed payload. Four actual samples were restored into a new cleanup-owned directory, including the 58,870,672-byte ODB; all hashes, lengths and Git file modes matched.
- **111 compatibility tests** and **115 fresh-checkout portable physical-host tests** passed with no skips or failures. The physical-host suites allowed no child process or CAD execution and left the clean checkout without a build directory.
- **20 retrieval tests** passed, including tampered metadata/bundle/blob, unsafe paths, missing repository, symlink and overwrite refusals. The same 20 controls also passed under optimized Python in the implementation review.
- Source membership, documentation links, the clean branch parent and absence of the excluded payload from its new history are checked separately at commit closeout.

Git whitespace checking reports 11 inherited items in exact original source files and captured intake patches. Cleanup-authored files have no whitespace warnings. Historical source and fixture bytes were retained rather than edited to silence those observations.

Initial test collection encountered a Python standard-library `test` package collision and a multi-object JSON output parser mismatch. Corrected invocations passed without changing existing source or weakening tests. The retrieval corruption fixture was corrected to corrupt the object actually read by Git. Detailed validation outputs and the original staging-hook observation remain in the local cleanup owner.

Historical exporters enforce their original complete baseline contracts and should run on the preserved original branch. The new branch is not retroactively qualified by old commit-bound receipts. Original toolchain, PDK and ignored build dependencies remain necessary for historical Native replay. No new Lean, CAD or solver work ran during this cleanup. Everything remains local; nothing was pushed or published. Disk space has not been reclaimed because original artifacts and history remain retained.
