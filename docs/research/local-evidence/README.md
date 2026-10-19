# Local evidence archive

The clean source branch keeps source, tests, conclusions and compact evidence indexes. The excluded generated evidence remains in the preserved original branch and its Git bundle. Original ignored `build/` owners remain undeleted.

Preserved source commit: `99f75b65fe524f266aa21654dc3d7f7054dd1aa8` (`99f75b65`). Local bundle: `/Users/attiliocastano/.codex/worktrees/1373/pinwheel/build/local-cleanup/streaming-tt-clean-20261019-01/streaming-tt-original-99f75b65.bundle`, **148,580,352 bytes**, SHA-256 `05a2be07f33ec5a401f87876336b2e7fb31c62ad7e6cb1a6e73822ca4fa7bf8a`. The [archive catalog](archive.json) and [payload index](payload-index.jsonl) bind the bundle, source identity and original relative paths.

The bundle covers **committed Git history only**. Inherited dirty-document patch/copies and the original ignored `build/` evidence are separate preserved local material. Design, proof, generator and existing test sources retain the preserved commit's bytes. Cleanup adds the retrieval tool/tests, catalog and ignore/attribute rules, and changes report link targets. Existing report claims are unchanged. The clean branch is not retroactively qualified, and the archive is not a standalone CAD reproduction bundle: original tools, runtime, PDK and ignored build dependencies remain separately required.

Use the local helper to verify the bundle into a fresh repository path, then recover selected payload into a separate destination. These commands do not run archived code:

```sh
python3 -B scripts/local-evidence.py verify --bundle /Users/attiliocastano/.codex/worktrees/1373/pinwheel/build/local-cleanup/streaming-tt-clean-20261019-01/streaming-tt-original-99f75b65.bundle --repository /absolute/existing-parent/verified-evidence.git
python3 -B scripts/local-evidence.py restore --repository /absolute/existing-parent/verified-evidence.git --destination /absolute/separate/restored-evidence --path ORIGINAL_RELATIVE_PATH
```

The repository path must not already exist; its parent directory must exist. The same verified repository is used for recovery. Each recovered file is checked before publication; recovery of a set is not a single atomic transaction.

Repeat `--path ORIGINAL_RELATIVE_PATH` for additional files, or use `--all` instead of `--path` for the indexed payload. Keep original relative paths and bytes intact; consult the catalog/index for content hashes and scope. Restored payload in the clean checkout is ignored. Successful verification or recovery establishes custody, not Lean, CAD, solver or physical acceptance.

Historical evidence exporters enforce complete baseline contracts and should run on the preserved original branch. Missing evidence must be reported, never recreated under an old run identity.

Each heading below identifies a migrated link target using the first 12 hex digits of SHA-256 of its UTF-8 original relative path. This is a path identifier, not the artifact's content hash. Every target is from preserved commit `99f75b65`; recover its exact original path locally with the command above to inspect the historical bytes and their original scope.

### artifact-2d25b4fed8e3

Original relative path: `docs/research/evidence/streaming-tt-20261018/manifest.json`.

### artifact-4c248989ba0a

Original relative path: `docs/research/streaming-tt-renewal-tooling-20261018/closed-snapshot-08/README.md`.

### artifact-4bf01153abeb

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-11/build/streaming-tt-resources/streaming-tt-balanced-final-03/report.json`.

### artifact-236624056770

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-11/build/streaming-tt-recovery/routing-rc-final03-terminal-inventory-observation-01/report.json`.

### artifact-1d7403809fd7

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-14/build/streaming-tt-recovery/routing-rc-coordinate06-pure-closeout-observation-01/result.json`.

### artifact-e57ec46bf17e

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-12/build/streaming-tt-recovery/routing-rc-final03-external-full-replay-observation-01/result.json`.

### artifact-d1e9b826ad79

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-13/build/streaming-tt-recovery/routing-rc-coated-sphere-actual-pure-closeout-01/result.json`.

### artifact-c69b39ad47ba

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-12/build/streaming-tt-rc-research/aspect-U-diagnostic-execution-preparation-unqualified-01/host-dispatch.json`.

### artifact-899c736de97a

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-14/build/streaming-tt-recovery/routing-rc-U-link-accuracy-failed-workflow-observation-01/report.json`.

### artifact-f420fd0a7dfc

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-14/build/streaming-tt-recovery/routing-rc-renewal-20261019-rc-closeout-refresh-01/report.json`.

### artifact-8ba565c373a1

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-14/build/streaming-tt-recovery/routing-rc-coordinate06-named-subset-aggregate-01/summary.json`.

### artifact-4b7f348a2aa0

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-14/build/streaming-tt-recovery/routing-rc-coordinate06-named-subset-Root-authentication-01/report.json`.

### artifact-2cd18714c569

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-14/build/streaming-tt-recovery/routing-rc-coordinate06-spatial-context-provisional-01/grid.csv`.

### artifact-ae6549fd90d8

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-14/build/streaming-tt-recovery/routing-rc-coordinate06-spatial-context-Root-authentication-01/report.json`.

### artifact-01cfda951e90

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-15/build/streaming-tt-recovery/routing-rc-coordinate06-fixed-geometry-Root-outcome-authentication-01/report.json`.

### artifact-4ee89f7fa1df

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-15/build/streaming-tt-recovery/routing-rc-coordinate06-fixed-geometry-independent-outcome-review-01/report.json`.

### artifact-c6d70a1e2843

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-15/build/streaming-tt-recovery/routing-rc-final-report-evidence-review-01/report.json`.

### artifact-a1ef1dc413d4

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-15/build/streaming-tt-recovery/routing-rc-final-report-closeout-review-03/report.json`.

### artifact-016e56c54ab7

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-15/build/streaming-tt-recovery/routing-rc-campaign-final-cleanup-01/report.json`.

### artifact-951f29d9bc6f

Original relative path: `docs/research/streaming-tt-routing-rc-tooling-20261019/closed-snapshot-15/source-manifest.json`.
