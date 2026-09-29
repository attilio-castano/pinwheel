# Recover and replay current Design A

The current-A command uses the v2 acceptance selection explicitly. It inventories
all dependencies before recovery, preserves the historical source/checker bytes,
and replays their assessment from a movable local bundle. The current Lean design,
emitter entry points, host format and build pins must still match that snapshot.
Current checker changes do not invalidate the preserved historical source.

**A remains unaccepted.** SRAM qualification, compatible fast timing conditions
and package power are required. This workflow invokes the preserved Lean
library's build and freshly kernel-checks eight captured program certificates. It reuses physical,
host simulation and RTL interpretation receipts by exact identity. It does not
rerun CAD, qualify the component, prove physical repeatability, implement B or
complete clean-source physical replay.

## Inventory and recover on this host

The tracked `design-acceptance-readback-results.json` pins the saved assessment,
whose complete `verified_files` inventory supplies the dependency list. The
already hash-bound host receipt adds its complete source freeze, including
emitter/peer entry points the older assessment did not reread. The
inventory command reads every dependency and lists all missing or changed files;
it creates no output directory. Explicit prefix relocations select recovered
locations, and each recovered file must match its original SHA-256.

```sh
python3 -B scripts/check-current-a.py inventory \
  --source-root /Users/attiliocastano/.codex/worktrees/c6eb/pinwheel \
  --relocate /Users/attiliocastano/.codex/worktrees/c6eb/pinwheel/build/tools=/Users/attiliocastano/.codex/worktrees/a2b1/pinwheel/build/tools \
  --relocate /Users/attiliocastano/.codex/worktrees/fc40/pinwheel/build/physical/pdk/ihp-sg13cmos5l=/Users/attiliocastano/.codex/worktrees/a2b1/pinwheel/build/recovery/pdk/ihp-sg13cmos5l

python3 -B scripts/check-current-a.py bundle \
  --source-root /Users/attiliocastano/.codex/worktrees/c6eb/pinwheel \
  --bundle build/retained-evidence/current-a-01 \
  --relocate /Users/attiliocastano/.codex/worktrees/c6eb/pinwheel/build/tools=/Users/attiliocastano/.codex/worktrees/a2b1/pinwheel/build/tools \
  --relocate /Users/attiliocastano/.codex/worktrees/fc40/pinwheel/build/physical/pdk/ihp-sg13cmos5l=/Users/attiliocastano/.codex/worktrees/a2b1/pinwheel/build/recovery/pdk/ihp-sg13cmos5l
```

Use a new bundle directory; an existing directory is refused. `inventory.json`
records original logical paths, exact hashes, byte counts, relative bundle
locations and recovery origins. The original assessment root is derived from
all eight certificate-command paths in the hash-bound saved index. References
to that root resolve to their same relative indexed files in the bundle;
unindexed paths still refuse. This alias can be derived for an existing bundle
without changing its inventory. Snapshot files are copied, made read-only and
checked again. Absolute library references move into the bundle without editing
old receipts. Copy the complete bundle directory to relocate it; do not replace
its files with links to the original worktrees. A failed copy retains its partial
directory for inspection and does not publish an inventory.

## Replay from the recovered bundle

```sh
python3 -B scripts/check-current-a.py replay \
  --bundle build/retained-evidence/current-a-01 \
  --tag current-a-replay-01 \
  --lean-bin /Users/attiliocastano/.elan/toolchains/leanprover--lean4---v4.33.1/bin
```

Use a fresh tag. The wrapper rechecks the entire bundle and current design,
checks the Lean version, builds the snapshot library, then invokes the preserved
checker with the explicit current v2 selection and `--require-accepted`. The path
adapter changes only file lookup. Every original identity, receipt comparison,
structural check and refusal remains active. An unindexed retained dependency is
refused even when a file happens to exist locally. Newly produced proof logs and
certificate copies are allowed only in the fresh assessment directory.

The wrapper writes `build/validation/<tag>/report.json` and `report.md`, with a
copy of the detailed assessment, command logs, current-source comparison, runtime
identities and explicit reused-physical status. The historical checker writes its
fresh assessment under the bundle's `root/build/validation/current-a-<tag>/`.
The bundle's inventoried input bytes stay fixed; `.lake/` and fresh run outputs
are working caches and are not promoted to historical evidence.
Later replays may reuse the snapshot's `.lake/` cache; the command does not claim
that every library module is recompiled on every invocation.

| Exit | Meaning |
| --- | --- |
| `0` for inventory/bundle | Every inventoried input matches, or recovery completed. This says nothing about chip acceptance. |
| `2` for replay | The complete v2 assessment ran; eight certificates were freshly checked; A is refused for exactly SRAM qualification, timing conditions and package power. |
| `1` | Missing/changed/unindexed evidence, design mismatch, wrong runtime, incomplete checks or failed replay. This is not the expected blocked result. |

The seed intentionally describes one retained implementation. New SRAM,
characterization, power or design evidence needs a new reviewed intake rather
than edits to historical receipts. [Implementation acceptance](implementation-acceptance.md)
owns the current verdict; [research status](status.md) owns the next decision.

## Focused controls

```sh
python3 -B -m unittest discover -s test -p 'test_retained_evidence.py' -v
python3 -B -m unittest discover -s test -p 'test_current_a.py' -v
```

The controls cover complete preflight refusals, identical-byte relocation,
bundle movement after source removal, unchanged receipt bytes, independent
historical checker sources, current design/format drift, missing/modified/escaping
bundle files, stale-v1 refusal, index tampering, logical identity/consumption,
original-root absolute references, contradictory root metadata, unindexed
dependencies and no-overwrite behavior. Wrapper controls additionally
reject an assessed-looking worker that exits 1, incorrect blockers, incomplete
fresh certificate checks and source edits during the run. These stub command
execution and provide tool-regression evidence, not new hardware measurements.

## Recorded local replay

On September 29 the surviving `c6eb` evidence had dangling tool and PDK paths
after `fc40` retirement. Pinned official CIRCT/OSS archives and five standard-cell
files were recovered locally and matched their historical hashes. Preflight then
verified **749 files / 602,275,665 bytes**, including the saved assessment's 740
inputs, its index/root manifest and seven additional hash-bound host source pins.
The final bundle was created under `build/retained/` and moved to
`build/portable/current-a-20260929-02/` before replay. Its inventory SHA-256 is
`0f9b8ac036f26872f47fbd440120f1617800125790dd2a5ea59f7a7da3ff2ac4`.

The first replay, `current-a-portable-01`, compiled the snapshot library but
refused an absolute own-root reference embedded in the old mapping receipt.
The correction derives that one root from the saved assessment's eight
certificate commands and resolves only indexed files. No original receipt or
inventory byte changed; the failed run remains available.

The corrected `current-a-portable-02` replay passes its expected blocked gate:
the snapshot build invocation passes using its existing `.lake` cache, all
**247 current design/format pins** match, all **eight certificates** receive fresh
kernel checks, and all bundle inputs remain unchanged. The preserved checker
verifies **740 inputs** in **103.385 seconds**, returning exactly the three
physical blockers. The wrapper requires exit 2 and rejects every other failure.
Its receipt is `build/validation/current-a-portable-02/report.json`, SHA-256
`b9896d8699dccd92c11fb5c6448395531e422e815486922c3a5b2ead24f83bad`;
the detailed assessment SHA-256 is
`73fbc19ae5c3d02c146aa259fa1e9f67ba553be44b90f6f8ff7f528d6b3ab90b`.
Fourteen inventory/alias controls and five wrapper controls pass normally and
under optimized Python. The [local continuation](local-iteration-continuation.md)
binds this replay alongside source interpretation and the power request.
