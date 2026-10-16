# Whole-build worktree retention

`retain_build.py` preserves ignored build evidence before a managed worktree is
archived. It is separate from the frozen `pack.py` receipt collector. The
overnight CAS retains its selected dependency closure; it does not contain every
earlier physical experiment. Git commits preserve source and selected reports,
while this local archive preserves the complete ignored build directory.

Collection requires an idle source tree, macOS `/bin/cp -cRpP`, a fresh archive
root whose parent already exists, and space for any copy-on-write divergence.
The collector hashes every source file, clone-copies the tree, hashes every
destination file, then rehashes the source. It requires exact contents, file and
directory modes, relative symlink targets, and source identity/timestamp
stability. Every destination regular-file inode must differ from every source
regular-file inode. An APFS clone may share storage blocks safely while retaining
separate file identities. The collector rejects absolute, broken, or escaping
symlinks and unsupported special files. Existing archive roots are never reused.

```sh
python3 -B tools/pinwheel-evidence-pack/retain_build.py collect \
  --source /absolute/original/worktree/build \
  --archive-root /absolute/durable/parent/NEW_ARCHIVE
```

The archive contains `build/`, the complete `source-before.json` identity ledger,
`manifest.json`, `copy.log`, and `retention-report.json`. On failure it retains
partial outputs plus `retention-failed.json` without claiming success. Nothing
is deleted, moved, rewritten, committed, restored, submitted, or uploaded. Record
the successful manifest SHA256 outside the archive, then verify read-only:

```sh
python3 -B tools/pinwheel-evidence-pack/retain_build.py verify \
  --archive-root /absolute/durable/parent/ARCHIVE \
  --manifest-sha256 EXTERNALLY_RECORDED_MANIFEST_SHA256
```

Offline verification checks the retained bytes against that pin and needs no
original worktree. It does not claim that old live paths still exist or remain
unchanged. Historical absolute receipt paths stay untouched; a separate archive
mapping identifies where their retained relative paths now live. The existing
CAS additionally retains external historical input bytes declared by its index.
CAD containers, the host Python/runtime installation, and already-missing old
tool binaries remain external. This is a local preservation copy, not an offsite
backup or a self-contained executable environment, and establishes no new chip
qualification result.

Tests use tiny temporary directories and no CAD/network:

```sh
python3 -B -m unittest discover -s tools/pinwheel-evidence-pack \
  -p 'test_retain_build.py' -v
```
