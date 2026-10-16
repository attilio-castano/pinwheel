# Historical physical experiment source archive

This directory preserves the source of local physical experiments captured on
2026-10-16 before closing the research worktree. It contains 936 byte-identical
source mirrors from 122 original directories: 5,551,759 source bytes and 75,016
lines. The manifest records each original repository-relative path, archived
path, SHA256 and size.

The selection includes immediate `.py`, `.tcl`, `.cc`, `.cpp`, `.h`, `.hh` and
`.sh` files in `build/physical/tt-*-tools-*` directories. It does not recursively
copy dependency or vendor subdirectories. Five source bootstrap files from
`build/physical/tt-p2-drt-onepass-route-01` are also preserved because later
campaign staging reads that original run's native program and coordinator.

These are historical snapshots, including unsuccessful attempts and superseded
helpers. Their presence does not designate a latest accepted version, establish
a passing chip, or authorize execution. They have not been refactored: embedded
absolute paths, old deadlines, original run names and source notices remain
unchanged. Executing an archived driver can perform writes or launch expensive
tools. Do not execute it as a reproduction shortcut.

This source archive is not a portable clean-clone physical flow. Complete replay
also requires the appropriate original receipts, checkpoints, generated design
inputs, guides, PDK and library files, native dependency headers, compiled
adapters and recorded runtime image. Those inputs and raw generated outputs
remain outside this Git archive. The separate overnight evidence pack closes
its declared receipt dependencies; it does not automatically preserve every
earlier experiment. Source identities here do not imply recovery of those
other inputs.

## Verify source retention

The verifier uses only the Python standard library. It reads and hashes files;
it never imports a snapshot or invokes CAD, Docker, a compiler, or the network.

```sh
python3 -B tools/pinwheel-physical-history/verify.py
```

While the original worktree and its ignored build files still exist, compare
all mirrors against those originals as well:

```sh
python3 -B tools/pinwheel-physical-history/verify.py --origins
```

An original checkout stored elsewhere can be selected using
`--origins --origin-root /path/to/original/checkout`. Without `--origins`, source
verification remains independent of the old build directory. Verification
requires the exact listed inventory and rejects missing, additional, changed
or symlinked archived files. It validates source retention only; native
execution and physical acceptance remain separate questions.

## Attribution

Original copyright and license headers are retained byte for byte. Pinwheel's
original source remains under the repository's Apache-2.0 license. Copied or
adapted OpenROAD material retains its BSD-3-Clause terms; the corresponding
[OpenROAD license](OPENROAD-LICENSE) is included. Some captured flow scripts
retain LibreLane Contributors and Efabless Apache-2.0 notices. Full vendor
source and dependency trees are not distributed in this directory. The
[physical tool replay guide](../README.md) describes source, ignored evidence
and runtime retention as separate obligations.
