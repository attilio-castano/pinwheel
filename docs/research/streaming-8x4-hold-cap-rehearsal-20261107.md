# Fresh 8×4 Tiny Tapeout rehearsal bundle, November 7, 2026

**Local rehearsal GO. Fabrication NO-GO.** The new hold/capacitance candidate
has a freshly assembled, compressed and independently verified local handoff.
Qualified CMOS5L extraction and timing with the accepted host I/O budget,
electrical power qualification, and shuttle allocation/custom-GDS acceptance
remain the three open qualification gates.

The bundle targets ODB
`dc654986c54512095c243407ea481ad3675a0269870ee4715dcbd1bd632c6a73`
and GDS
`d4cd48f0919ac47ec4b2ceb061bc5dc6a217ce730b02b819a6b7e09d9e73c832`.
Its committed source checkpoint is
`a305a4b339767e80719c9720a12ced7345b0e814` on
`codex/8x4-timing-closure`, in the existing worktree.

## Local handoff

The directory is `build/8x4-hold-cap-20261107/trial-02/rehearsal-01/`.
It contains the `bundle/` tree, the compressed
`pinwheel-8x4-hold-cap-rehearsal.tar.gz`, and the assembly, archive and
independent-verification receipts. Large payloads remain in ignored local
storage. This report records their exact digests.

| Item | Verified content |
| --- | --- |
| Payload | 17 files, including GDS, LEF, logical and powered Verilog, ODB, CDL, provisional SDC, metadata, datasheet, license, demo source, fixture and dry-run output |
| Selected evidence | 330 files with raw reports, traces and process receipts |
| Source snapshot | 2,050 committed files, packaged under `source/` |
| Complete bundle | 2,398 regular files, 1,160,382,718 uncompressed bytes |
| Compressed archive | 156,064,791 bytes |
| Manifest SHA-256 | `0533dfb6c6ddf203a43f8b2a5cd67a399e6deb1a3afa2911a1d0b00646b4158f` |
| Archive SHA-256 | `07e8716279ca1458bcb12c3ed1f2f4c230d2961f799987fd02679cbab5b96632` |

The selected SDC equals the exact `bcfd5a3e…` assumptions consumed by the
nine-case draft timing sweep. Current source files and selected raw evidence
have separate manifest inventories. Other original producer bindings are
retained as provenance labels, with custody scopes recorded in the manifest.

## Checks and fresh bring-up

The verifier reopens the selected native outputs and their target/view joins.
It checks complete rule inventories, raw trace indices and bytes, process
journals, every state pin, precheck XML and draft timing reports.

| Evidence | Result |
| --- | --- |
| Physical | 332 main-deck categories, 11 enclosure rules and 23 foundry antenna categories, all zero markers; 39 strict transistor LVS pairs matched |
| Public geometry | 1,724.16 × 710.64 µm outline and 43 public signal pins |
| Supply bindings | VDD/VSS assignments checked for all 98,904 instances |
| Digital | 6,039 state bits, 24 output bits, all 35 public-pin cases and sampler mutation detection |
| Raw wire replay | All 14 native processes and 513,297 sampled edges |
| Tiny Tapeout precheck | All 9 selected checks passed, including its complete 332-category main DRC |
| Draft timing | All 9 scenarios pass setup, hold, slew, signal capacitance and fanout under the retained provisional models |
| Fresh bring-up | UART receive, SPI duplex, I²C read and I²C write all passed on the exact current compiled model |

The new [bring-up runner](../../scripts/streaming_8x4_hold_cap_bringup.py)
completed the four fixtures in 36.736 seconds. UART received `96`. SPI
transmitted `135ca5ee3780c912` and received `a53cd36a00992ec7`. I²C used
address `0x52`, 64-byte read/write payloads and 585 stream cells per transfer.
The read observed 51 target-stretch edges and the clean write observed zero.
All four cases completed matching-release cleanup. This is local public-pin
simulation; the receipt records `board_exercised=false`.

[Physical evidence](streaming-8x4-hold-cap-physical-20261107.md),
[digital/precheck evidence](streaming-8x4-hold-cap-digital-precheck-20261107.md)
and [draft timing evidence](streaming-8x4-hold-cap-trial-20261107.md) retain
their measurement scopes and exact target identities.

## Extracted-archive verification

The [clean verification launcher](../../scripts/streaming_8x4_hold_cap_rehearsal_clean.py)
created a clean Git archive of the committed source, then extracted the
actual compressed handoff into a physically separate temporary directory.
Its verifier ran with `-I -B`, without a `.git` or `build` directory in the
source checkout. A cooperative Python audit guard blocked file reads from
the live worktree, history checkout and main repository, plus subprocess,
network and ctypes bypasses. All six guard self-tests were blocked and the
positive verifier attempted zero denied reads. It returned `verified=true`
with the exact candidate, source commit and manifest identities.

Two controls then exercised disposable extracted copies. Replacing the GDS
with the earlier fanout ECO and updating the payload size/hash plus the
external manifest digest was rejected by the independently reopened evidence.
After restoring the exact payload, modifying the archived verifier source
was rejected by the source-snapshot comparison. Both controls exited 2 for
the intended reason. The complete guarded check took 21.525 seconds.

An independent audit hashed every live bundle file and streamed every
archived regular file against the same manifest bindings. It also checked
the archive hash and verification receipts. The verifier packaged under
`bundle/source/` separately passed on the finished bundle.

The handoff carries selected evidence and source for portable readback.
Native CAD/simulation re-execution uses separately retained toolchains and
full PDK inputs. Complete historical proof-archive custody, independent
backup custody and a fresh source-to-GDS rebuild have separate scope flags.
The manifest preserves `tapeout_ready=false` and fabrication `no-go`.

## Reopening the local bundle

The [assembler/verifier](../../scripts/streaming_8x4_hold_cap_rehearsal.py)
can verify from its packaged source snapshot. From the repository root,
run the following on the retained bundle.

```sh
python3 -B build/8x4-hold-cap-20261107/trial-02/rehearsal-01/bundle/source/scripts/streaming_8x4_hold_cap_rehearsal.py verify \
  build/8x4-hold-cap-20261107/trial-02/rehearsal-01/bundle \
  --manifest-sha256 0533dfb6c6ddf203a43f8b2a5cd67a399e6deb1a3afa2911a1d0b00646b4158f
```

After extracting the archive elsewhere, the same command uses the extracted
`bundle/source/scripts/` verifier and the extracted `bundle` path. It opens
its mirrored evidence through recorded path labels.

## Artifact manifest

Paths below are relative to `build/8x4-hold-cap-20261107/trial-02/`.

| Artifact | SHA-256 |
| --- | --- |
| `rehearsal-01/bundle/manifest.json` | `0533dfb6c6ddf203a43f8b2a5cd67a399e6deb1a3afa2911a1d0b00646b4158f` |
| `rehearsal-01/pinwheel-8x4-hold-cap-rehearsal.tar.gz` | `07e8716279ca1458bcb12c3ed1f2f4c230d2961f799987fd02679cbab5b96632` |
| `rehearsal-01/assembly.json` | `9fffa223ec2c44197e5cf1629a6fdb1dbc125c8230599a6a095b8d6a5be54458` |
| `rehearsal-01/archive.json` | `5c36d8ba34663905f231826825381f1f01378260f94d0b8b7f61c86d308ed5dc` |
| `rehearsal-01/independent-readback.json` | `ba710bda5e46dd3d557777da52a37d4d51155f60a54bbb68802a5d6f96a8e411` |
| `rehearsal-01/bundled-source-verification.json` | `9fffa223ec2c44197e5cf1629a6fdb1dbc125c8230599a6a095b8d6a5be54458` |
| `rehearsal-bringup-01/receipt.json` | `72fc3a6d9e1e1ca9ebd485621ad52da26ef8a848c27bab70519d9c0876166739` |
