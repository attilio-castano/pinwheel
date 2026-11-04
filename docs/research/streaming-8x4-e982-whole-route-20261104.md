# Whole routing from the e982 antenna repair

The bounded whole-route run completed on November 4, 2026. It started at
`OpenROAD.DetailedRouting` from the original pre-fill `e982…` ODB and used
the pinned `Streaming8x4ExistingDiodeFixed48` flow through
`OpenROAD.FillInsertion`. The detailed router finished with zero markers.
Its DEF is byte-identical to the input DEF, including the fixed `net840`
repair. The post-fill DEF equals the fill-only control byte for byte. The
GDS matches that control after normalizing only library and cell timestamps.

| Check on the new output | Result |
| --- | --- |
| IHP SG13CMOS5L main DRC | 332 categories, zero markers, including `NW.b` |
| Supplemental IHP enclosure checks | 11 exact rule bodies from the pinned maximal deck, zero markers |
| IHP foundry antenna | 23 categories, zero markers |
| OpenROAD antenna | Zero failing nets and pins across the block and in the explicit `net840` check |

The fill-only control reduced `NW.b` from 2,697 to zero and preserved every
original component and routing record. The
[admission checker](../../scripts/streaming_8x4_enclosure_admission.py)
admits the exact seven ordered `DRT-0349` diagnostics in the full-block
checker only when it can reopen the matching fill and physical evidence.
The detailed routing log contains that same warning sequence. LibreLane
separately skipped its optional wire-length threshold checker because the
configuration has no threshold.

The completed routing, fill, and physical checks apply to the hashes below.
Qualified extraction and timing, final-target logical and full release
checks, and shuttle acceptance remain separate work.

| Artifact | SHA-256 |
| --- | --- |
| Original pre-fill ODB | `e982e1a2949db8d6f34ef2666002b31be2a770093a0631e98b3442a27387c8f4` |
| New detailed-route ODB | `527aebefb817a64694a84ae1cb97ddb4df52bb64fc80e5c4837f3995e1be5853` |
| New post-fill ODB | `b7e60eded5198fc53df7e5dd1e3ab0f5162720516ab0c1692a1cf7c7bb62602b` |
| New post-fill GDS | `041ff30708e46be33db330e2f1dcafab889824b689499e931ec9d180a11c1689` |
| Independent result readback | `4b23185cbef099e8eef84bfeac39c4ab63461aa5a77b52a3dc4fe516b0513f3b` |
| Execution receipt | `143ba01396beabbd43209d11c880f50a7583370f95331a03dff7215b8351ffc3` |
| Main DRC report | `1076394b7f848b72be1b7b4100b0bd927dd39a32a8eec31201434dd34bbf85fe` |
| Supplemental enclosure report | `0dec2c309cd90376c7d6b8221ce635438bedf14ad924d7e5a9799f97f85a4792` |
| Foundry antenna report | `e79884207d98700b8e4af3acdb07cf0f5270593e11b6a54db7cbe97d132fec66` |

The raw outputs and replay scripts live in this worktree's ignored
`build/e982-whole-route-20261104/` directory. This record inventories those
artifacts and does not serve as a portable evidence pack.

To exercise the warning matching controls from source, run:

```sh
python3 -B -m unittest discover -s test -p test_streaming_8x4_enclosure_admission.py
```

To reopen the actual admission, use the retained local evidence:

```sh
python3 -B scripts/streaming_8x4_enclosure_admission.py \
  --check build/e982-check-20261104 --fill build/e982-fill-20261104
```
