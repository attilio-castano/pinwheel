# 8×4 hold/capacitance candidate physical checks, November 7, 2026

All four requested checks passed on the exact
[hold/capacitance candidate](streaming-8x4-hold-cap-trial-20261107.md).
Carry this candidate forward for the remaining digital, Tiny Tapeout and
qualification checks. Fabrication readiness requires qualified CMOS5L
extraction with the accepted host I/O budget, electrical power
qualification and shuttle admission.

| Check | Result |
| --- | --- |
| Main-deck IHP SG13CMOS5L DRC | All 332 categories, zero markers, including `NW.b` |
| Supplemental enclosure | All 11 categories, zero markers |
| Transistor LVS | All 39 circuit pairs matched in strict port mode, NET_ONLY=false, 256 definition-level devices per side |
| Foundry antenna | All 23 categories, zero violation items or multiplicity |

The main deck completed in 1,968.99 seconds according to its native log.
Each native container exited zero and its owned cleanup confirmed absence.
The physical jobs read the candidate without modifying its ODB or GDS,
so the prior nine-case draft timing result still refers to these same bytes.

The candidate ODB is
`dc654986c54512095c243407ea481ad3675a0269870ee4715dcbd1bd632c6a73`.
Its GDS is
`d4cd48f0919ac47ec4b2ceb061bc5dc6a217ce730b02b819a6b7e09d9e73c832`.
The LVS reference is the complete CDL exported from that ODB, SHA-256
`4bde936d6896a26a42ce7c443b3abcb134adc391045edacd5bae80ab42f15c5b`. It includes the newly used
`buf_2` and `dlygate4sd2_1` masters. Both matched, along with the top-level
circuit. The raw log confirms transistor mode, strict port comparison
and the netlist-match success message.

The enclosure subset covers `M1.c`, `M1.c1`, `M2.c`, `M2.c1`, `M3.c`,
`M3.c1`, `M4.c`, `M4.c1`, `V1.c1`, `V2.c1` and `V3.c1`. Its exact deck
was mounted read-only. Foundry antenna used the pinned CMOS5L antenna
deck, distinct from the earlier OpenROAD antenna result.

## Verification and reproduction

The [exact-target runner](../../scripts/streaming_8x4_hold_cap_physical.py)
checks candidate hashes, completed native execution and cleanup, pinned
deck identities, read-only input mounts, complete rule coverage, raw
result hashes and matching CDL provenance. Independent readback requires
all 39 circuit pairs to match, includes both new masters and the top,
and checks the actual antenna report has zero items and multiplicity.
The DRC and enclosure category inventories match the retained checker
references. A wrong candidate GDS digest was tested and rejected before
native execution. Python compilation and `git diff --check` passed.

With `PINWHEEL_HISTORY` pointing to the retained history checkout,
run the following phases on a fresh checked candidate evidence tree.
Each native phase uses a fresh output directory. The `decision` phase
independently reopens completed results on this exact candidate.

```sh
python3 -B scripts/streaming_8x4_hold_cap_physical.py enclosure --history "$PINWHEEL_HISTORY"
python3 -B scripts/streaming_8x4_hold_cap_physical.py lvs --history "$PINWHEEL_HISTORY"
python3 -B scripts/streaming_8x4_hold_cap_physical.py layout-readback --history "$PINWHEEL_HISTORY"
python3 -B scripts/streaming_8x4_hold_cap_physical.py drc --history "$PINWHEEL_HISTORY"
python3 -B scripts/streaming_8x4_hold_cap_physical.py decision --history "$PINWHEEL_HISTORY"
```

All work remains local on `codex/8x4-timing-closure` in the same worktree.
Raw results are in the ignored candidate directory
`build/8x4-hold-cap-20261107/trial-02/`, under `main-drc-01/`,
`enclosure-01/` and `layout/`. The aggregate decision is
`physical-decision.json`. The new candidate awaits fresh digital correspondence,
Tiny Tapeout precheck and its own release-package adoption review.

## Artifact manifest

| Local artifact | SHA-256 |
| --- | --- |
| `physical-decision.json` | `70137eccd434c27864923fa3a9b3114e6fb363008b185822ad9a14e64d05bd72` |
| `main-drc-01/readback.json` | `ddbc4dc566251e650936f8cf42df39be72f4dd8d3225fcb777a972e55986fc33` |
| `main-drc-01/drc_sg13cmos5l.xml` | `1076394b7f848b72be1b7b4100b0bd927dd39a32a8eec31201434dd34bbf85fe` |
| `main-drc-01/execution.json` | `a0a7873ed928e1679e54a0b8406f1163f5245a5f79952ef2d90ddca2288318d2` |
| `enclosure-01/readback.json` | `cfb0133bff13ada11c6be55d29edc9b29b867953bb8c40f5ed08086aea2a18f7` |
| `enclosure-01/enclosure.xml` | `0dec2c309cd90376c7d6b8221ce635438bedf14ad924d7e5a9799f97f85a4792` |
| `enclosure-01/execution.json` | `5ca9cb7627243cef5e8044d3700cc99af40dafd3aa08f0214204c87fadb64718` |
| `layout/independent-readback.json` | `f36b45640a4114722647a19799758e5a589a4df6979df1ffc77eba6fed5e956d` |
| `layout/rehearsal-lvs-readback.json` | `d002a6859062c58222d90a3e0185675dadd3b4f34b06de28f12a5c42c9959501` |
| `layout/lvs.lvsdb` | `b9377dbdb5616ab6b102ceded820e227c868bad04c3a97d638a4e5ede21bfe61` |
| `layout/antenna.xml` | `e79884207d98700b8e4af3acdb07cf0f5270593e11b6a54db7cbe97d132fec66` |
| `layout/native-result.json` | `dca12f102f4c02d688cf3e4e72c50f814204385596198525896feae51c24e36a` |
| `layout/execution.json` | `91b6ca6e37720d7396b698065947a625a8cdd46f165d5481f06f481796ca07d8` |
