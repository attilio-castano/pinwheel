# Draft: 512×64 SRAM width convention and qualification route

**Prepared locally; not submitted.** Intended as a focused follow-up to
[IHP issue 239](https://github.com/IHP-GmbH/IHP-Open-PDK/issues/239), with the
fixture attached when publication is separately authorized. Repository-relative
links below are local review material, not a claim that these files are already
available upstream.

We are integrating `RM_IHPSG13_1P_512x64_c2_bm_bist` through the CMOS5L SRAM alias
at IHP-Open-PDK `2bbec755dc67ca3db0261c3d6163e15735d66710`. All seven used views
and the shared behavioral model match that release's Git blobs. We would like
to establish the intended verification contract without editing supplied views
or disabling dimensional checks.

In the complete 32-bit `BITKIT_16x2_SRAM` tile:

| Definition | Terminals | GDS marker layer | CDL W × L | Measured W × L |
| --- | --- | --- | --- | --- |
| R0 | BLT_BOT–BLT_TOP | 10/29, metal2 | 0.260 × 0.600 µm | 0.200 × 0.600 µm |
| R1 | BLC_BOT–BLC_TOP | 10/29, metal2 | 0.260 × 0.600 µm | 0.200 × 0.600 µm |
| R2 | RWL–LWL | 30/29, metal3 | 0.260 × 0.600 µm | 0.200 × 0.600 µm |

The three definitions repeat across 32 bit cells. All markers are rectangular
and fully inside their conductors. Independent extraction agrees with direct
geometry measurement. The original December 2023 GDS/CDL already has this
discrepancy; it is not introduced by our tile export.

Our strict adapter rejects it. A separate diagnostic changing only the three
width tokens, with explicit model/hierarchy preparation, matches 288 devices,
182 nets and 42 ports in deep and flat modes. Restoring source widths fails.
Forty-two injected defect comparisons reject. Resistance value is outside this
dimensional comparison; width and length remain checked and individual
resistors are retained. This diagnostic does **not** qualify the supplied macro.

Questions:

1. Does SRAM `lvsres w=0.260 µm` intentionally correspond to a 0.200 µm marker?
   If so, where is that model/geometry convention specified, and which supported
   extraction/comparison settings implement it?
2. If the supplied views are inconsistent, which version or correction is
   authoritative? We can replay the retained fixture against it.
3. For this exact 512×64 macro and CMOS5L use, is there a version-bound commercial
   qualification report or a supported blackbox acceptance procedure, including
   its internal verification and operating-corner scope?

The [historical commercial LVS report](https://github.com/IHP-GmbH/IHP-Open-PDK/issues/239#issuecomment-2451952732)
is encouraging; we are asking how it maps to these precise inputs. Our boundary
LVS and fault controls pass, but they provide no internal-width coverage.

Reproduction material:

- [Complete tile, original source, physical witnesses and commands](../../physical/fixtures/sram-tile/README.md).
- [Tile results and counterfactual limits](sram-tile-results.md).
- [Provenance and native abstraction measurements](sram-trust-results.md).
- [Captured source URLs and SHA-256 digests](../../physical/fixtures/sram-trust/sources.json).

Pinned tools: LibreLane 3.1.0.dev3, Magic 8.3.674 and Netgen 1.5.320;
the tile's KLayout/deck/container identities are pinned in its manifest.

Supplied GDS SHA-256:
`5ea60dd194594f6587906683e5ca44759d6e847297b99085a4cb889e046cce03`

Supplied CDL SHA-256:
`825b831a246e1158fd4409501533874c21bc39f0f82369b2128947ffa2632999`
