# Draft follow-up: 512×64 SRAM width/layer convention and qualification path

**Prepared for review on 2026-09-29; not submitted.** Intended as a follow-up to
[IHP issue 239](https://github.com/IHP-GmbH/IHP-Open-PDK/issues/239).
The [local tracker](qualification-followups.md) owns disposition. The
[original draft](sram-maintainer-report.md) remains unchanged because the
provenance study binds its exact bytes. The text below is the proposed report.

## Proposed report

We are integrating `RM_IHPSG13_1P_512x64_c2_bm_bist` through the CMOS5L SRAM alias
at IHP-Open-PDK `2bbec755dc67ca3db0261c3d6163e15735d66710`. All seven supplied
views and the behavioral-model dependency match that release. We would like
help identifying the supported layout/schematic interpretation and qualification
path for these exact inputs.

Our complete 32-bit `BITKIT_16x2_SRAM` fixture preserves the source geometry,
neighboring context, hierarchy and 42 physical ports. It has these dimensional
differences, repeated over 32 bit cells:

| Source definition | Terminals | Physical marker and conductor | CDL W × L | Measured/extracted W × L |
| --- | --- | --- | --- | --- |
| R0 | BLT_BOT–BLT_TOP | 10/29 within metal2 | 0.260 × 0.600 µm | 0.200 × 0.600 µm |
| R1 | BLC_BOT–BLC_TOP | 10/29 within metal2 | 0.260 × 0.600 µm | 0.200 × 0.600 µm |
| R2 | RWL–LWL | 30/29 within metal3 | 0.260 × 0.600 µm | 0.200 × 0.600 µm |

Direct GDS measurements agree with extraction. The original December 2023
GDS/CDL already has the difference, so it was not introduced by the fixture
export or a mixture of releases. The original widths fail our dimensional
comparison. A separate diagnostic changing three width tokens to 0.200 µm,
with explicit hierarchy/model preparation, matches 288 devices, 182 nets and
42 ports in both deep and flat modes. Restoring the original widths fails;
42 injected defect comparisons reject.

This diagnostic tests the source of the mismatch. It does not determine which
width is authoritative, check resistance values, qualify analog behavior, or
establish the complete macro's internal and cross-block correctness. Our
351-pin macro boundary comparison passes and rejects wiring faults, but is
deliberately blind to internal width changes.

At [proposal 1121](https://github.com/IHP-GmbH/IHP-Open-PDK/pull/1121) head
`22a1f12ed015b52ccb689e71f9f2a3dadd6a8cdb`, the three single-port bit-cell
resistors gain `layer=Metal1` while retaining `w=2.6e-07 l=6e-07`. Our retained
physical witnesses place R0/R1 on metal2 and R2 on metal3. We have not adopted
that proposal or changed the supplied views.

Could you clarify:

1. Does `lvsres w=0.260 µm` intentionally correspond to a 0.200 µm GDS marker?
   If so, which documented model/geometry rule and supported extraction or
   comparison settings implement the conversion?
2. How should the proposed `Metal1` annotations be interpreted against the
   metal2/metal3 witnesses? If these are view inconsistencies, which correction
   or replacement version should we replay?
3. Is a version-bound qualification report or supported macro-abstraction
   procedure available for this exact 512×64 macro in CMOS5L, including internal
   verification, behavioral coverage and operating conditions?

The [historical commercial LVS report](https://github.com/IHP-GmbH/IHP-Open-PDK/issues/239#issuecomment-2451952732)
and subsequent work on the 512×32 variant are useful context. We are asking how
the supported procedure applies to these precise 512×64 inputs.

Reproduction and evidence:

- [Complete tile recipe, unchanged source/GDS, dimensional witnesses and controls](https://github.com/attilio-castano/pinwheel/blob/codex/paired-design-iteration/physical/fixtures/sram-tile/README.md).
- [Measured tile results and diagnostic limitations](https://github.com/attilio-castano/pinwheel/blob/codex/paired-design-iteration/docs/physical/sram-tile-results.md).
- [Release provenance, abstraction controls and captured source identities](https://github.com/attilio-castano/pinwheel/blob/codex/paired-design-iteration/docs/physical/sram-trust-results.md).

The fixture includes the upstream license notice and pins its source/deck/tool
inputs. It requires the pinned PDK and CAD container; the whole Pinwheel campaign
is not needed to run the tile comparison. Detailed raw campaign receipts remain
local and are identified by hashes in the repository manifests.

The surrounding flow uses LibreLane 3.1.0.dev3, Magic 8.3.674 and Netgen 1.5.320;
the tile's KLayout, deck and container identities are recorded in its manifest.

Supplied GDS SHA-256:
`5ea60dd194594f6587906683e5ca44759d6e847297b99085a4cb889e046cce03`

Supplied CDL SHA-256:
`825b831a246e1158fd4409501533874c21bc39f0f82369b2128947ffa2632999`
