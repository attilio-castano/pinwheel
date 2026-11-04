# Pinwheel 8×4 Tiny Tapeout rehearsal

**GO for local rehearsal. NO-GO for fabrication.** The November 4, 2026
rehearsal used the frozen post-fill successor of the e982 antenna repair.
The package is bound to source revision
`241dc0ec50a465d19d081cdc4e460a0e8d594c48`.

| Frozen artifact | SHA-256 |
| --- | --- |
| Post-fill ODB | `b7e60eded5198fc53df7e5dd1e3ab0f5162720516ab0c1692a1cf7c7bb62602b` |
| GDS | `041ff30708e46be33db330e2f1dcafab889824b689499e931ec9d180a11c1689` |
| Canonical TT-format LEF | `5700fca9cd42d1e232bfb6c5f91a0491491ec53cd904c6c8fce6e84561f4bbbd` |
| Logical Verilog | `6d3994230c8b56f99db0fce61ca1ebfddbd13de96d792b03605ee8107a05593c` |
| Powered Verilog | `e96a9ba1da1ce4560180e118342b793b713c5413406ddee930b4b6f5e110c5e1` |

## Local evidence

| Check | Observed result |
| --- | --- |
| Whole routing and fill | The route replay retained the fixed `net840` wire. Foundry DRC had zero markers across 332 categories, including `NW.b`. The 11 supplemental enclosure rules and 23 foundry antenna categories had zero markers. OpenROAD reported zero antenna violations across the block and on `net840`. |
| Frozen views and boundary | The fresh streamout matched the packaged GDS after normalizing only library and structure timestamps. The ODB exports bind the LEF, two Verilog views, DEF and complete reference CDL. The exact 8×4 template matched the die, rectangular `prBoundary` and all 43 signal-pin rectangles and labels. |
| LVS and power connectivity | Strict-port transistor-level LVS matched all 37 circuit pairs. The geometric rail check reached all 98,900 instance terminals and one top-level terminal on each of VPWR and VGND. The rail check covers geometric opens. IR drop and electromigration remain outside that check. |
| Tiny Tapeout precheck | The unmodified support-tools precheck at `d66cf179e7bc4d296362ab7e2e3b344dc3c4f665` passed all nine CMOS5L checks, including three KLayout runs. The verifier reopened all three raw KLayout reports. |
| Boolean correspondence | The accepted f516 Boolean proof carries over through equality of all 36,005 active gates, 6,039 state bits, clock and reset cones, and 24 outputs. A clean Git archive independently rederived the graph and state map. The proof authority is the retained Lean result and its checked transport. |
| Gate-level wire and bring-up | All 35 zero-delay UART, SPI, I²C, and JTAG cases passed across 513,297 sampled edges. The deliberately modified sampler was detected. The separate [bench fixture](../../scripts/streaming_8x4_bringup.py) passed warm reset, UART receive, SPI duplex, and 64-byte I²C read and write, including clock stretching, on the same compiled model. The fixture is ready for a board adapter. |

The portable test selections covered 754 8×4 cases, 371 Tiny Tapeout cases,
and 126 sampled-ready cases, with 26 opt-in cases skipped. The rehearsed
custom-GDS handoff contains GDS, LEF, logical and powered Verilog, metadata,
the bring-up datasheet and the license. The source revision binds the
[portable workflow](../../.github/workflows/tt-rehearsal.yml) and the
[metadata](../../info.yaml). The workflow names the prospective TTIHP27a
custom-GDS action revision and keeps external actions separate. The local
precheck used the older exact support revision recorded above. A
source-based build would also need the certified generated sources under
`src/`. The qualified clock field remains open, with `clock_hz: 0` in the
rehearsal metadata.

## Fabrication gates

1. **Qualified CMOS5L extraction and timing.** The fresh 20 ns diagnostic
   used the pinned PDK's legacy seven-layer nominal rules and reused that
   SPEF at the three Liberty corners. The critical hold path was from
   `ui_in[5]` to `engine.frontend._0230_/D`.

   | Liberty corner | Worst setup | Worst hold | Fanout violations |
   | --- | ---: | ---: | ---: |
   | Fast | +10.266 ns | −24.696 ps | 5 |
   | Typical | +8.143 ns | −7.519 ps | 5 |
   | Slow | +2.463 ns | +51.773 ps | 5 |

   The next admissible timing run needs a qualified five-layer extraction
   model, justified RC/Liberty corner pairings, full relevant annotation
   and propagated-clock setup, hold and electrical checks under the
   integration I/O constraints. The [model scope](streaming-tt-extraction-scope.md)
   records the known limitations of the pinned stack.
2. **Shuttle admission.** TTIHP27a is the proposed target. Confirm a
   contiguous 32-tile allocation and the run-specific custom-GDS acceptance
   path, checker revisions and integration limits. The precheck evidence
   here is local.

## Reopen the package

The ignored directory `build/tt-rehearsal-20261104/bundle/package/` contains
the handoff files. The manifest seals those copies and points to raw
evidence retained in this worktree's ignored build directories. Keep that
evidence with the worktree for verification.

```sh
workspace=$(pwd -P)
archive=$(mktemp -d)
git archive 241dc0ec50a465d19d081cdc4e460a0e8d594c48 | tar -x -C "$archive"
python3 -B "$archive/scripts/streaming_8x4_tt_rehearsal.py" --workspace "$workspace" \
  verify "$workspace/build/tt-rehearsal-20261104/bundle" \
  --manifest-sha256 023b5224678513fdb2792718fabf2e794218d8935d90a4b967b1435193e55bbe
```

| Readback under `build/tt-rehearsal-20261104/` | SHA-256 |
| --- | --- |
| `bundle-independent-readback.json` | `e3420ffb404a00654172063ed7d5149f7cb260a296cca3aa70ec1d9a90e2b37e` |
| `native-receipt.json` | `9fbe194c1358ad3d3ecd698ef00725d634398a101c9ecec14fe96b0b3b948e86` |
| `timing-diagnostic/diagnostic-readback.json` | `e865c863bcc6ab4038e415d1c35eedd45d77835cf23e75bf1eb5254bef02c764` |
| `release-decision.json` | `9249841c5cb9655d8147c2ff8582c0621516c3c5481046e1e1b32d2e4d22d761` |
| `cleanup.json` | `c6f3cf729f88d50cc706b648863ae0eb65245223774bd73a327b6689d874129d` |

The scoped postflight at 17:23 UTC found the rehearsal processes and
containers absent and the native lease available. The run and commits
stayed local.
