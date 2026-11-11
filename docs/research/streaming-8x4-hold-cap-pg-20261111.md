# Frozen 8×4 power-grid connectivity, November 11, 2026

The November 7 hold/capacitance candidate passed fresh OpenROAD PSM geometric
connectivity on both supply nets. The run required boundary terminals and
checked the routed grid and attached instance terminals against an independently
reopened census from the read-only ODB.

| Rail | Instance terminals | Boundary terminals | Shapes | Nodes | Connections |
| --- | ---: | ---: | ---: | ---: | ---: |
| `VGND` | 98,904 | 1 | 379,894 | 389,792 | 709,551 |
| `VPWR` | 98,904 | 1 | 321,328 | 330,870 | 589,037 |

OpenROAD reported all shapes connected on each net and both error reports
were empty. The pinned offline native job exited zero in 38.881 seconds
with matching-container cleanup verified. Its census includes 98,904
instances and 197,808 supply terminals.

The check establishes geometric connectivity on each rail. The receipt
records `shorts_checked=false` and `ir_drop_qualified=false`. Electrical
qualification still needs current and supply assumptions, rail voltage-drop
analysis, and electromigration limits.

## Local evidence

The ODB SHA-256 is
`dc654986c54512095c243407ea481ad3675a0269870ee4715dcbd1bd632c6a73`.
The associated GDS SHA-256 is
`d4cd48f0919ac47ec4b2ceb061bc5dc6a217ce730b02b819a6b7e09d9e73c832`.
These identify the frozen [rehearsal candidate](streaming-8x4-hold-cap-rehearsal-20261107.md).
New evidence is under the ignored `build/8x4-hold-cap-20261107/trial-02/pg/`
directory. The verified archive and manifest retain their November 7 digests.

| Artifact | SHA-256 |
| --- | --- |
| `rehearsal-pg-readback.json` | `5de097e8e7a425333c643f5baae7534e6fac8ff225f5993f82916655265f75a5` |
| `execution.json` | `4876c212b32f822f5d29e9a4f55066b50b40ce968e54a20765a0ddd501976bed` |
| `openroad.log` | `0c52d874318f90b92da7fcb70f6f9a6d6a4f68e7dee530e1cbcc36b1d6fe5bb3` |
| `inputs/request.json` | `a8f322715e96ef2c440a9075c5b8be3285aad7996e3f83ae36b518f92765de0c` |
| `inputs/inventory.json` | `d1a6e5fb7f084cc186a4d213e377bcb48869a036f503bfd136859de9baa50fa2` |
| `inputs/reference.json` | `da19eccfaa31dca8836f40bd693b4f125759470959cb06a0ed9ee3df34a2d1a4` |
| `launch.py` | `26771e548e15a2ffb73c3637b53435f6f11c0d73bd9c19e1a8d038a73238005d` |

From the worktree root, the runner takes the retained history checkout with
the pinned native tool inputs. It creates a fresh `pg/` output and refuses
to overwrite an existing one.

```sh
python3 -B scripts/streaming_8x4_hold_cap_pg.py --history "$PINWHEEL_HISTORY"
```
