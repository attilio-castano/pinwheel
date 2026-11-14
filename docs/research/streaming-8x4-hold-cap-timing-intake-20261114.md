# Frozen 8×4 provider timing intake and draft I/O margin

Both the pre-STA SPEF intake and the post-STA annotation check now accept the
exact hold/capacitance target, ODB `dc654986…` and GDS `d4cd48f0…`.
They passed on all nine retained draft cases. Each SPEF graph covers 41,787
consumed nets. OpenSTA reported 282 unused drivers and zero partially
annotated drivers per case. The three RC graph digests were distinct.
Provider authority, physical extraction accuracy and qualified timing
remain open. [Timing coverage](streaming-8x4-hold-cap-timing-coverage-20261111.md)

## Draft host timing margin

The port table in `io-margins.json` reopens all nine cases for the ten
consumed nonclock inputs and twelve active outputs. It uses the pinned
20 ns SDC with 0.200 ns uncertainty, 0.200 ns minimum and 4.000 ns maximum
I/O delay, `sg13cmos5l_buf_2/X` input drive and 10 fF output load. The
break-even value varies one delay while holding the clock, driver, load,
all other delays and extracted parasitics fixed.

| Boundary | Worst draft slack | Break-even external delay |
| --- | ---: | ---: |
| `ui_in[3]` input hold | +38.855 ps | Minimum 161.145 ps |
| `ui_in[5]` input hold | +45.780 ps | Minimum 154.220 ps |
| `rst_n` input setup | +2.253401 ns | Maximum 6.253401 ns |
| `uo_out[0]` output setup | +7.591245 ns | Maximum 11.591245 ns |

Of the consumed inputs, `ui_in[3]` has the least draft hold margin. Both
it and the repaired falling `ui_in[5]` path need a host arrival and slew
contract. The repaired path has at least 15.325809 ns setup slack within
the draft matrix. The tightest global hold check remains an internal
register path at +31.572 ps. A longer cycle leaves the same-edge hold
calculation unchanged. Joint changes can accumulate along an input-to-output
path and need a new STA run. [Original draft model and constraints](streaming-8x4-hold-cap-trial-20261107.md)

## Intake and local replay

Use `--target hold-cap-trial` with a hash-reviewed request for the frozen
ODB, GDS, implemented logical Verilog and ODB signal inventory. The
pre-STA schema `pinwheel.e982-parasitics-intake-request.v1` consumes each
scenario's RC corner, STA corner, mode, SDC, SPEF and exact Liberty list.
The `authority` object binds the extraction receipt, corner matrix and
host timing contract by file path and SHA-256. A reviewer still needs to
admit those authorities and confirm scenario coverage. The reader parses
a scalar detailed-net SPEF dialect and checks names, connectivity, units,
coverage and corner graph identity. It never executes provider inputs.

Once the approved scenario matrix has run, use the post-STA schema
`pinwheel.e982-parasitics-preflight-request.v1` to add the scenario's native
annotation report and analysis receipt. Complete setup, hold and electrical
checks then need independent readback on the approved matrix. Obtain an
accepted CMOS5L deck or exact-target corner SPEFs and the applicable host
clock and I/O contract before claiming timing qualification.
[Provider and analysis requirements](streaming-8x4-e982-timing-intake-20261104.md)

The adapter writes a fresh ignored directory. Both sample requests
use the old draft model and provisional assumptions.

```sh
OUT=build/8x4-hold-cap-20261107/trial-02/timing-intake-04
python3 -B scripts/streaming_8x4_hold_cap_timing_intake.py --out "$OUT"
request="$OUT/draft-intake-request.json"
digest=$(shasum -a 256 "$request" | cut -d ' ' -f 1)
python3 -B scripts/streaming_8x4_e982_parasitics_preflight.py "$request" \
  --target hold-cap-trial --request-sha256 "$digest"
```

The successful local evidence is in the sibling `timing-intake-03/`.
The original timing runs and rehearsal archive remain in place.

| Receipt | SHA-256 |
| --- | --- |
| `draft-intake-preflight.json` | `96edf3f7f4b926be4333ac3262dca17261c39ec4c7aaa054e4505770745728d4` |
| `draft-preflight.json` | `86a33967855040394aebfc43007e9e026ccc7e15bc73238859faa43f1986b3b2` |
| `io-margins.json` | `ad7239d543724185873ffb8a1f6e28383b6dd80d8843ec2b45a37d5baca3106f` |
