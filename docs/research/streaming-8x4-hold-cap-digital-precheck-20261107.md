# 8×4 hold/capacitance digital correspondence and precheck, November 7, 2026

Fresh Boolean correspondence, public-pin replay and pinned Tiny Tapeout
precheck all passed on the exact candidate that passed
[all four physical checks](streaming-8x4-hold-cap-physical-20261107.md).
The candidate can proceed to local release-package adoption review.
Qualified extracted timing with the accepted host I/O budget, electrical
power qualification and shuttle admission remain open.

| Check | Verified result |
| --- | --- |
| Complete state/output correspondence | 6,039 state bits and 24 output bits matched |
| Clock/reset cones | Equal across all 6,039 state endpoints |
| Fresh public-pin replay | All 35 cases passed, UART/SPI/I²C/JTAG |
| Fault detection | One actual sampler-pin mutant detected |
| Replay coverage | 14 native processes, 513,297 physical sampled edges |
| Pinned Tiny Tapeout precheck | All 9 selected checks passed, no skips or failures |
| Native precheck geometry | Three closed KLayout calls, zero markers in each report |
| Precheck main-deck DRC | Full 332-category inventory, including `NW.b` |
| Aggregate custody | All 3,635 bound files verified, native cleanup confirmed absent |

The target is ODB
`dc654986c54512095c243407ea481ad3675a0269870ee4715dcbd1bd632c6a73`
and GDS
`d4cd48f0919ac47ec4b2ceb061bc5dc6a217ce730b02b819a6b7e09d9e73c832`.
The accepted correspondence receipt is `digital-02/transport.json`, SHA-256
`09a71320c29f15ace79151b1fbfd311af06c6796f7274bb2baab77129981d047`.
Its adapter bytes match commit `336a97b` and source SHA-256
`739ce44935efd20041f9d47395d1cf40fb916a49fa1e8a281a9f5d4ad155ff1b`.

## Correspondence and fresh replay

The comparison maps exactly five named `buf_2` masters to the original
`buf_1` masters and contracts the single `holdcap_delay` identity cell.
All three pinned Liberty corners agree on the A→X identity functions.
The resulting complete named graph and next-state/output model equal
those of the accepted fanout ECO. This composes the earlier semantic
correspondence with these checked identity transformations. The earlier
fanout receipt's graph hashes describe its contracted baseline; the new
receipt explicitly fingerprints the raw fanout comparison basis.

The state mapping uses the actual candidate connectivity, including the
delayed `_0230_/D` endpoint. Fresh replay retained all 42,210 functional
instances, 36,011 active gates, 6,039 flip-flops and 160 antenna diodes.
Signal-free filler/decap membership and every rail binding were checked
separately. The 35-case corpus retained the complete actual-cell model
and its clocks. All 14 native processes closed successfully and the
actual sampler-pin mutation was detected. Replay took 702.832 seconds.

Independent host review rejected nine in-memory changes to data, clock,
reset, buffer/delay master or function, rail binding and delayed-net usage.
Four source-binding controls also checked correct archive selection and
rejection of altered, outside-root or unpinned helpers. The reusable
[adapter](../../scripts/streaming_8x4_hold_cap_digital.py) and
[result verifier](../../scripts/streaming_8x4_hold_cap_readback.py) check
the selected archived worker and canonical helper bytes. Digital evidence
is a zero-delay Boolean model and finite public-pin corpus.

Authoritative evidence uses `digital-02`. The earlier `digital-01` host
comparison preceded the archived-helper pinning refinement and is retained
as exploratory data. The final transport and replay use committed source.

## Tiny Tapeout precheck

The [precheck entry point](../../scripts/streaming_8x4_hold_cap_precheck.py)
used pinned official source at `d66cf179e7bc4d296362ab7e2e3b344dc3c4f665`.
All 21 support files matched their recorded Git blobs and SHA-256 values.
Runtime checks cover the Python interpreter and pinned package-version
inventory. Geometry ran in the pinned offline native image, with one CPU
and a 6 GiB memory/swap ceiling. The completed precheck took 2,051.955 seconds.

The nine checks were pin-label/drawing overlap, CMOS5L DRC, zero area,
KLayout Checks, Pin, Boundary, Layer, Cell name and Analog pin. Their
ordered XML testcases all passed without errors or skips. The three
native KLayout calls were independently rejoined to their input GDS,
report hashes, process identities and zero exits. The full main-deck
report matches the preceding physical run's complete 332-category set.
The staged GDS, LEF, powered Verilog and `info.yaml` match their exact
candidate sources. Source inputs and PDK custody passed the before/after
checks, and owned-container cleanup confirmed absence.

## Reproduction and retained evidence

All work remains local on `codex/8x4-timing-closure` in the same worktree.
Raw artifacts are under the ignored directory
`build/8x4-hold-cap-20261107/trial-02/`. The aggregate receipt is
`digital-precheck-readback.json`. Independent review revalidated every
bound file and every proof, wire and precheck join.

The completed run used the following commands, with `PINWHEEL_HISTORY`
pointing to the retained history checkout. Replay and receipt creation
use fresh output paths to preserve earlier evidence.

```sh
python3 -B scripts/streaming_8x4_hold_cap_digital.py transport \
  --output build/8x4-hold-cap-20261107/trial-02/digital-02
python3 -B scripts/streaming_8x4_hold_cap_digital.py wire \
  --proof build/8x4-hold-cap-20261107/trial-02/digital-02/transport.json \
  --proof-sha 09a71320c29f15ace79151b1fbfd311af06c6796f7274bb2baab77129981d047 \
  --output build/8x4-hold-cap-20261107/trial-02/digital-02/wire --timeout 1800
python3 -B scripts/streaming_8x4_hold_cap_precheck.py --history "$PINWHEEL_HISTORY"
python3 -B scripts/streaming_8x4_hold_cap_readback.py --history "$PINWHEEL_HISTORY"
```

The aggregate records `qualified_timing=false`,
`electrical_power_qualified=false` and `tapeout_ready=false`. Local package
adoption and the remaining qualification inputs are tracked independently
of these completed checks.

## Local artifact manifest

| Artifact relative to candidate directory | SHA-256 |
| --- | --- |
| `digital-02/transport.json` | `09a71320c29f15ace79151b1fbfd311af06c6796f7274bb2baab77129981d047` |
| `digital-02/semantic-state-map.json` | `d2d057e91a0c896f5c21289bcf856470aa1c549bafa4657f4ea3271bd35f206e` |
| `digital-02/sampler-binding.json` | `5b2a7ec0dd8b9f246f61a3318e1c00631becb20d08758ce417df666d57eac517` |
| `digital-02/wire/report.json` | `2bfadee2aff5fd8341b0d00772399571e6c64cabec63da714d4462b9ab30183b` |
| `digital-02/wire/worker/report.json` | `46ed8daacd6e05c93339f31952a982f5621ac97e8e2189229430ceb9124fdd8a` |
| `digital-02/wire/worker/native.jsonl` | `276cec6decfa40a4a89880d5eef661e80ae6165e7c2fcc75137abbc8c6f44d29` |
| `official/rehearsal-tt-precheck-readback.json` | `fb04e8205dec2f3a8ca7177d42281a64fd3041375dcc59f393421900ee066c81` |
| `official/native-klayout.jsonl` | `9999dc0084916415cd094d57cf6d34d3002d34b2aa7c286fd52cbaed251cbb86` |
| `official/tt/precheck/reports/results.xml` | `0cbd8dc7acef4b28442407ed0e11a90c4c8711f663c182463510a65885fcfd15` |
| `official/tt/precheck/reports/drc_sg13cmos5l.xml` | `a31ee7a26146bf0912141c9407f13172156699c2003d495acf9235e2d736bdb5` |
| `digital-precheck-readback.json` | `22a9a418a695e20324632d315a0d28c5991a186383bbd79a38d83dd7f0a414e8` |
