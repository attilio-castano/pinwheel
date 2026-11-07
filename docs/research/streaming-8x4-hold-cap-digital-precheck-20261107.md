# 8×4 hold/capacitance digital correspondence and precheck, November 7, 2026

Fresh Boolean correspondence passed on the exact candidate that passed
[all four physical checks](streaming-8x4-hold-cap-physical-20261107.md).
Fresh public-wire replay also passed. Pinned Tiny Tapeout precheck is running.

| Check | Current result |
| --- | --- |
| Complete state/output correspondence | Passed, 6,039 state bits and 24 output bits |
| Clock/reset cones | Equal across all 6,039 state endpoints |
| Fresh public-wire replay | Passed, all 35 cases and sampler mutation detection |
| Pinned Tiny Tapeout precheck | Running |

The target is ODB
`dc654986c54512095c243407ea481ad3675a0269870ee4715dcbd1bd632c6a73`
and GDS
`d4cd48f0919ac47ec4b2ceb061bc5dc6a217ce730b02b819a6b7e09d9e73c832`.
The accepted correspondence receipt is
`build/8x4-hold-cap-20261107/trial-02/digital-02/transport.json`, SHA-256
`09a71320c29f15ace79151b1fbfd311af06c6796f7274bb2baab77129981d047`.
Its adapter bytes match commit `336a97b`.

The comparison maps exactly five named `buf_2` masters to the original
`buf_1` masters and contracts the single `holdcap_delay` identity cell.
All three pinned Liberty corners agree on the A→X identity functions.
The resulting complete named graph and next-state/output model equal
those of the accepted fanout ECO. This composes the earlier semantic
correspondence with these checked identity transformations.

The state mapping uses the actual candidate connectivity, including the
delayed `_0230_/D` endpoint. The fresh wire replay retains all 42,210
functional instances, 36,011 active gates, 6,039 flip-flops and 160 antenna
diodes. Signal-free filler/decap membership and every rail binding are
checked separately. The replay uses the existing 35-case public-pin
corpus with an actual sampler-pin mutation.

Independent host review rejected nine in-memory changes to data, clock,
reset, buffer/delay master or function, rail binding and delayed-net usage.
Four source-binding controls also checked correct archive selection and
rejection of altered, outside-root or unpinned helpers. The reusable
[adapter](../../scripts/streaming_8x4_hold_cap_digital.py) and
[result verifier](../../scripts/streaming_8x4_hold_cap_readback.py) preserve
and check the selected archived worker and canonical helper bytes.

The [precheck entry point](../../scripts/streaming_8x4_hold_cap_precheck.py)
uses the pinned official source and all nine checks selected for CMOS5L,
including another full main-deck DRC. Runtime binding covers the Python
interpreter and pinned package-version inventory. All raw artifacts stay
in the ignored candidate directory. Qualified extracted timing, electrical
power qualification and shuttle admission remain open.

The fresh wire run closed all 14 native processes, validated 513,297
physical sampled edges and detected the actual sampler-pin mutation.
Independent readback reopened its raw traces, journal and artifact set,
verifying 3,599 bound files. The wire receipt is
`digital-02/wire/report.json`, SHA-256
`2bfadee2aff5fd8341b0d00772399571e6c64cabec63da714d4462b9ab30183b`.
