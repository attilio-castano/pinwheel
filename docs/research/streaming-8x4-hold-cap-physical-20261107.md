# 8×4 hold/capacitance candidate physical checks, November 7, 2026

Supplemental enclosure, strict-port transistor LVS and foundry antenna
passed on the exact [hold/capacitance candidate](streaming-8x4-hold-cap-trial-20261107.md).
Main-deck DRC is pending. The completed checks alone do not establish
fabrication readiness. Qualified timing, electrical power qualification
and shuttle admission remain open.

| Check | Result |
| --- | --- |
| Main-deck IHP SG13CMOS5L DRC | Pending |
| Supplemental enclosure | All 11 categories, zero markers |
| Transistor LVS | All 39 circuit pairs matched in strict port mode, NET_ONLY=false, 256 definition-level devices per side |
| Foundry antenna | All 23 categories, zero violation items or multiplicity |

The [exact-target runner](../../scripts/streaming_8x4_hold_cap_physical.py)
checks candidate hashes, completed native execution and cleanup, pinned
deck identities, complete rule coverage, raw result hashes and matching
CDL provenance. All work remains local on `codex/8x4-timing-closure` in
the same worktree. Raw results are in the ignored candidate directory
`build/8x4-hold-cap-20261107/trial-02/`, under `enclosure-01/` and `layout/`.

The candidate ODB is
`dc654986c54512095c243407ea481ad3675a0269870ee4715dcbd1bd632c6a73`.
Its GDS is
`d4cd48f0919ac47ec4b2ceb061bc5dc6a217ce730b02b819a6b7e09d9e73c832`.
The LVS reference is the complete CDL exported from that ODB, including
the newly used `buf_2` and `dlygate4sd2_1` masters. Native layout checks
used the committed worker scripts with unchanged decks and source inputs.
