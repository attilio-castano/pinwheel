# Pinwheel 8×4 scratch fanout trial

The five-net scratch ECO passed the fanout, detailed-router, antenna and
supplemental enclosure checks. The DRT writer also changed 19 additional
ordinary signal wire records. This is a routed experiment with a larger
wire delta than the declared topology edit. The frozen rehearsal ODB and
GDS remain the release reference. [Rehearsal report](streaming-8x4-tt-rehearsal-20261104.md)

The trial started from exact post-fill ODB
`b7e60eded5198fc53df7e5dd1e3ab0f5162720516ab0c1692a1cf7c7bb62602b`.
Five `sg13cmos5l_buf_1` instances replaced five same-footprint
`sg13cmos5l_decap_4` cells on sites clear of the pinned power-grid blockage
rule. All remaining instance records, all original antenna diode
connections, and the die, tracks, public pins and special-net DEF records
matched the source. The placement check passed.

| Original net | Operation | Original loads before → after | Loads on new branch |
| --- | --- | ---: | ---: |
| `net2157` | Equal-master clone | 12 → 8 | 4 |
| `net2298` | Equal-master clone | 10 → 8 | 2 |
| `net11223` | Equal-master clone | 9 → 8 | 1 |
| `net2333` | Serial buffer | 9 → 8 | 2 |
| `net840` | Equal-master clone, fixed leaf cut | 9 → 8 | 1 |

The `net840` operation moved `fanout833/A` to a new routed branch. The
native wire encoder removed exactly four FIXED path records for that
leaf and retained the other 121 path records, including both antenna
bridges. A fresh process reopened the final ODB and verified the exact
625-entry FIXED vector, the clone wiring and power bindings, and a
maximum load count of eight across 44,609 regular signal and clock nets.

The four-net control cleared router markers and OpenROAD antenna and kept
the whole `net840` DEF record byte-identical. It changed 15 additional
ordinary signal wire records and exposed a special-terminal annotation
gap in the initial partition runner. The five-net run marks every new
rail terminal special and verifies the complete DEF partition before
starting routing. Its initial router marker count was 200. The final
count was zero, with zero OpenROAD antenna violations across the block
and on each affected net. Independent KLayout checks on the streamed
scratch GDS had zero markers across 23 foundry antenna categories and
all 11 supplemental enclosure rules.

The 19 collateral wire records retained exact terminal sets. No
collateral clock or FIXED wire record changed. The experiment establishes
fanout and antenna feasibility for the routed derivative. Main-deck
DRC, transistor LVS, updated power and timing signoff, digital
correspondence and Tiny Tapeout precheck remain for any candidate
adoption. Power review needs to account for the five decap replacements.
Hold closure still requires admitted CMOS5L parasitics and the shuttle
I/O contract. [Timing intake](streaming-8x4-e982-timing-intake-20261104.md)

## Retained trial evidence

The ignored directory `build/e982-fanout-20261104/five-01/` contains the
route and screen artifacts. The [local runner](../../scripts/streaming_8x4_e982_fanout_trial.py)
can repeat the experiment into a fresh output directory. The same parent
directory retains the native ODB reopen and independent deck launchers
as `reopen-odb.py` and `screen.py`.

| Artifact | SHA-256 |
| --- | --- |
| `trial.odb` | `e40e40804ddf5c4093f83710ec27b0a5b975f3a047e5c95810e175fbe6aa78f9` |
| `trial.def` | `fbccaa1f145b74050eb5ff257db80cbdd9a3a1b56a530ab27a2d6ba9ad6d23ff` |
| `stream/design.gds` | `dcc496d71202677f6d2fe3785dca6ff9bb225ef954953bf7925171174d4b7e82` |
| `review.json` | `34fe0a51cec73d9476887aefbdcfb8b118ff817fe848c09dfb063d9dd060c213` |
| `reopen/result.json` | `dd753e2ebaa0d0973977c6bb0aa8f45398512715fdbe9c64f67b737e7edb5625` |
| `screen.json` | `86eff28a562f4d51f3719f146e8529cb10db89c703bb8b87d8b992ab64e94170` |
