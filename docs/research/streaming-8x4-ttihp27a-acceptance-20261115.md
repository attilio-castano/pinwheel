# TTIHP27a acceptance review for the frozen Pinwheel 8×4

I’m requesting review of Pinwheel’s exact filled SG13CMOS5L GDS for a
contiguous 8×4 allocation on TTIHP27a. Pinwheel is a programmable digital
protocol engine for the Jane Street competition. The candidate passes local
rehearsal. Fabrication is on hold pending the shuttle’s decision and the timing
and power inputs below.

## Candidate and evidence

The top cell is `tt_um_pinwheel_streaming_ready_d2`. The outline is
1,724.16 × 710.64 µm with 43 public signal pins and the VPWR/VGND rails.
The frozen source revision is `a305a4b339767e80719c9720a12ced7345b0e814`.
Use the GDS SHA-256 as the acceptance key.

| View | SHA-256 |
| --- | --- |
| Filled GDS | `d4cd48f0919ac47ec4b2ceb061bc5dc6a217ce730b02b819a6b7e09d9e73c832` |
| LEF | `04a956a96fff1b7008d9c2f324866fbb8147e385f57244c81c3ab16474583efd` |
| Logical Verilog | `6b50411924e8bcd369137c0187b25d08e2b0f1f1c5baafbce700a657d893d90e` |
| Frozen OpenDB | `dc654986c54512095c243407ea481ad3675a0269870ee4715dcbd1bd632c6a73` |

- Main-deck DRC, supplemental enclosure and foundry antenna ran on the exact
  filled GDS and reported zero markers across 332, 11 and 23 rule categories,
  respectively. Strict transistor LVS matched all 39 circuit pairs. Both
  power rails passed geometric connectivity across 98,904 instance terminals
  each. [Physical checks](streaming-8x4-hold-cap-physical-20261107.md) ·
  [Power connectivity](streaming-8x4-hold-cap-pg-20261111.md)
- All ten local Tiny Tapeout prechecks passed using the TTIHP27a pins below.
  An independent exact-netlist simulation with IHP cell models passed all 35
  positive public-pin cases and caught a deliberately changed sampler pin.
  One simulated instance ran UART, I²C, SPI and JTAG after successive uploads.
  [Local release rehearsal](streaming-8x4-jane-street-release-20261114.md) ·
  [Exact release behavior](streaming-8x4-jane-street-behavior-20261115.md)

| Rehearsed Tiny Tapeout input | Revision |
| --- | --- |
| IHP Verilog template | `4b1204ab387b5ab94db1d57067051d8d89a2f83c` |
| TTIHP27a GDS and precheck action | `e7a50f8f46f9f8df4b2c9935bfeb1cbc6b6ae4f6` |
| Support tools | `9d13ff3e3e6202090740110438c6a10c1d62ca0f` |
| SG13CMOS5L Ciel PDK | `89d42ee6d2fd9b50b86a1aada6fee6673c3e6008` |

## Requests for Tiny Tapeout integration

1. **Custom GDS and allocation.** Can TTIHP27a review and integrate this exact
   GDS using the custom-GDS action? It came from pinned local hardening with
   audited physical ECOs. The separate clean stock flow reproduced functional
   behavior through synthesis and stopped in detailed routing. Please confirm
   whether the exact custom candidate can use the competition path, or identify
   the hardening evidence required. Please also confirm the contiguous 8×4
   reservation process, required revisions and checks, any additional repair or
   waiver requirements, and which receipt will bind the submitted revision and
   GDS hash to the allocation. [Clean-build report](streaming-8x4-tt-clean-harden-20261115.md)
2. **Timing at the macro boundary.** Please provide the run’s mux/host SDC or an
   equivalent contract with the clock reference, operating modes, edge and
   waveform, latency, skew, jitter and setup/hold uncertainty. Please include
   rising and falling minimum/maximum input and output delays, input slew or
   drive, output load, and reset, enable and bidirectional timing treatment.
   Earliest arrival and slew at `ui_in[3]` and `ui_in[5]`, including the falling
   path at `ui_in[5]`, are the most immediate input budgets needed.
3. **Parent power attachment and boundary.** Please confirm whether 27a
   generates TopVia1 landing arrays from accepted LEF pin rectangles or
   requires the stock power-pin phase. The frozen macro has 35 continuous
   Metal4 stripes per rail, each 2.1 µm wide, at a 49.880 µm pitch. VPWR/VGND
   centers start at 16.400/24.080 µm in macro-local X. The stock template uses
   50.000 µm pitch and starts at 12.880/16.980 µm. For the assigned slot, please
   provide the parent revision, placement and orientation, contact polygons or
   the parent views and via/cut map, and the supply and return reference plane.
   Please specify the guaranteed voltage and temperature range, current and
   activity limits, permitted droop and ground bounce, and the shared feed and
   return impedance or package/board models for static and transient analysis.
   [Historical and stock pin comparison](streaming-8x4-hold-cap-parent-attachment-20261115.md#stock-hardening-pdn-comparison)

Jane Street’s November 9 update confirms the 8×4 maximum for the planned
March 2027 shuttle. The FAQ describes the custom-GDS route for long local
Tiny Tapeout runs with a passing precheck. The exact ECO provenance above is
the question for this candidate. The competition entry deadline is January
18, 2027. A hosted `tt_submission` with passing precheck, the shuttle’s
revision-specific decision, and the organizer’s entry receipt and selection
are distinct steps. [Competition rules and FAQ](https://blog.janestreet.com/protocol-emulator-asic-competition/#faq) ·
[Tiny Tapeout local hardening](https://tinytapeout.com/guides/local-hardening/) ·
[Tiny Tapeout submission](https://www.tinytapeout.com/guides/advanced-workshop/submit-your-design/)

## Requests for IHP or a Tiny Tapeout accepted provider

1. **CMOS5L parasitics.** Please identify an accepted SG13CMOS5L five-layer
   extractor and rule-deck revision, with the applicable process/PDK revision,
   extraction settings for signal metal, vias, fill and coupling, and the
   RC-to-Liberty/PVT pairings for setup, hold and electrical checks. If the
   deck is unavailable, can IHP or an accepted reference service return
   per-corner SPEFs for this exact filled GDS with matched net names, the
   extraction log, tool and rule identities, and the corner matrix? The
   packed logical and powered views and CDL provide circuit references.
   [Public CMOS5L extraction issue](https://github.com/IHP-GmbH/IHP-Open-PDK/issues/1151) ·
   [Draft five-layer rules](https://github.com/IHP-GmbH/IHP-Open-PDK/pull/1237)
2. **Electrical reliability limits.** Please identify the applicable CMOS5L
   sheet, via and contact data and the acceptable EM and thermal criteria for
   the declared lifetime and temperature range. We need average, RMS and peak
   or pulsed criteria where applicable, including narrow Metal1, contact and
   via arrays, and the parent TopVia1 landings. Please specify how to assess
   cut sharing and transient current or any required qualification method.

## What the diagnostic values support

The eight-case timing comparison used released CMOS5L sheet and cut
resistance with draft five-layer capacitance rules, plus a legacy comparison.
The limiting five-layer case has +31.572 ps global hold and +1.554538 ns setup.
Under the draft 200 ps earliest input arrival, `ui_in[3]` and `ui_in[5]` have
+38.855 and +45.780 ps of hold margin. Moving just the two minimum arrivals
40 ps earlier changes those margins to −1.145 and +5.780 ps. Use the included
SDC as the diagnostic reference for supplying the host budget. Qualified
timing needs accepted extraction and a rerun with the actual boundary.
[Timing intake](streaming-8x4-hold-cap-timing-intake-20261114.md)

The static heated I²C case uses a fixed 19.306429 mA per-rail load. A historical
TT0004 contact projection gives 1.255 mV of combined rail loss under the modeled
individual feeds. An illustrative 0.50 Ω shared supply and return adds about
9.653 mV, giving 10.908 mV total. Power qualification needs the assigned 27a
attachment, supply/package boundary, activity envelope and transient and
current-density checks against the accepted limits.
[Parent power analysis](streaming-8x4-hold-cap-parent-attachment-20261115.md) ·
[Workload and attachment intake](streaming-8x4-hold-cap-workload-power-20261114.md)
