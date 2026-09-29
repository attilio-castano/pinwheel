# Physical qualification: what can move locally

Assessment dated **2026-09-28**, after the paired RTL interpretation gate.
**All three physical blockers remain open.** The bounded inventory identifies
two component-provider dependencies and a power experiment that needs an
explicit integration contract. A and B retain their existing admission gates.

| Requirement | Decision | Evidence needed to advance |
| --- | --- | --- |
| SRAM qualification | **External evidence required.** The supplied source/layout width disagreement persists. The current upstream proposal does not resolve it. | An authoritative width/layer interpretation or corrected views, plus exact-version internal and behavioral qualification for the permitted operating environment. |
| Fast timing conditions | **External characterization or a justified bound required.** No compatible replacement appears in the pinned or captured development-tree libraries. | SRAM characterization at −40°C / 1.32 V, a supported alternative logic/SRAM pair, or an applicable bound on the affected delay and constraint arcs. |
| Package power | **A local experiment can resolve part of the question.** Source placement, external impedance and activity must become declared inputs. | Supply-entry geometry and voltage/impedance bounds from the parent chip or package, a justified activity envelope, and power analysis tied to those inputs and the timing voltage limits. |

The [manifest](../../physical/experiments/physical-qualification-results.json)
binds the inventory, public captures and this study. The
[audit recipe](../../physical/fixtures/physical-qualification/README.md)
reproduces the measured inventory without CAD. This pass adds **zero CAD
seconds**; campaign use stays **8,412.163 seconds / 140.20 minutes**, with three
A routing attempts used and two B attempts reserved. No external message was
sent. The acceptance policy, supplied libraries and filled candidate are unchanged.

## SRAM: narrow the provider question

The seven supplied views and behavioral dependency still match the pinned
`2bbec755dc67ca3db0261c3d6163e15735d66710` release. Their seven view blobs also
match both captured upstream branches: `main` at
`5e6d592e4002946a4616f798c357f0f3c06cf3b6` and `dev` at
`0488153564fdae82164201091e1c4375b97e61ad`. These are dated inventories, not
evidence that future releases will remain unchanged.

[Issue 239](https://github.com/IHP-GmbH/IHP-Open-PDK/issues/239) is open in the
fresh capture. Its 14 comments include the historical commercial LVS claim and
work on a different 512×32 macro, but no exact-input report or rule explaining
our 0.260 µm source / 0.200 µm physical markers. The existing
[maintainer report](sram-maintainer-report.md) remains the primary question set.

There is a useful change in the live
[lvsres proposal](https://github.com/IHP-GmbH/IHP-Open-PDK/pull/1121): at captured
head `22a1f12ed015b52ccb689e71f9f2a3dadd6a8cdb` it is open and no longer a draft.
The complete 47-file diff includes our 512×64 CDL. Its three single-port bit-cell
resistors gain `layer=Metal1` while keeping `w=2.6e-07 l=6e-07`.
The retained [physical witnesses](sram-tile-results.md) place R0/R1 on metal2
and R2 on metal3. This is an apparent additional source/geometry disagreement
to ask about, not an adopted correction. The proposal is unmerged and includes
no Magic file changes. The cached browser page still showed its earlier draft
state; the fresh API capture supplies this dated observation.

**Supplement to the unsent report:** ask the provider to explain the proposed
Metal1 annotations as well as the width convention, or identify authoritative
replacement views. A corrected tile alone would still leave the other SRAM
contexts, cross-block wiring, behavioral and operating-condition obligations.
The next independent internal comparison should wait for that interpretation;
passing the width-edited diagnostic cannot settle it.

## Timing: a library inventory, not a temperature extrapolation

The audit reads Liberty contents and checks their Git blob identities. It
inventories all six CMOS5L standard-cell libraries and all three libraries for
the exact SRAM. The relevant pairings are:

| Condition | Standard cells | SRAM | Assessment |
| --- | --- | --- | --- |
| Typical | 1.20 V, 25°C | 1.20 V, 25°C | Voltage and temperature agree. |
| Slow | 1.08 V, 125°C | 1.08 V, 125°C | Voltage and temperature agree. |
| Fast | 1.32 V, −40°C | 1.32 V, −55°C | Unqualified mixed-temperature pairing. |

The remaining standard-cell files describe the 1.5 V family, so they do not
provide a compatible 1.32 V alternative. All nine libraries retain the same
blobs in the captured `dev` tree. The captured `main` tree lacks CMOS5L and
therefore is not an alternative CMOS5L characterization set. None of the nine
files supplies timing `k_temp_*` coefficients. The SRAM files do contain two
power-temperature coefficients, both zero; these do not describe timing arcs.
The macro documentation lists three characterized corners and its operating
range, without the required cross-temperature arc bound. Range membership alone
does not supply that bound.

The saved reports help scope a future request: the **+0.026979 ns** global fast
hold margin belongs to `ui_in[5]` → `_14362_`, a standard-cell path. All 64 SRAM
write-data hold paths are present; their minimum is **+0.112677537 ns** at
`A_DIN[42]`. Those are observations under the mixed pair, not a bound on how
the missing characterization could change the answer. SRAM read, address,
enable, pulse-width, setup and hold behavior must retain their own coverage.

**Provider request:** supply a characterized compatible fast pair or document
why the delivered SRAM view bounds each relevant arc/constraint under the
declared environment, including the voltage allowance consumed by power loss.
Renaming a library or choosing a nominal temperature does not create those data.
A slower clock does not resolve a hold-condition qualification gap.

## Power: make the boundary conditions real

The saved typical-corner report measures **9.119430 mW** of modeled design power;
its IR report rounds this to 9.12 mW. It reports **0.257 mV** worst VPWR drop
and **0.285 mV** worst VGND rise. Those rail extrema are separate locations;
their sum is not a measured local differential voltage.

The retained configuration has `VSRC_LOC_FILES=null`. Inspection of the pinned
[OpenROAD solver](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/psm/src/ir_solver.cpp)
clarifies what “automatic sources” means: without a source file, it first uses
block power-pin shape nodes, and falls back to a generated source grid only
when none exist. The actual DEF exposes VPWR as 86 shapes (44 TopMetal1, 42
Metal4), and VGND as 85 shapes (43 TopMetal1, 42 Metal4). These span grid straps.
The expected supply boundary therefore distributes sources over those shapes;
the exact runtime source-node count was not instrumented in this assessment.
It must not be described as a measured package pad or bump arrangement.

The pinned [OpenSTA power code](https://github.com/The-OpenROAD-Project/OpenSTA/blob/857316ff001b2a8dbbdc5996944d08a6d38c87ab/power/Power.cc)
seeds unspecified input activity at 0.1 transitions per minimum clock period
and duty 0.5, then propagates activity. At the declared 20 ns clock this input
seed is 5 million transitions per second; clocks and propagated internal nodes
have their own activity. The saved flow provides no waveform activity replay.
The 9.12 mW estimate is consequently not a maximum over legal Pinwheel programs.

The pinned flow accepts explicit source files for **both rails**. Its power
solver also exposes an external-resistance setting, whose documented default
is zero. These mechanisms can model declared conditions; they cannot determine
which conditions a parent chip or package actually supplies. The digital
“package” module in the Lean proof is an I/O wrapper, not that physical supply
environment.

### Next local experiment and its admission conditions

Use the saved ODB/SPEF and a separate analysis directory. Before running:

1. Bind source regions to the candidate's actual power geometry. Record both
   rails' locations, contact dimensions, voltage tolerances and the interpretation
   of external resistance. Obtain or explicitly propose the parent integration
   contract; unknown values remain unknown, rather than becoming zero.
2. Declare which activity claim is being measured. Capture clocked idle, legal
   maximum-rate upload/replacement, and execution traces using the existing
   controller/host contract. Trace coverage is a workload observation; a general
   power bound needs a justified envelope including internal switching and SRAM
   mode-dependent power.
3. Declare allowable local rail voltage consistently with timing qualification.
   For a conservative lower-bound check, source differential voltage minus
   VPWR drop and VGND rise must remain above the qualified minimum. A source
   already at 1.08 V leaves no drop budget against the 1.08 V slow library.

Then reproduce the default analysis as a control and vary source placement and
activity separately before combining them. Record per-rail drop, local supply
bounds, modeled total/macro power and continuity. Confirm explicit sources
actually bind to the intended geometry. Any illustrative source or resistance
choice stays labeled as a sensitivity case until the integration contract
supports it. Static IR analysis does not settle transient package noise or
SRAM-internal supply behavior.

**Exit:** a power result under justified integration/activity conditions, or a
specific failed voltage budget. If integration data remain absent, retain the
conditional sensitivity result and the package-power blocker. Full routing is
not needed to answer this first power-model question.

## Validation and stop decision

The replay checks 64 file identities, reconstructs the captured Git trees and
their subtrees, matches all nine libraries to the pin, verifies the exact
candidate artifacts, and extracts the retained timing/power/port observations.
The first audit refused because a GitHub tree response echoed a commit ID in
its `sha` field. The corrected recipe reconstructs the Git tree objects and
checks them against each commit's tree identity; no identity check is waived.
The selected inventory and a fresh replay are byte-identical. Local validation
also passes 723 links and 113 anchors across the nine affected documentation
pages, checks the manifest/input identities, and passes `git diff --check`.
No Lean, circuit or CAD change calls for a new physical or formal test run here.

This assessment stops at the available evidence. No suitable replacement fast
view or authoritative SRAM convention was found in the named inventories and
captured discussions; that is a bounded search result, not a claim that none
exists privately. Resolve those provider questions and declare the physical
power interface, then run the scoped checks. The
[acceptance intake](../research/implementation-acceptance.md) needs new
identity-bound evidence before any blocker can change. Accepted A still
precedes the 64-record B experiment and clean-source replay.
