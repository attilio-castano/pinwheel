# First routed Tiny Tapeout streaming candidate

Launch: **2026-10-18 02:32:27 UTC**. Deadline: **2026-10-18 14:32:27 UTC**.
Final verification reserve begins **2026-10-18 11:32:27 UTC**.
Branch: `codex/streaming-tt-candidate`.
Baseline: `787260b07c7dffc06799feeee6fd604e0b290fe7`.

The user explicitly approved the proposed twelve-hour physical-candidate
campaign. Local implementation, incremental commits, bounded CAD, proof work,
independent review and evidence/report production are authorized. Publishing,
push/PR, paid services, provider messages and fabrication submission are outside
this campaign. Existing evidence and shared PDK files remain immutable.

## Mandatory finish line

Take the qualified depth-two programmable streaming device through the official
CMOS5L Tiny Tapeout 6×4 physical flow, retaining its source-to-implementation
functional correspondence. Preserve the 64×64 program bank, two-word TX/RX
queues, host contract, long duplex SPI, JTAG, reactive I²C and autonomous
single-frame UART capabilities. The qualified source is
`7715ba61c9a837aa96916e823f65c8e7b6a653d9`; its evidence is preserved by the
baseline checkpoint.

Success requires completed detailed routing, extracted setup/hold and
electrical acceptance at the declared clock/I/O/corner conditions, named
DRC/LVS/antenna/power-connectivity results, the applicable official TT precheck,
actual final-netlist functional correspondence and independent public-pin
regressions. Missing, unsupported, disabled or waived checks remain gaps.
Do not call a routed artifact tapeout-ready while a required gate is open.

The comparison target is a **20 ns clock**, maximum/minimum input and output
delays of **4.0 / 0.2 ns**, **0.2 ns clock uncertainty**, buffer-2 input drive
and **10 fF output load**. Supported timing and RC conditions must be recorded
from actual inputs; nominal RC must never be relabelled min/max RC signoff.
Clock period, capacity, pin map or protocol behavior cannot silently change to
manufacture a passing result. A separately characterized slower profile is
additional evidence, not acceptance of the 20 ns target.

## Ordered execution

1. Freeze exact depth-two state, netlist, library, tool, PDK, official pin/DEF
   and constraint identities. Create a separately named standard-cell-only
   target and explicit PDN; do not inherit the old SRAM configuration.
2. Start placement, CTS and congestion measurements early. Investigate actual
   bottlenecks and compare bounded source-bound candidate attempts.
3. If needed, optimize combinational logic while first retaining all 6,039
   source FF bits and their meanings. Changed mappings require new kernel
   correspondence. No retiming, FSM recoding or state quotient is implicit.
4. Account for actual buffers, tie cells, resizing and clock-tree edge polarity.
   Re-export the final physical database and certify its real connectivity;
   a pre-PNR netlist alone does not cover implementation transformations.
5. Pursue detailed routing and each declared physical check, then reconnect
   source/session proofs and execute the final-netlist wire corpus.
6. Reserve the final three hours for committed-source checks, independent
   review, clean replay, immutable accepted/failed receipts and a final report.
   Stop launching new candidate CAD at the reserve boundary.

Ordered stretches after depth-two acceptance: an independent clean physical
rerun, depth-four qualification, then improved timing headroom. Twelve hours
is a maximum budget, not a completion guarantee. At the deadline preserve and
report remaining obligations; an incomplete mandatory goal stays incomplete.

## Ownership and resource boundaries

The physical agent owns the new target/preparer/runner and serializes native
CAD producers. The optimization agent owns state-preserving combinational
changes and their correspondence. The formal agent owns post-PNR/CTS
certificates. The root owns integration, physical-acceptance observations,
fresh gates, commits and final evidence. Native runs use fresh tags, explicit
wall-time/resource caps, frozen inputs and owned cleanup; no unrelated jobs
or historical attempt is stopped or overwritten.

The pinned ARM64 LibreLane image and retained PDK/official DEF were inspected
read-only before approval. This checkout has no staged `build/physical` yet.
The retained source is
`/Users/attiliocastano/Developer/pinwheel/build/research-archives/2026-10-16-tt-buffered-8259/build/physical`.
Validate all regular files, symlinks and actual runtime identities again before
use; prior availability is not a new execution receipt.

## Intake preservation

These documents were already dirty and remain outside campaign commits:

| Path | SHA-256 |
| --- | --- |
| `docs/protocols/buffered-spi-refinement.md` | `805eba24279d4dd798c49f92aaaa146005475f9496cafdf393d9f5140aa66d59` |
| `docs/research/status.md` | `c669c35bf690df6c370da43dc6d2cfa6fa96fb3e56be0e9bd2d741a39fb198fe` |

The combined binary diff hashes to
`efb3443f8103705eaeb222847c21750cdeeee5b0bde2ec0c3dea6d6eddef1108`.

Kernel artifacts allow only `propext`, `Classical.choice` and `Quot.sound`,
including private declarations. `bv_decide`, `native_decide`, custom axioms
and admitted proofs do not qualify. Digital functional certificates remain
distinct from clock skew, analog/CDC, board and silicon observations.
