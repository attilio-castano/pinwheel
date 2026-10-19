# Streaming Tiny Tapeout closure: renewed campaign

Launch: **2026-10-18 15:00:00 UTC** (11 a.m. Eastern).
Deadline: **2026-10-19 03:00:00 UTC** (11 p.m. Eastern).
New candidate CAD admission closes **2026-10-19 00:00:00 UTC**.
Baseline: `f5c6a980158d7c216eb81c8e615734368cca3219`.
Branch: `codex/streaming-tt-candidate`.

The user renewed authorization for an ambitious autonomous campaign after
reviewing the previous morning report and confirming that the machine had
gone down. The preceding twelve-hour maximum is used again. Local code,
bounded proof/CAD work, incremental local commits, review and a report are
authorized. No paid services, external messages, shared-PDK edits, pushes,
PRs, publication or fabrication submission are included.

The goal API rejected a replacement because the previous goal is unfinished.
Its blocked status is preserved: that campaign did not achieve acceptance.
This document records the new authorization and time window without
misrepresenting the previous result.

## Required outcome

Obtain a fully routed, checked **6×4, standard-cell-only, depth-two** candidate
at the existing **20 ns clock** and reconnect its actual implemented digital
netlist to the source contract. Preserve all **6,039 state identities**, the
64×64 program bank, two-word TX/RX queues, SPI 4 KiB duplex streaming,
4,097-bit JTAG, 64-byte reactive I²C and autonomous single-frame UART.
Keep the exact official pin rectangles and declared clock/I/O constraints.

Acceptance requires completed routing; declared-corner extracted setup/hold
and electrical checks using justified CMOS5L RC models; power connectivity;
DRC, LVS and antenna checks; applicable official TT precheck; actual final
netlist public-wire regressions; kernel functional correspondence; and an
audit covering public and private declarations. Unsupported, failed, waived
or unexecuted checks remain gaps. No slower clock, reduced capacity, relaxed
pin geometry, proof assumption or weaker acceptance criterion is implicit.

## Execution order and decision points

1. Establish process ownership, a global single-heavy-job lease, host memory
   and disk admission, wall-time limits, process-group cleanup and durable
   receipts. Parallel agents prepare and inspect on the host; Native Lean
   and CAD are serialized. A keep-awake assertion cannot prevent a reboot.
2. Resolve the three measured public-pin/PDN overlaps and illegal power-port
   geometry. Check every public and power pin against the actual native
   floorplan before committing an expensive route attempt.
3. Replace the measured 64-stage guard chain with a balanced, equivalent
   expression. Verify state identity and correspondence before admitting a
   new candidate. Improve fanout buffering using load locations only where
   measurement supports it.
4. Run placement, CTS and congestion checks early. Continue a viable
   candidate through complete detailed routing, fillers, official geometry
   checks, native extraction/STA and LVS. Failed attempts remain immutable.
5. Complete bounded actual-netlist public-output and clock proofs, typed
   device/pad composition and remaining transport obligations. Explicitly
   establish any compatibility used between old and fresh compiled libraries;
   a declaration comparison is not a fresh rebuild. Run the whole-root axiom
   audit only after all required roots actually compile.
6. At the admission cutoff, concentrate on committed-source regressions,
   independent review, source/tool/input seals and the final evidence report.
   If mandatory gates remain open at the deadline, report their exact status
   and stop owned jobs rather than declaring completion.

The inherited RC model is not accepted merely because extraction executes.
The [upstream CMOS5L model proposal, PR1237](https://github.com/IHP-GmbH/IHP-Open-PDK/pull/1237)
remains a draft on today's read; its September 29–30 discussion leaves process
stack review unresolved. OpenROAD's
[calibration workflow](https://openroad.readthedocs.io/en/latest/main/src/rcx/doc/calibration.html)
binds extraction tables to a specific process corner. Stack qualification is
an explicit separate obligation. Continue useful implementation and proof
work while investigating primary-source evidence.

## Resource policy

The host has 24 GiB RAM; Docker reports about 7.65 GiB. At intake there were
no running proof/CAD jobs or containers, host memory availability was 85%,
and the volume had about 39 GiB free. These are observations, not guarantees.

Only one heavy process tree may run at once. Each attempt must have an
immutable output directory, explicit command and timeout, input hashes and
owned cleanup. Default Native Lean uses one thread and a 4 GiB Lean limit;
larger limits require a measured reason, never concurrent heavy work. CAD
containers remain bounded to at most 6 GiB and four CPUs, with swap disabled
where the producer supports it. Refuse new heavy jobs below 25% reported
memory availability or 12 GiB free disk; stop a running job below 15% or at
its RSS bound. Missing resource observations fail admission. Job receipts
record termination separately from mathematical or physical acceptance.

## Preservation

All evidence and reports committed at the baseline remain immutable. Preserve
the two intake-dirty files and their combined binary diff exactly:

| File | SHA-256 |
| --- | --- |
| `docs/protocols/buffered-spi-refinement.md` | `805eba24279d4dd798c49f92aaaa146005475f9496cafdf393d9f5140aa66d59` |
| `docs/research/status.md` | `c669c35bf690df6c370da43dc6d2cfa6fa96fb3e56be0e9bd2d741a39fb198fe` |

Combined binary diff: `efb3443f8103705eaeb222847c21750cdeeee5b0bde2ec0c3dea6d6eddef1108`.
Use new attempt tags. Commit explicit intended paths only. Kernel acceptance
allows only `propext`, `Classical.choice` and `Quot.sound`, including private
declarations; admitted proofs, custom axioms and Native decision shortcuts
are excluded.

Reference: [previous report](streaming-tt-morning-report.md) and
[extraction scope](streaming-tt-extraction-scope.md).
