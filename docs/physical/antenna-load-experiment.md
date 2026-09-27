# Antenna-aware branch experiment

The September 27 follow-up tests one coordinated change to the 15 measured
electrical failures in the [second detailed layout](balanced-detailed-experiment.md).
The user approved this bounded continuation. Prior receipts remain unchanged.

The source is the independently checked seven-buffer coarse circuit. Split each
affected net into spatial groups of at most three functional inputs, each driven
by a new noninverting buffer. This leaves at least five fanout units for antenna
protection on each new leaf. The original drivers see at most three buffer
inputs. Shorter local branches should also reduce wire capacitance. This is a
hypothesis about subsequent protection insertion, not a guarantee that the final
diode count will fit. Every added load must be measured after detailed routing.

The pinned router's `GlobalRouter::repairAntennas` inserts jumpers only when no
detailed routes exist. Its post-detail `jumper_only` flag therefore cannot repair
the saved detailed layout. No CAD attempt is spent on that unsupported strategy.

Keep original placements, the SRAM, clock routes, package constraints, timing
constraints and electrical limits fixed. Reuse the existing scoped route-import
adapter, repeat removal/replay and edit/revert controls for this exact source and
net set, and retain any conservative resource reservation explicitly. No antenna
cell is removed from an accepted artifact; this experiment starts before antenna
insertion and reruns the original antenna checks and repair.

Before detailed routing require exact declared geometry/connectivity edits,
arbitrary-state equivalence including every state input and clock/reset,
package-pin replay, all-corner coarse setup/hold and electrical checks, all 64
SRAM write holds, minimum pin access and zero conservative overflow. The final
candidate needs fresh extraction, the shared all-corner electrical/timing gate,
routing DRC, full-rule Magic DRC, LVS, antenna and power checks. Enable native
cap/slew enforcement on every corner as well. Fast-view qualification and complete
paired refinement remain separate unmet gates.

Allocation: one candidate plan, ten minutes per cheap stage, one additional A
full flow capped at 90 minutes, one CAD process at a time, four CPUs and 6 GiB.
The eight-hour campaign limit and two reserved B attempts remain. Prior charge
is 4,926.281 seconds; failures and controls count. A failed screen closes this
candidate without consuming the additional full-flow slot. No automatic sweep
or second candidate follows under this allocation.
