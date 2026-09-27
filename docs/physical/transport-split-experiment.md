# Split the two wire-dominated parent routes

The user approved this continuation on September 27 after reviewing the
[rejected antenna-headroom placement](antenna-load-results.md). Preserve its
41 buffers and all preceding receipts. The source is electrically rejected but
has validated geometry, circuit equivalence, timing and route resources; it is
an input for repair, not an accepted physical design.

Insert one noninverting transport buffer on each of `_03354_` and
`paired_balanced_148_17_out`. Choose a cut of the saved routing tree using the
existing calibrated layer capacitances and measured pin loads. Minimize the
larger parent/child capacitive load, including a conservative allowance for
connecting a legal nearby placement to the saved route. The estimate selects
a proposal; fresh routed measurements decide admission. Keep all original cells,
the 41 antenna-headroom buffers, clocks, SRAM and package geometry fixed.

The bounded refinement permits at most two placement proposals for this same
two-net hypothesis if the first screen rejects it and provides a concrete
correction. Controls, circuit checks and cheap measurements each have a
600-second cap. Use one CAD process at a time, four CPUs and 6 GiB. Charge
failures and retries against the existing eight-hour aggregate; starting charge
is 5,052.680 seconds. No additional full-flow slot is created: at most the one
already allocated third A attempt can follow a passing candidate. The two B
attempts remain reserved behind accepted A.

Require exact import/removal/replay and edit/revert controls, declared
connectivity and geometry, arbitrary-state equivalence including clock/reset,
package-pin replay, all-corner coarse timing/electrical checks, all 64 SRAM
write holds, zero conservative overflow and minimum pin access before detailed
routing. Both sides of each transport buffer must have at least 20% coarse
capacitance headroom (at most 0.240 pF), without relaxing the library limit.

The full continuation must retain antenna protection, extract the final wires,
and repeat circuit identity, all-corner timing/electrical, DRC, LVS, antenna and
power checks. Explicitly enforce native capacitance and slew checks on all
corners and independently check fanout. Fast-view qualification and complete
paired refinement remain separate, open obligations.
