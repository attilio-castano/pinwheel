# Successor-fetch experiments

The general 32-entry dense cached core misses the 20 ns target at the slow
corner. Its worst measured path starts at a captured input, selects the next
address, looks up its instruction, and writes the current-word cache. This
study seeks a shorter implementation of that operation while preserving the
same protocol observations on every clock edge.

## Fixed contract and baseline

Preserve every program accepted by the current backend, its capacity checks,
and every defined output: pin levels and enables, capture, status, faults,
loader behavior, and diagnostic reads. Reset, start, commit, same-address
branches, terminal capture feeding a branch, and consecutive one-cycle
branches are part of the contract. Speculative reads must have no effects.

The baseline is `routed4`, retained under `build/physical/core/runs/` and
documented in [physical validation](physical-validation.md). The RTL SHA-256 is
`1664dc719bff05307e3f17a6a8c611aba520917d49be132f1bf164bf1c53548b`.
The diagnostic core uses the same 6×4 rectangle, 20 ns clock, input/output
constraints, pinned tools and PDK for all flow controls. Neither the official
8×4 wrapper nor an external serial loader is included.

`python3 scripts/report-fetch-paths.py --tag routed4` examines the retained
slow-corner extracted maximum-path report and records source hashes in
`build/successor-fetch/routed4/paths.json`. Of its 1,000 reported paths, 112
have negative slack; report counts need not equal unique endpoint counts.
The worst 20 end at cached-word bits. The worst path ends at
`r_cached_word[49]`, with arrival 26.871183 ns, required time 20.617083 ns,
and slack −6.254101 ns.

| Worst-path contribution | Delay (ns) |
| --- | ---: |
| External input delay | 4.000000 |
| Logic-cell arcs | 12.406310 |
| Buffer-cell arcs | 10.185289 |
| Wire arcs | 0.272971 |
| Input-port arc | 0.006611 |

There are 56 output-cell arcs. The largest data-path fanout is nine and the
largest reported slew is 1.493079 ns. Excluding external input delay, 8.055636 ns
precedes the observed `read_b` net and 14.815547 ns follows it. This named-net
split does not separately identify address-map and dictionary costs.
Cell delay includes output-load and slew effects: the small wire-arc total
does **not** establish that wiring is unimportant. The path's clock leaf drives
15 loads. Buffering and electrical limits therefore merit a controlled test
before changing the fetch architecture.

## Experiment gates

1. **F1: fanout control.** Use `physical/experiments/fanout.json` to set the
   synthesis fanout constraint and CTS sink clustering size to eight. Clustering
   is a flow control, not a guarantee that every clock branch satisfies eight.
   Measure the resulting clock-tree area, hold repair and extracted timing.
2. **F2: post-global-route repair.** Continue from F1's global-route checkpoint
   with `physical/experiments/fanout-repair.json`. Enable design and timing
   repair after global routing. Compare with an unrepaired continuation from
   the same checkpoint. Keep repair cost separate from F1's effect.
3. **Combinational architectures, if needed.** A reads both candidate address-map
   indices, selects an index late, then reads the dictionary once. B reads both
   complete candidate records and selects a record late. C moves 55-to-64-bit
   expansion after record selection, if measured logic identifies expansion as
   useful to move. Each candidate must cover sequential, branch and idle paths;
   only the chosen successor can affect state.
4. **Proof and screening.** Prove lookup equivalence, then complete step/trace
   correspondence using the [timed contracts](timed-components.md). Run independent
   RTL regressions and a deliberately faulty variant before comparing full-core
   mapped area and timing. Preserve the baseline; reject candidates dominated in
   both area and timing. Route at most two architectural candidates, recording
   where the worst path moves and whether register-started paths become limiting.
5. **Physical acceptance.** Require fresh extracted setup and hold at all three
   PVT corners, electrical-limit checks, routing/Magic DRC, antenna checks, LVS,
   and the implemented-netlist regression. Report functional cell area before
   fillers and preserve failed results. A pass with negligible slack needs a
   margin review before further architectural work can be dismissed.
6. **Latency-changing storage only if necessary.** First prove availability and
   bandwidth for arbitrary accepted programs, including an endless sequence of
   one-cycle input-dependent branches. A registered prefetch or SRAM proposal
   cannot silently insert stalls or weaken the sampling schedule.

If the flow controls close timing and electrical limits with useful margin,
stop at that evidence gate and assess the value of architectural complexity.
The experiment list is conditional; it is not a commitment to build every
candidate.

## Reproduction and status

The runner allows only the four controls above in `--overrides`. Clock period,
I/O constraints, floorplan and RTL cannot be changed through that option. Each
run gets a new tag, frozen config/RTL/SDC, and a receipt with source identities.
Resume states must come from the matching implementation and configuration;
the runner records the checkpoint hash, but does not prove resume compatibility.

```sh
python3 scripts/run-physical.py --tag fetch-fanout --overrides physical/experiments/fanout.json --to OpenROAD.GlobalRouting
python3 scripts/run-physical.py --tag fetch-fanout-route --overrides physical/experiments/fanout.json --from-step OpenROAD.CheckAntennas --state build/physical/core/runs/fetch-fanout/39-openroad-globalrouting/state_out.json
python3 scripts/report-physical.py --tag fetch-fanout-route
python3 scripts/report-fetch-paths.py --tag fetch-fanout-route
```

The baseline decomposition is complete. F1 has reached global routing, and its
unrepaired continuation is running. F2 and the conditional architectural gates
remain pending. Mid-PnR states can inherit stale corner metrics; only final
extracted STA supports a routed timing comparison.
