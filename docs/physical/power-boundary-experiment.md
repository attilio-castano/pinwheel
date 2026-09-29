# Power boundary sensitivity experiment

Frozen 2026-09-29 before native analysis. This is a diagnostic study of the
unchanged filled A chip, following the
[physical qualification assessment](physical-qualification-assessment.md).
It cannot qualify an unspecified package, SRAM or timing corner.

## Question and controls

How much do static power-grid results change when we replace distributed ideal
supply terminals with a few explicit contacts, add external resistance, and use
finite functional activity instead of the default activity estimate?

1. Replay the retained nominal 1.2 V, 25 C, 20 ns baseline, reporting the actual
   resolved supply sources, power and both rail drops.
2. Select four contacts per rail from actual top-metal grid nodes inside the
   exported power pins. Record their coordinates before running the scenario.
   Use ideal contacts, then illustrative 1 and 10 ohm resistance **per resolved
   source node**. These values are sensitivities, not measured package values.
3. Generate checked functional traces for clocked idle, a complete legal
   replacement upload and a running branch loop. Preserve initialization,
   before/after pin checks, exact measurement windows and 20 ns clock timing.
   Report waveform matching and unknown signals. No SDF/glitch completeness or
   maximum-over-all-programs claim is made.
4. Compare the activity cases on the same four-contact ideal boundary; combine
   the highest measured total-power workload with the 10 ohm sensitivity.
   Adaptive corrections must retain unsuccessful attempts and their cost.

The minimum rail-differential estimate subtracts worst VDD drop and worst ground
rise from 1.2 V. Those extrema may occur at different locations: their sum is a
conservative bound within this static model, not a measured simultaneous local
voltage. No transient inductance, package model or supply tolerance is supplied.
Exported PG SPICE is used only to inspect source-node identity: the pinned
exporter omits the external series-resistance setting.

## Inputs, budget and decision

Use the exact finalization ODB, nominal SPEF, original SDC/environment and pinned
standard-cell/SRAM models. The request binds these inputs, tooling and prior
acceptance record by SHA-256. All physical inputs are read-only in a pinned,
offline container. Do not reroute, change libraries, edit SRAM internals, change
acceptance rules or send maintainer messages.

The continuation cap is **900 CAD seconds**, with **600 seconds maximum per
invocation**, **4 CPUs / 6 GiB** for native analysis, and the existing
**28,800-second campaign cap**. Starting campaign cost is **8,412.163 seconds**.
Count native analysis and functional CAD simulation, including failed attempts
and cleanup. No additional full-route attempt is allocated; B retains its two
reserved attempts.

Success is an auditable sensitivity result and a concrete integration-data
request. The acceptance readback remains authoritative: A is unaccepted and B
is not admitted until the existing SRAM, timing-condition and package/power
blockers are discharged.
