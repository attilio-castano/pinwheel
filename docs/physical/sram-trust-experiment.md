# Bounded SRAM provenance and reference-flow investigation

The user authorized the proposed investigation on September 27: trace the exact
supplied SRAM views, compare their intended verification flow with the linked
Tiny Tapeout example, and prepare a concrete maintainer report if the remaining
interpretation is undocumented. Start from **8,390.384 campaign CAD seconds**.
The outcome is an evidence-backed trust-boundary proposal, not automatic SRAM
or chip admission.

Check the seven physical/behavior/timing views used by the retained chip against
the pinned complete PDK tree. Trace source history for the schematic widths and
layout markers, distinguish the tested 1024×8 example from our 512×64 macro, and
record the exact public reference revision, flow version and PDK. Resolve mutable
references once and retain downloaded source bytes, URLs, dates and hashes.
Repository comments and examples describe their own policies; they are not
foundry qualification certificates for another configuration.

Inspect the native implementation of macro abstraction. Run a small comparison
with the unchanged supplied SRAM and its exact interface under that policy,
including signal/power connection faults where a positive control passes.
Account explicitly for which internal faults an abstract comparison cannot
detect. Reuse existing strict internal and chip-boundary receipts where source
identity holds; do not rerun broad chip extraction merely to reproduce known
failures. A tool exit, blackbox match or different macro's silicon test cannot
be reported as internal verification of this macro.

Use at most **900 additional CAD seconds**, within the existing eight-hour
campaign. Each offline pinned invocation is capped at 600 seconds, four CPUs
and 6 GiB, with one container at a time. Allow at most two implementation/repair
cycles per hypothesis. Freeze executable inputs before each invocation, retain
all failures and cleanup, and never overwrite an executed output directory.
Raw sources and receipts live under `build/validation/sram-trust-01/`.

Preserve the chip, installed PDK, supplied views, prior fixtures/manifests and
historical verdicts. Any interpretation remains a separate diagnostic. No new
full chip route, unrelated block qualification, source width edit, error waiver,
publication or message to maintainers is authorized by this experiment. Prepare
an unsent report and a precise qualification question for review if needed.

State separately: provenance, integration checking, supplied macro behavior,
timing qualification, internal transistor/geometry verification, and the Lean
assumptions that remain. Existing fast-view, full-refinement, A/B and replay
gates continue unless new evidence actually discharges them.
