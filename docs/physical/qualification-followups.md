# Physical qualification follow-ups

Updated **2026-09-29** for the paired design merge milestone. This is the local
issue tracker for the three open physical requirements. No new Pinwheel GitHub
issue or upstream comment has been submitted. [Research status](../research/status.md)
owns the active decision; this page owns the follow-up actions and closure criteria.

The [current acceptance selection](../../physical/experiments/design-acceptance-readback-inputs.json)
uses the same requirement IDs below. Its [report](../research/implementation-acceptance.md)
still rejects design A; B and the complete design iteration remain unaccepted.
Merging proofs, tools and recorded experiments does not close these requirements.
Closure requires new evidence with exact input identities and an applicable
acceptance intake. A successful command or a provider reply alone is insufficient.

| ID | Status and next-action responsibility | Next input or action | Closure criterion |
| --- | --- | --- | --- |
| `sram_qualification` | **Open; report prepared, unsent.** Pinwheel prepares the reproduction; the component provider supplies the authoritative interpretation or qualification. | Review the [SRAM follow-up](sram-maintainer-followup.md), then post it to existing IHP issue 239 when separately authorized. Obtain a supported width/layer convention or corrected views, and qualification for the exact macro/version and permitted environment. | Resolve the dimensional disagreement and establish the required internal, cross-block and behavioral coverage through supported comparison or a justified component qualification boundary. Replay applicable fixtures and fault controls, then bind the accepted evidence in a new intake. A width-edited diagnostic or boundary-only LVS does not qualify the supplied macro. |
| `timing_conditions` | **Open; component characterization required.** Pinwheel identifies the required environment; the library provider supplies characterization or a supported bound. | Obtain a compatible fast logic/SRAM pair, or a documented bound covering the relevant SRAM arcs and constraints at the declared voltage/temperature. Current standard cells use −40°C and SRAM uses −55°C at 1.32 V. | Assess the saved extracted candidate under qualified, mutually compatible conditions, including supply allowance. All required setup, hold, pulse-width and electrical checks must pass. Renaming a corner or slowing the clock does not establish the missing hold bound. |
| `package_power` | **Open; integration inputs required.** The parent-chip/package design supplies the physical power boundary; Pinwheel evaluates the saved candidate. | Declare contacts on both rails, voltage tolerance, external impedance and a justified activity envelope, then reuse the saved-layout analysis. | Demonstrate an applicable local supply budget consistent with timing and SRAM qualification, with any transient limitations explicitly covered. Retain exact source bindings and complete activity annotation. Illustrative resistance cases and three finite workloads do not establish a package-wide or all-program bound. |

## Evidence and reopening scope

The [September 28 assessment](physical-qualification-assessment.md) and its
[manifest](../../physical/experiments/physical-qualification-results.json) are
frozen historical evidence. Its proposed local power experiment was subsequently
completed as the [September 29 sensitivity study](power-boundary-results.md):
the source count and resistance choices materially change the measured rail loss,
and all signal pins are annotated for three checked workloads. Those measurements
sharpen the required integration inputs; they do not close `package_power`.

The SRAM views and behavioral dependency match pinned PDK
`2bbec755dc67ca3db0261c3d6163e15735d66710`. The
[tile diagnostic](sram-tile-results.md) isolates 96 resistor-width disagreements
while retaining the complete physical tile. The
[provenance study](sram-trust-results.md) establishes that the discrepancy
predates Pinwheel and that a passing macro boundary comparison cannot see it.
The [original maintainer draft](sram-maintainer-report.md) is hash-bound by that
study. It remains unchanged; the linked follow-up incorporates the later layer
question and provides a distinct, reviewable publication draft.

IHP [issue 239](https://github.com/IHP-GmbH/IHP-Open-PDK/issues/239) remains open
in the September 29 read-only check. Its discussion includes work on a different
512×32 macro. [Proposal 1121](https://github.com/IHP-GmbH/IHP-Open-PDK/pull/1121)
is open and unmerged at `22a1f12ed015b52ccb689e71f9f2a3dadd6a8cdb`.
These are dated observations; recheck before posting or adopting a correction.
Record any eventual comment URL, response, new artifact version and disposition
here. No external response or future experiment is required to preserve the
current contribution in the repository.

The retained chip, acceptance policy, 4.5942% historical area overage and routing
budget are unchanged. Campaign usage is **8,843.120 CAD seconds / 147.39 minutes**;
three A routing attempts are used and two B attempts remain reserved. Resume
scoped qualification when its inputs arrive; this tracker authorizes no new CAD
run and makes no claim that the physical campaign is reproducible from source alone.
