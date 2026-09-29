# A concrete request for package-power analysis

The saved-layout evaluator exists. The missing gate is a supported integration
boundary and operating envelope. The new
[request](../../physical/fixtures/package-power-contract/contract.json) makes
those absent inputs explicit, assigns their owners and binds the unchanged A
chip, all eight physical candidate artifacts, circuit readback and the retained
20 ns clock with VPWR/VGND rail identities. This is local request preparation;
`package_power`, SRAM qualification and compatible fast timing remain open.

The [checker recipe](../../physical/fixtures/package-power-contract/README.md)
uses no CAD. It refuses changed or disconnected bindings and malformed values,
and reports missing evidence as `incomplete_request`. Its numeric checks remain
active under optimized Python. The frozen
[power study](power-boundary-results.md) and its manifest are unchanged.

Each requirement has `owner`, `status`, `value`, `evidence` and `stop_condition`.
An absent input must use `status: missing`, `value: null`, `evidence: null`.
Zero resistance, zero transient loss and zero supply tolerance are positive
assertions requiring supplied evidence; they are never defaults. A supplied
input uses `status: supplied` and an evidence identity with relative `path` and
64-character lowercase `sha256`. Values have these exact fields and units:

| Requirement / owner | Typed supplied value | Review or stop criterion |
| --- | --- | --- |
| `parent_geometry` / parent-chip integrator | `ownership` text; `contacts` list with `rail`, `layer`, `x_um`, `y_um`, `width_um`, `height_um` | Positive-size contacts on both rails; require ownership and actual exported-shape containment. The checker only checks structure; the existing source validator must check containment and native source resolution. |
| `source_voltage` / parent or package integrator | `reference_point` text; `minimum_v`, `maximum_v` in volts | Actual guaranteed source differential and tolerance at the named boundary. Do not replace this with a nominal voltage. |
| `external_impedance` / parent or package integrator | `interpretation: ohm_per_resolved_source_node`; `vpwr_ohm`, `vgnd_ohm`; `return_path` text | The saved static evaluator applies resistance independently to each resolved source. A lumped package resistance or distributed RLC model needs a separate analysis and explicit interpretation. |
| `operating_envelope` / Pinwheel and integrator | `temperature_min_c`, `temperature_max_c`; `clock_period_ns: 20`; `program_scope` text | Declare legal program/input domain and temperature range. A different clock/candidate needs a new request intake. |
| `activity_envelope` / Pinwheel and component provider | `total_power_upper_bound_mw`; `method`, `program_scope` text; `supported_modes`; boolean `includes_physical_glitches`, `includes_macro_energy` | Cover `clocked_idle`, `replacement_upload`, `execution` under the declared domain. Missing glitch or macro-energy coverage blocks readiness; finite observed power is insufficient to establish a bound. |
| `supported_local_supply` / logic and SRAM library provider | `minimum_v`, `maximum_v`; `temperature_min_c`, `temperature_max_c`; `fast_pair_compatibility: supported_pair` or `supported_bound` | Exact-version support must cover the requested environment, timing arcs and constraints. Mixed-temperature analysis requires a supported bound. The checker checks declarations and hashes; it does not validate provider authority or characterization contents. |
| `transient_allowance` / parent or package integrator | `loss_mv`; `method`, `scope` text | Justify loss allowance and coverage for transient package noise, including any upper-voltage limitations. Static IR does not supply this evidence. |
| `analysis_conditions` / Pinwheel and component provider | `model_voltage_v`; `logic_temperature_c`, `sram_temperature_c`; `parasitic_corner: min`, `nom` or `max` | The selected voltage must cover the declared source minimum. Nominal losses cannot be relabeled as a slow-corner result. Coverage across the full permitted range still needs scoped worst-case analysis. |

A structurally complete request may report `ready_for_scoped_analysis: true`.
It always reports `qualification: false`, `A_accepted: false`,
`contact_containment_verified: false` and `provider_claims_validated: false`.
Readiness means the declarations and evidence identities can be reviewed and
consumed by the saved evaluator. A hash establishes identity; it does not prove
that an attached statement supports the declared values.

## What the existing traces cover

The checker binds the recorded window and connected-unknown summaries and checks
the three accepted manifest rows' 38,497-pin annotation counts. It does not rerun
simulation, reparse every VCD, or independently qualify the macro power model.

| Finite observation at 20 ns | Window | Coverage retained | Coverage absent |
| --- | --- | --- | --- |
| Clocked idle | 8,192 cycles / 163.84 µs | Clock running; unread result retained after completed UART. Both banks initialized. | All possible idle metadata/data states, analog leakage variation and a universal idle bound. |
| Replacement upload | 63,656 cycles / 1,273.12 µs | BEGIN, 290 legal PUSH frames and COMMIT; prior active bank retained until commit. | Every legal payload/input transition, abort/error/reset history and worst-case upload switching. |
| Execution | 8,192 cycles / 163.84 µs | Busy sampled-input branch loop with input fixed at 1. | All instructions/programs, changing sampled inputs, all branch histories and maximum internal switching. |

All three are finite zero-delay functional observations with zero connected
unknown bits in the retained audit. Complete pin annotation removes a missing
activity-data problem; it does not establish physical glitch completeness or
maximum power. The default vectorless estimate happens to exceed these three
total-power observations, which does not make it a universal envelope.

The next activity task is to define the permitted program/input domain and build
a mode-specific switching argument or conservative bound, including clock and
internal activity. Any additional stress traces remain observations until that
argument establishes coverage. SRAM mode-dependent energy and internal supply
behavior still require supported component evidence. Package inductance,
transient droop, overshoot, temperature effects and electromigration remain
outside the static nominal study.

## Voltage budget and next gate

The lower local supply estimate is:

```text
local_min_v = source_min_v
              - (worst_vdd_drop_mv + worst_ground_rise_mv + transient_loss_mv) / 1000
margin_v = local_min_v - supported_local_min_v
```

The two rail extrema may be at different locations; adding them is conservative
within the solved static model. The helper performs dimensional arithmetic and
always returns `qualification: false`. Its diagnostic outputs retain the actual
nominal 1.2 V / 25°C conditions, with no supported-supply margin asserted. The
36.6201 mV combined workload sensitivity corresponds to 1.1633799 V in that
nominal model; it supplies no 1.08 V slow-corner qualification.

Once source minimum, supported local minimum and transient allowance are supplied,
the checker computes the available static rail-loss budget. A source already at
1.08 V against a 1.08 V local minimum leaves no positive static loss allowance
even with zero transient loss; readiness stops. Source maximum above the
supported local maximum also stops: rail drop cannot be assumed to protect an
oversupply case.

The local done criterion is a checked, reviewable request with explicit absent
inputs and finite-trace coverage. Actual parent geometry, source tolerance,
return-path impedance, activity/component evidence and qualified operating
conditions remain indispensable. When supplied and reviewed, validate contact
containment/resolution, reuse the saved ODB/SPEF evaluator under applicable
conditions, check the full local voltage/timing budget and bind the result in a
new acceptance intake. A valid request or successful analysis command does not
close the [qualification tracker](qualification-followups.md).

## Recorded local request check

The September 29 checker first verified all **14 saved references** from the
surviving evidence checkout. Thirteen exact candidate/readback/activity-summary
files were then copied with their original relative paths into
`build/portable/package-power-support-01/`; the fourteenth reference is the
unchanged tracked power-study manifest. Every copied file is read-only and
hash-indexed. Validation against this recovered support produced the identical
assessment, with exactly **eight missing inputs**, `qualification: false` and
`ready_for_scoped_analysis: false`. The expected `--require-ready` exit is 2.

The standalone assessment is
`build/validation/package-power-request-02.json`, SHA-256
`a840316d0af9f8c7a80b8c128da486ad2c3f2fbff5e958ca9e25ca1c85926276`.
The support inventory SHA-256 is
`5b2a88132c0b700185f73fce2b4f7feeac5d61d64b03609e7ce3b2c30dcc3214`.
Eighteen focused controls pass normally and under optimization, including
evidence tampering, disconnected/malformed contacts, nonfinite values,
unsupported voltage budgets and absent glitch/macro-energy coverage. No
simulation, native power analysis or CAD invocation was added.
