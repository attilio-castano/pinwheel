# CMOS5L extraction model review, 2026-10-18

The process-stack uncertainty has narrowed: the merged CMOS5L ITF and the draft
five-metal TYP process describe the same metal geometry under the draft's stated
reference convention. The three draft RC rule files remain **unqualified**.
Stack arithmetic, solver-log admission, model calibration, and routed-design
signoff are separate gates. This review changes no PDK, candidate constraints,
historical evidence, or physical acceptance result.

## Frozen evidence and work performed

The source intake is
`build/streaming-tt-rc-research/upstream-itf-20261018-01/report.json`, with the
three rule files separately listed in `rules-intake.json`. The host comparison
checks all 21 selected files against their byte counts, SHA256 values and Git
blob SHA1 values, exact commit URLs, and both retained intake-producer hashes.
The downloaded generator scripts were read as data; none was imported or run.

- [PR1251](https://github.com/IHP-GmbH/IHP-Open-PDK/pull/1251) was merged on
  October 15 at commit `9182b4ff461d90948ade30b1614d5000128cb9f7`. Its three
  [ITF files](https://github.com/IHP-GmbH/IHP-Open-PDK/tree/9182b4ff461d90948ade30b1614d5000128cb9f7/ihp-sg13cmos5l/libs.tech/parasitics/itf)
  are the reference descriptions compared here. A merge establishes upstream
  provenance; it does not validate extraction tables produced by another flow.
- [PR1237](https://github.com/IHP-GmbH/IHP-Open-PDK/pull/1237), observed at commit
  `ffdafdbb4abb17316fa0ffd221ea99c0475c4734`, was open and draft in the retained
  intake. Its process descriptions, three rules, and generation code are an
  engineering candidate, with no native generation logs in this selected intake.

`scripts/streaming_tt_rc_compare.py` performs the provenance and Decimal
arithmetic comparison. Division uses 50 decimal digits; finite input decimals
and additions/multiplications in the displayed geometry are exact at that
precision. `scripts/streaming_tt_rc_solver_audit.py` is a separate, prepared pure
log-admission gate. Their 24 host tests pass under normal Python and `-O`.
Neither module invokes CAD or a field solver. Native solver grammar and behavior
have not been exercised by these tests.

The immutable comparison receipt is
`build/streaming-tt-rc-research/independent-stack-comparison-01/report.json`, SHA256
`e03deeb9a9e381390dcf7c1c8c4da1f3cbb5e80204bce1243f87d3bb29a36789`.
Its committed producer is `7f2f3e2505b6d167a3e0f9bf934f3dbdb8794b8a`, source SHA256
`07b7b871c2f6d10b5bb8be2f98945c6d3a2ea12df0f8ae0e273c9e30ac5fc0ee`.
It records producer/commit/source digests, all corner values and differences,
width support, and first RESOVER-grid inventories.
`qualified`, `physical_acceptance`, and `native_executed` are explicitly false.
The rules inventory is deliberately narrower than a complete format validator.

## TYP geometry and numerical differences

Heights are measured from the silicon surface specified by the draft process.
The lower Metal1 gap is `fox + nitride + dummyOx = 0.40 + 0.05 + 0.59 = 1.04µm`.
The dielectric above each metal includes that metal's thickness, so, for
example, the next gap is `ox1 − Metal1 = 0.96 − 0.42 = 0.54µm`. Poly, active and
trench thicknesses are not added as serial interconnect heights. This is a
comparison under that explicit interpretation, rather than an independent
measurement of the fabrication stack.

| Metal | Gap below, µm | Bottom, µm | Thickness, µm | Minimum width / spacing, µm | ITF RPSQ, Ω/□ | ITF RPSQ×thickness, Ωµm | Draft rho, Ωµm |
|---|---:|---:|---:|---:|---:|---:|---:|
| Metal1 |1.04|1.04|0.42|0.16 / 0.18|0.110|0.04620|0.0462|
| Metal2 |0.54|2.00|0.49|0.20 / 0.21|0.088|0.04312|0.0431|
| Metal3 |0.54|3.03|0.49|0.20 / 0.21|0.088|0.04312|0.0431|
| Metal4 |0.54|4.06|0.49|0.20 / 0.21|0.088|0.04312|0.0431|
| TopMetal1 |0.85|5.40|2.00|1.64 / 1.64|0.018|0.03600|0.036|

All TYP gaps, bottoms, thicknesses, minimum widths and minimum spacings agree.
Metal2–4 rho differs by `−0.00002Ωµm`, or approximately `−0.04638%`; this is
small rounding, explicitly recorded rather than accepted as exact equality.
The draft's [CMOS5L README lines 11–12](https://github.com/IHP-GmbH/IHP-Open-PDK/blob/ffdafdbb4abb17316fa0ffd221ea99c0475c4734/ihp-sg13cmos5l/libs.tech/librelane/openrcx/README.md#L11-L12)
say TopMetal1 starts around 5.16µm; summing its actual process fields gives
5.40µm. The statement is stale relative to those fields. Its 1.64µm minimum
width/spacing agrees with the merged ITF; the older ITF bundled in PR1237 still
has 1.5µm, so using that older file without an explicit revision would be unsafe.

## MIN/MAX describe a different corner construction

The merged ITF keeps metal thickness and dielectric thickness fixed across
corners, changes intermetal/dummy-oxide ER from 4.0/4.1/4.2 and top-nitride ER from 6.5/6.6/6.7,
and changes sheet/via resistances. The draft instead keeps its dielectric
epsilon at nominal values, scales gaps using claimed plate-capacitance ratios,
and applies linewidth deltas to capacitance geometry. These are different
parameterizations; matching corner labels does not prove equivalent envelopes.

| Gap | Draft MIN | TYP | Draft MAX | Draft scale ratios MIN / MAX |
|---|---:|---:|---:|---|
| Metal1 |1.241|1.04|0.8949|37/31 and37/43|
| Metal2–4 |0.68|0.54|0.4478|68/54 and68/82|
| TopMetal1 |1.07|0.85|0.7049|68/54 and68/82|

These ratios reproduce stored values with small rounding: the largest relative
gap-rounding magnitude is about 0.03461% for MIN TopMetal1. The three dielectric
pieces under Metal1 sum to 1.24128µm in MIN versus the declared 1.241µm gap, and
0.89492µm in MAX versus 0.8949µm. The report retains these differences. The
underlying plate-capacitance and linewidth table interpretations still need an
authoritative review; this comparison does not validate the process-specification
tables cited by the draft comments.

The linewidth treatment also needs a coherent electrical justification.
[solve_pattern.py lines 107–114](https://github.com/IHP-GmbH/IHP-Open-PDK/blob/ffdafdbb4abb17316fa0ffd221ea99c0475c4734/ihp-common/libs.tech/librelane/openrcx/solve_pattern.py#L107-L114)
applies `width_delta` to the capacitance solver's conductor boxes. Resistance is
generated earlier by OpenROAD and remains keyed to drawn width; the later
RESOVER expansion copies that resistance across neighbor spacings. For MIN
Metal1, solver width is `0.16 − 0.064 = 0.096µm`, while rule resistance is
`0.085/0.16 = 0.53125Ω/µm`. Applying the same resistivity to a 0.096µm wire would
instead give approximately 0.88542Ω/µm. This arithmetic does not establish the
correct sign or interpretation of the specification's linewidth delta. An
intentional empirical corner fit could use different effective parameters, but
that choice and the resulting envelope need evidence.

## Why the existing rules cannot yet establish timing closure

The following findings concern the frozen draft code, reviewed as data:

- **Failed or unconverged solver output can be accepted.**
  [solve_pattern.py lines 121–154](https://github.com/IHP-GmbH/IHP-Open-PDK/blob/ffdafdbb4abb17316fa0ffd221ea99c0475c4734/ihp-common/libs.tech/librelane/openrcx/solve_pattern.py#L121-L154)
  ignores the subprocess exit code, catches timeout and proceeds, and returns
  the last matrix associated with a Frobenius metric. It does not require that
  metric to meet requested accuracy. Successful script completion is therefore
  insufficient evidence of convergence.
- **The two matrices are not checked for identical names or dimensions.**
  [Lines 187–203](https://github.com/IHP-GmbH/IHP-Open-PDK/blob/ffdafdbb4abb17316fa0ffd221ea99c0475c4734/ihp-common/libs.tech/librelane/openrcx/solve_pattern.py#L187-L203)
  discard the second name list and difference rows/cells using `zip`, which
  silently truncates unequal sizes. Numerical finiteness and physical matrix
  properties are not acceptance gates there.
- **Incremental reuse lacks an input seal.**
  [gen_rcx_model.sh lines 139–145](https://github.com/IHP-GmbH/IHP-Open-PDK/blob/ffdafdbb4abb17316fa0ffd221ea99c0475c4734/ihp-common/libs.tech/librelane/openrcx/gen_rcx_model.sh#L139-L145)
  skips a log containing `Dimension`, without binding its process, geometry,
  solver, requested accuracy, or convergence outcome. Its default OpenROAD
  parser commit is pinned, but an existing downloaded parser or `OPENROAD_SRC`
  checkout is accepted without a content check.
- **The dielectric approximation requires error bounds.** Each box is solved
  in a single global epsilon 4.1. The nominal Metal1 gap's simple 1D series
  effective epsilon is about 4.11294, which is a useful planar sanity check, but
  says little about sidewall, fringe or mixed-layer fields. The nitride
  passivation and air boundary are absent from the uniform-medium solve.
  MIN/MAX use the same global epsilon. Two wire lengths 10/20µm remove a constant
  end term only if the residual is length independent; a third length and
  changed boundary extension are needed to measure that approximation.
- **Coverage is narrow and generation provenance is incomplete.** Each retained
  corner has only one nonempty width value per metal: 0.16/0.20/0.20/0.20/1.64µm.
  Each has 16 empty width tables; that inventory alone does not identify which
  contexts are supported by the consumer. `DIAGMODEL ON` is not a coverage
  proof. The 22 repeated resistance rows per first RESOVER grid are replicated
  coefficients, not 22 independent measurements. The selected intake includes
  no complete pattern manifest, raw solver traces or independent calibration.

The prepared host gate rejects nonzero exit, timeout, an unreaped process,
stale planned run/input/solver/runner bindings, altered logs, nonfinite values,
unexpected names or dimensions, incomplete terminal output, and terminal
reported Frobenius change above the requested threshold. It refuses to upgrade
a completed prefix after a later failed/truncated iteration. It **trusts the
runner's process facts and the solver's reported metric**; it does not
independently prove convergence. Its grammar is synthetic-test preparation,
not a drop-in native qualification result or a complete execution supervisor.

## A bounded local calibration path, conditional on tools and resources

A useful pilot can be prepared locally, with all sources isolated from the
shared PDK. It needs a frozen trusted FasterCap executable/runtime and complete
OpenROAD-helper content hashes first. No FasterCap executable has been observed
on the host command path. A later bounded, offline pinned-image inventory found
neither `FasterCap`, `fastercap`, nor `resover` on its PATH, and no matching
FasterCap package name in a completed top-level Nix-store scan. Compiler, CMake,
make and Ninja commands were also absent from PATH, although Nix package names
for clang-wrapper 21.1.8, gcc-wrapper 15.2.0 and CMake 4.1.2 were present. These are
limited availability observations, not an exhaustive filesystem search or a
claim that the packages are usable without preparation.

The OpenROAD query itself exited 0 and its startup banner reported full revision
`dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`. Its `ord::openroad_git_describe`
returned empty, so the strict inventory probe exited 1; that failed job is
preserved. Cleanup and immutable-input checks closed. The separate host
interpretation is
`build/streaming-physical-development/pinned-tool-inventory-interpretation-unqualified-01/report.json`,
SHA256 `5a89f71860532c8759c5a599dc366c7debbeea3e48d961c1595e7ef86465dc62`.
This started OpenROAD without a design; it ran no field solver, downloaded code
or installation. It supplies no RC calibration or physical acceptance.

The concrete sequence is:

1. Freeze a small case manifest before measuring: nominal and extreme corners,
   Metal1/substrate, every adjacent-metal gap, lateral minimum spacing and a
   larger spacing, TopMetal1/passivation sensitivity, and at least two drawn
   widths per selected layer. Reserve cases with widths/geometries outside the
   one-width training set as held out. A 12–24-case pilot is feasible preparation;
   it is deliberately insufficient to qualify every layout context.
2. Run a new, reviewed local wrapper in one bounded resource lease, with at
   most 4 CPUs / 6 GiB and no swap. Freeze solver and helper hashes, exact geometry,
   process/corner definitions, units, log digests, resource/exit facts and the
   complete expected-case membership. Accept no cache without these bindings.
   Require the strict log gate, then native grammar/negative-control validation.
3. Compare against an independently constructed layered-dielectric reference
   and analytic limiting cases; reusing the draft's own uniform geometry is
   not an independent calibration. A second converter with the same solver
   tests geometry translation, but not independent solver correctness. Check
   mesh/accuracy refinement, at least a third wire length, and ground-boundary
   extension. Test matrix symmetry, passivity/energy, sign conventions and
   charge conservation under the applicable reference convention.
4. Predeclare error tolerances for resistance, ground/total/coupling C and
   corner ordering before fitting. Validate held-out geometries without tuning
   against them; justify the linewidth/resistance interpretation and the corner
   envelope. Expand width, spacing, diagonal, vertical/via and power-wire
   coverage where the intended design needs it. A small pilot can reveal a bad
   approximation; passing it cannot establish the untested envelope.
5. Only then validate the exact pinned extractor consumer, complete supported
   table membership, extraction/annotation completeness and SPEF units, followed
   by all-corner routed STA. This remains separate from DRC, LVS, antenna,
   power connectivity and final TT acceptance.

There is no measured pilot runtime yet. The draft README estimates roughly 300
patterns per five-metal corner at about one minute for each pair of solver
lengths. Three corners therefore imply about 15 worker-hours, or an optimistic
3.75 wall-hours with four single-thread workers, before builds, refinements,
held-out references and retries. The 6 GiB limit may require less concurrency;
solver internal threading must also fit the 4 CPU total. With the script's 600s
limit per length, even the 24-case/two-length pilot could consume up to 8
worker-hours before rejecting timeouts; those outputs must not be reused as
successful evidence. These are estimates, not measured capacity commitments.

A strict local pilot could be worthwhile after candidate CAD if a trusted
solver is already available and the resource lease permits it. Building tools,
regenerating all three tables and independently validating the entire model
envelope within the remaining campaign is not currently a defensible promise.
The report therefore keeps model qualification open while making the specific
engineering tasks and acceptance evidence concrete.

## Headless solver build readiness

A small follow-up source intake checks the build prerequisites, without
configuring or compiling anything:
`build/streaming-tt-rc-research/fastercap-build-readiness-unqualified-01/report.json`,
SHA256 `419e75480a566605d82efa0ab1bc2737e9eddb38f0890cfe1d7079f8c2134248`.
It retains five Git-blob-checked README/CMake files from FasterCap commit
`b42179a8fdd25ab42fe45527282b4a738d7e7f87` and separately pinned LinAlgebra and
Geometry commits. No package archives or complete source trees were fetched.

The [official build instructions](https://github.com/ediloren/FasterCap/blob/b42179a8fdd25ab42fe45527282b4a738d7e7f87/README.md)
support `FASTFIELDSOLVERS_HEADLESS=ON`, but headless still needs wxWidgets base.
The [CMake file](https://github.com/ediloren/FasterCap/blob/b42179a8fdd25ab42fe45527282b4a738d7e7f87/CMakeLists.txt)
selects wx-config 3.0, adds the sibling LinAlgebra/Geometry projects, and uses
OpenMP and GNU-style compiler/linker options. The observed Nix package names
therefore do not establish a complete usable build environment, particularly
wxBase headers/libraries, a generator and OpenMP support. ARM64 compilation and
runtime compatibility have not been tested here.

There is also a concrete configure-compatibility issue: the project declares
CMake minimum 2.8, while [CMake 4.0 removed policy compatibility before 3.5](https://cmake.org/cmake/help/v4.1/release/4.0.html#deprecated-and-removed-features).
Using the observed 4.1.2 package would need an explicitly reviewed build-file
change or an external policy setting such as
[`CMAKE_POLICY_VERSION_MINIMUM`](https://cmake.org/cmake/help/v4.1/variable/CMAKE_POLICY_VERSION_MINIMUM.html).
Neither route has been tried. The next conditional step is a bounded offline
dependency inventory, followed by a separately leased build only if the
required dependencies can be frozen. The OpenROAD parser and its Python
dependencies are another check before full rule generation. The draft's
RESOVER expansion is its own `expand_resover.py`; a standalone `resover` command
is not required by that script. These findings make the setup cost explicit
and provide no new calibration or model-qualification claim.
