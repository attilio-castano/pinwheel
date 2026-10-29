# Independent RC pilot for the 8×4 campaign

Prepared October 22, 2026, before new numerical measurements. This is a new
experiment. Historical failed receipts remain failed, and a passing pilot does
not qualify the CMOS5L extraction model or a routed chip.

## Current source boundary

The official CMOS5L support branch remains pinned at
`d66cf179e7bc4d296362ab7e2e3b344dc3c4f665`; its
[tile table](https://github.com/TinyTapeout/tt-support-tools/blob/d66cf179e7bc4d296362ab7e2e3b344dc3c4f665/tech/ihp-sg13cmos5l/tile_sizes.yaml)
contains 8×4 at 1724.16×710.64 µm. The GDS action remains
`3412659307918422f3f0727917cf9b499aaca588`.

[IHP PR #1237](https://github.com/IHP-GmbH/IHP-Open-PDK/pull/1237) remains open,
draft and unmerged at `ffdafdbb4abb17316fa0ffd221ea99c0475c4734`. Current IHP
`dev` was observed at `7c783c7c56086511be93bb2097bee656a26148bd`. Its existing
RCX configuration still selects inherited seven-layer rules. The three merged
CMOS5L ITFs are process inputs, not evidence that the draft generated rules are
accurate or complete. No shared PDK or historical model is changed here.

The raw GitHub responses and exact UTF-8 source bytes are retained under the
campaign's ignored `rc-upstream-intake` owner, with request URLs and content
hashes. The live FasterCap option/solve sources match the exact archived build
sources: SHA-256 `38399e5853a686b80d988e753ee229ac5efcea41e62cc75bef5d53c4ae2745a5`
and `90ef8c9b26333683dda437e1d60009caeafeda4ec77e8db2dc0f96e5da9337f9`.

## The failure mechanism being tested

The old automatic U solve begins with mesh threshold `m=1e32`. With interaction
ratio `d=1`, this makes the initial link threshold equally coarse. Its initial
matrix warned about diagonal dominance and had a negative SIGNAL row sum.
Later iterations recovered, but the unchanged all-warnings-fatal rule rejects
the entire execution.

The old `d=3.83703e-36` follow-up repaired that coarse initial interaction
selection, but subsequent mesh refinement drove the link computation towards
a dense problem. Its third attempted iteration estimated 129,629,610 links and
1,977 MiB of link storage, while its temporary filesystem was 32 MiB. It exited
with a file error. This is evidence of that scratch-capacity failure; it is
neither an observed OOM nor a converged result.

The relevant pinned implementation computes `eps = d * m`, sets the automatic
initial `m=1e32`, and later replaces `m` from the mesh refinement measurement:
[SolveCapacitance.cpp](https://github.com/ediloren/FasterCap/blob/b42179a8fdd25ab42fe45527282b4a738d7e7f87/Solver/SolveCapacitance.cpp).
The [console options](https://github.com/ediloren/FasterCap/blob/b42179a8fdd25ab42fe45527282b4a738d7e7f87/FasterCapConsole.cpp)
permit a manual mesh, interaction ratio and GMRES tolerance.

The new intervention therefore uses **manual mesh refinement with `d=1`**,
rather than automatic iteration followed by an extremely small global ratio.
It changes the numerical experiment, not the historical verdict. Every emitted
matrix must pass the same warning and physical screens. External comparisons
between independently executed mesh levels replace the automatic stopping
metric; no single manual solve is called converged continuum electrostatics.
The new protocol also tightens GMRES tolerance from the old automatic 0.005 to
0.0005. Its result tests that combined numerical policy; it does not isolate
the mesh choice as the sole experimental cause of any improvement.

## Frozen measurement protocol

`scripts/streaming_8x4_rc_protocol.py:frozen_protocol` is the machine-readable
authority. A prepared owner records its exact hash, producer hashes, runtime
membership and generated input membership before any execution.

- First execute the unchanged historical U geometry as a **new manual-mesh
  experiment**. Do not import its old execution code or promote its old result.
- Training wire width is 0.16 µm. The 0.32 µm width is held out; it cannot tune
  flags or tolerances. Both use a 1.04 µm gap, 0.42 µm thickness and uniform
  relative permittivity 4.1.
- Execute lengths 10, 20 and 30 µm with 20 µm finite-ground margins. Additional
  20/30 µm cases use 30 µm margins to measure finite-ground sensitivity.
- Use Galerkin, GMRES tolerance 0.0005, interaction ratio 1, and the ordered mesh
  ladder 0.000383703, 0.000248446, 0.000172698, 0.000086349, 0.0000431745. The
  first three values came from the failed development U trace; the last two
  are predeclared halvings. This is explicitly development-derived policy.
- Every run must exit zero, finish within 120 seconds, retain exact names,
  dimensions, flags, units and inputs, and contain no warning/error. Require
  positive diagonal entries, nonpositive off-diagonals, nonnegative Maxwell
  row sums, at most 1% reciprocity error and a positive definite symmetric
  energy form.
- Require **two consecutive mesh comparisons** with at most 2% change in
  every matrix cell. A Frobenius norm dominated by the large ground conductor
  cannot conceal a drifting small SIGNAL entry.
- Require length-difference slopes to agree within 5%; native ground-extension
  sensitivity must be at most 2%. Missing cases are failures, not optional
  omissions.

The pilot requests one CPU, at most 6 GiB container memory including a bounded
4 GiB scratch filesystem, no extra swap, and at most 55 solver calls. Actual
runtime/resource admission and cleanup are separate campaign-owner checks.
Preparation and import never launch a solver. No Native job starts without
the campaign owner's explicit GO for its exact frozen plan and hashes.

## Independent reference and held-out checks

`scripts/streaming_8x4_rc_reference.py` independently discretizes
`div(epsilon grad V)=0` on a nonuniform two-dimensional Cartesian grid, with a
rectangular conductor at one volt and a grounded exterior. It uses
preconditioned conjugate gradients, harmonic vertical dielectric conductance
and integrated horizontal dielectric conductance. It shares no mesher,
interaction kernel, source conversion or matrix parser with FasterCap.

Its small equation controls check an exact two-unknown linear solution,
series/parallel dielectric laws, the terminal-flux/energy identity, and exact
capacitance scaling under a uniform epsilon change. The full reference is
predeclared at 0.04/0.02 µm near-wire mesh and 16/32 µm domain extents, for both
training and held-out widths. Require a recomputed relative residual at most
1e-9, a discrete maximum principle, flux/energy agreement, and at most 2%
mesh/domain changes. Compare the three-dimensional length-difference
capacitance per length with this independent reference within 10%.

These numerical checks are useful error discriminators, **not rigorous
continuum error enclosures**. Uniform epsilon does not validate the real
layered stack. Passing this pilot leaves resistance, vias, multilayer and
diagonal geometry, corner definitions, dielectric/passivation accuracy,
extractor coverage, SPEF annotation and final routed timing open.

## Initial host validation

Twelve focused controls pass under normal and optimized Python. They reject
warnings, incomplete/duplicate matrices, automatic runs, wrong flags/names,
nonfinite values, nonphysical matrices, skipped meshes, insufficient mesh
comparisons and protocol changes. The independent small equation controls
pass in the same suite. Native outcomes will be recorded separately; this
document does not assert that a new solver execution has occurred.
