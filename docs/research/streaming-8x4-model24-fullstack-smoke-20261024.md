# Model24 observed full-stack cost smoke

This is a fixed two-call development experiment, prepared after the actual
310-pattern TYP OpenROAD census. Root alone admits and executes Native. It cannot
qualify mesh, length, ground extension, independent accuracy, a generated model,
heldouts, or timing.

The closed pattern census contains 45 `1v2` and 265 `3v2` files. The new native
parser checks every record, path family, target voltage, rectangle, width,
spacing, length, ground role and material. All 310 files normalize against the
retained full TYP ITF. Some Over/OverUnder patterns use a local vertical origin:
the adapter derives one exact offset from every conductor and ground plane,
then checks all printed dielectric intervals against the global ITF partition.
This observation does not substantiate an alleged TopMetal1 stack mismatch.
A `wire_` prefix alone is also not a demonstrated old-parser classification bug.

Two UnderDiag3 M4/TopMetal1 cases are selected before any numerical measurement:

- `3v2/MODEL24_TYP/UnderDiag3/M4duM5/W0.2_W1.64/S0.21_S0_L10/wires`
- `3v2/MODEL24_TYP/UnderDiag3/M4duM5/W0.2_W1.64/S0.42_S6.56_L10/wires`

Both reach the observed inventory maxima of six conductors, 65 initial faces
and 29 dielectric faces. They bracket near and far upper-metal contexts; those
HOST counts do not prove a universal runtime upper bound. Each finite geometry
uses 20 um wire length and 20 um ground extension, retains every native ground
and wire, and includes every actual TYP material interface. Zero-voltage neighbor
wires remain independent conductors in the complete six-row Maxwell matrix.
The internal CSG ground-anchor rename is bijective and adds no substrate or
conductor. Geometry certificates and physical SI to S20 witnesses are bound.

The fixed call uses the retained FasterCap binary/runtime, explicit in-core
`-f0`, Galerkin, Jacobi, `-m0.000383703 -t0.0005 -d0.25`. Every warning, convergence
failure, matrix/name/role/physics or unit failure remains fatal, including a
printed last matrix with exit zero. The hard limits are one CPU, 6 GiB RAM with
no extra swap, 512 MiB tmpfs, 256 MiB polled owned outputs, 120 seconds per leaf,
270 seconds actual work and 330 seconds outer supervision. A resource/custody
failure stops the suffix. Both closed numerical failures may be retained as
measurements; no successful prefix is a complete smoke pass.

The independent reader reopens raw logs, exact full matrices, copied inputs,
all source and runtime bytes, observed cgroups/counter deltas, actual elapsed
work, Root GO, wrapper/guard/shared lease and terminal cleanup. The original
closed pattern source/resource receipt is reopened again. No downloaded Python
or generator source is imported or executed by preparation or readback.

Preparation01 remains preserved, unexecuted and superseded. Preparation02 binds
the actual underscore-key cgroup schema and the explicit output-size guard.
The seven portable HOST controls pass normally and under `python3 -O`.

The current frozen packet is:

- Plan `build/campaigns/8x4-20261024-01/model24-fullstack-smoke-preparation-02/plan.json`, SHA256 `dbbea83d261877367eca371b24ef6bae14034528c78d7b1f48df199dafe9b887`.
- Proposal `model24-smoke-command-proposal-02.json`, SHA256 `d5b9d0b18abc6b73dd854f056c8228613c5d1437024077bf97cc7b60236ed367`.
- Launcher `model24-smoke-launch-reopen-02.json`, SHA256 `f11bb3e6df36e4c1de8bbe2edff6ae070c5e4ece4c75581346aa4d97e14082a4`.

All 34 producer dependencies are sealed. The first pattern packet and its 30
sources remain unchanged. Root must create the exact bound GO file and use the
launcher command; the HOST closeout command is eligible only after actual
terminal cleanup and Root's signal.

## Executed outcome

Root executed the exact packet and closed resource cleanup. Both solver processes
returned zero and completed, in 8.000612 and 7.555965 seconds. The complete packet
took 16.396802883 seconds; observed cgroup peak was 222,990,336 bytes, without OOM
or resource/custody failure. Both fail the unchanged 1% full-matrix reciprocity
gate. Completion and low cost are therefore measured; numeric smoke success is
false.

All 15 unordered matrix pairs for each geometry are retained in
`model24-smoke-raw-observations-01.json`, SHA256
`9345faa756c8ced053f612e39e582399bde6b2e9a67dfd30e5d87b11689cb3be`.
That diagnostic independently reopens the exact frozen raw/resource reader and
preserves its failed verdict. It does not symmetrize or promote the printed
matrices.

| Geometry | Refined panels | Links | Pairs failing 1% | Maximum reciprocal disagreement |
| --- | ---: | ---: | ---: | ---: |
| Near upper context | 12,874 | 9,002,854 | 3 of 15 | 4.898726% |
| Far upper context | 12,891 | 8,893,145 | 4 of 15 | 5.240293% |

The weakest far couplings have large relative disagreement despite small
absolute discrepancies. However, substrate-ground to selected-M4 reciprocity
also fails by 4.8987% near and 2.0660% far. This is not solely a negligible far
coupling issue. The pinned solver separately sets interaction approximation
`m_dEps = m_dEpsRatio * m_dMeshEps` and applies GMRES's implicit relative residual
stopping condition. A separate predeclared residual-versus-interaction
experiment is proposed; neither error source is established from these two
failed matrices alone.

A HOST replay of all 310 observed patterns confirms maxima of six conductors,
65 initial faces and 29 dielectric faces; target counts are M1=70, M2=78,
M3=74, M4=58, TopMetal1=30. A complete three-corner, three-length, five-mesh,
two-extension deck would contain 27,900 solves. At the observed coarsest average
alone that projects about 60 hours, before finer-mesh cost, independent
references or consumer checks. Even the 210 M2–M4 target patterns imply 18,900
calls. These are illustrative cost projections, not a proved runtime bound or
an admitted reduced model. An actual final-route census must define the
applicable envelope before calibration; successful subsets cannot define it.
