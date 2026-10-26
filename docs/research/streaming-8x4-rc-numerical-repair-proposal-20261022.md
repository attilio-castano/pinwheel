# Uniform-wire numerical failures: causal repair proposal

The uniform finite-wire pilot remains false. The50-call block completed45strict passing calls, then rejected the46th actual solver call, `wire_w0p32_L30_M30` at manual mesh `0.000383703`. FasterCap exited0 but printed GMRES nonconvergence after1,000iterations; the last four selected calls were correctly not executed. The50 passing raw leaves include the earlier U5control. They do not close the full pilot.

Independent readback also finds five complete wire cases failing the unchanged requirement for two successive complete-matrix changes≤2%:

| Case | Penultimate change | Final change |
| --- | ---: | ---: |
| w.32/L10/M20 | 3.2478% | 0.4565% |
| w.32/L20/M20 | 2.0337% | 1.6899% |
| w.16/L20/M30 | 31.2488% | 0.3481% |
| w.16/L30/M30 | 26.4106% | 0.6051% |
| w.32/L20/M30 | 16.6140% | 2.7636% |

The exact development measurements are retained in `build/campaigns/8x4-20261022-01/rc-uniform-consumer-independent-readback-01/strict-mesh-diagnostics.json`. For example, w.16/L20/M30 changes from14,550to25,613panels at the31.25%jump, and w.16/L30/M30 changes from9,424to26,288panels at the26.41%jump. These are self-capacitance cells, not only near-zero matrix entries. The GMRES iterations for those refined solves are far below1,000. Repairing one iteration-cap failure therefore cannot be described as closing mesh convergence.

## Pinned causal source evidence

Five exact primary source blobs are retained under `rc-fastercap-iterative-source-intake-01`; manifest SHA256 `bc77f662bc2bf61c255194110255944c71667413f849d597a3dcb8f880577417`. They were retrieved as base64 bytes and independently checked against Git blob SHA1 at FasterCap commit `b42179a8fdd25ab42fe45527282b4a738d7e7f87`. The recovered executable was not changed or rebuilt.

- [`SolveCapacitance.h:45`](https://github.com/ediloren/FasterCap/blob/b42179a8fdd25ab42fe45527282b4a738d7e7f87/Solver/SolveCapacitance.h#L45) compiles the GMRES maximum at1,000. There is no corresponding iteration-cap CLI option in the pinned parser.
- [`SolveCapacitance.cpp:2363`](https://github.com/ediloren/FasterCap/blob/b42179a8fdd25ab42fe45527282b4a738d7e7f87/Solver/SolveCapacitance.cpp#L2363) bounds the loop by that cap; lines2504–2509log the nonconvergence error, then lines2517–2573still construct a solution and return normal. This explains the actual exit0 and why the warning/error gate must remain fatal. The printed residual/target each use only three decimal places; the displayed equal values do not establish convergence.
- [`SolverGlobal.cpp:53`](https://github.com/ediloren/FasterCap/blob/b42179a8fdd25ab42fe45527282b4a738d7e7f87/Solver/SolverGlobal.cpp#L53) defaults to Jacobi, automatic preconditioning off, and two-level dimension128. [`FasterCapConsole.cpp:208`](https://github.com/ediloren/FasterCap/blob/b42179a8fdd25ab42fe45527282b4a738d7e7f87/FasterCapConsole.cpp#L208) supports clearing preconditioners with `-pn`, then enabling two-level with `-ps128`. The explicit clearing is essential: enabling two-level alone retains the default Jacobi bit, producing a fatal mixed-preconditioner warning at SolveCapacitance.cpp122–124. Block-combination/hierarchical branches explicitly emit unsupported errors at1256–1275.
- [`SolveCapacitance.cpp:108`](https://github.com/ediloren/FasterCap/blob/b42179a8fdd25ab42fe45527282b4a738d7e7f87/Solver/SolveCapacitance.cpp#L108) sets the potential-interaction threshold to `d*m`. The previously verified Autorefine.cpp2780/2878uses the mesh threshold during panel refinement, while3138/3283uses the interaction threshold during link construction. Changing m at fixed d therefore changes both discretization and interaction approximation. A tighter d at the same m distinguishes interaction accuracy from adding panels.

## Proposed bounded development diagnostic

Before a full new pilot, freeze a separately typed four-call2×2diagnostic on the exact failed geometry and original coarse m. Factors are Jacobi versus explicit `-pn -ps128`, and d=1versus d=.25. Repeating the Jacobi/d1case is a fixed control, not a skipped failure. Retain the same geometry bytes/unit, executable, Galerkin scheme and GMRES target `.0005`; do not raise the compiled cap, loosen the target or change physical inputs. The d=.25choice tightens interaction approximation by a fixed4×, before any new measurement. The preconditioner dimension128is the source default, not fitted to results.

Every raw warning/error remains fatal. Require exact actual preconditioner, d, m and scheme markers, names, complete matrix physics, zeroexit, terminal footer, process reaping and input/runtime custody. This tests whether improved conditioning or interaction accuracy removes the observed failure. It does not establish the full wire pilot, a true-residual enclosure or model qualification. A failed branch remains a failed branch; do not pick its matrix or overwrite its receipt.

If Root admits that closed diagnostic and it finishes, a separately reviewed continuation can run the fixed five-mesh ladder on the known large-jump w.16/L20/M30development case using the predeclared two-level/d=.25policy, preserving the2%gate. The four-factorial result can explain effects; the continuation cannot qualify held-out geometry. Full uniform admission would still require a fresh, complete frozen universe, all length/boundary/reference gates, and measured resource feasibility. Further mesh extension needs its own predeclared plan; the existing five-mesh failure stays intact.

The suggested first diagnostic ceiling is four120-second leaves,1CPU/6GiB/no extra swap,512MiB scratch,540s work and600s outer guard. The two-level implementation allocates two4096²double matrices (256MiB total) regardless of the requested128active dimension, plus O(N) indices and existing Krylov storage; retain the hard6GiB ceiling. No worker implementation, numerical execution or Root admission is claimed by this proposal. A new typed worker/parser contract and exact command must be reviewed and frozen before GO. The frozen uniform, M1, all-layer, consumer and runtime files remain unchanged.
