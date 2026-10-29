# One fixed 600-second finest-M1 OOC point

Proposal only. Root has requested review before implementation or Native
admission. This is a separately typed, one-call development experiment after
the original OOC packet timed out. It preserves that failed packet, the failed
full150 M1 policy, and the failed uniform55/extra-point policies unchanged.

The useful question is whether the exact finest real-stack M1 point can finish
within 600 seconds under the already observed memory/storage policy. The
original solve reached its 120-second limit without a final matrix. It had no
cgroup max/OOM events, a 2,216,009,728-byte cumulative memory peak and
8,521,777,152-byte maximum allocated scratch. These observations justify a
bounded runtime study; they do not establish that disk I/O alone caused the
timeout or that five times the time will finish the solve.

## Fixed experiment

One fresh solve uses the exact original `TYP-w.16-self-L10-E20` geometry:
35 input files, full nominal TYP dielectric stack, S20 coordinate unit
`2^-20 m`, 10um wire and 20um ground extension. It retains the exact 215-entry
FasterCap runtime inventory and source commit
`b42179a8fdd25ab42fe45527282b4a738d7e7f87`.

The complete solver argv remains:

```
/solver/runtime/bin/FasterCap -b geometry.lst -g -m0.0000431745 -t0.0005 -d0.25 -f5
```

Galerkin, Jacobi, mesh, interaction ratio, GMRES tolerance, geometry, material
and parser/math gates are unchanged. No bulk-I/O patch, runtime rebuild,
preconditioner change, count retry, mesh change, fallback or later attempt is
included. The new execution clock is 600s for this sole solve, 630s measured
worker work including custody/cleanup, and 690s outer supervision. A new typed
worker, plan, scratch owner, command proposal, launcher and independent reader
would identify this policy; no frozen producer receives a timeout override.

The container retains one CPU, 6GiB RAM, memory-swap equal to 6GiB (zero
additional swap), 128 PIDs, offline/read-only rootfs and 512MiB tmpfs. Scratch
is a fresh owned disk bind with the same 16GiB polled logical/allocated-byte
threshold and 12GiB running free-disk reserve. These are polled limits, not a
hard filesystem quota. The same .25s polling stops at 95% of the memory limit,
the scratch threshold, the disk reserve or 600s, whichever occurs first.
All process-group reaping, exact owned-file cleanup and outer shared lease
checks remain mandatory. File cache remains charged to the cgroup.

## Reuse of the authenticated count, not a completed solve

There is no new count invocation. The new plan binds and independently reopens
the original closed packet and its exact expected97 count branch:

| Original artifact under `build/campaigns/8x4-20261022-01/` | SHA-256 |
|---|---|
| `rc-ooc-preparation-03/plan.json` | `c31469a9a8bfcdf3bad0fced51d74eb8cd4d1bd39fdaf725244febedf29cd314` |
| `rc-ooc-independent-readback-01.json` | `18070daf9090a528ff8373ccfb7d5f60d6ca39ca1045a7169ca209774b6f968f` |
| `rc-native-outputs/rc-ooc-single-finest-01/count97/report.json` | `4604c284022099ac8120c07225b44433ec335d8d06647b1250697dbfd01c5e7f` |
| `rc-native-outputs/rc-ooc-single-finest-01/count97/native.log` | `7c4ee1ae8d50555aa6e799fb896c657a87fdb4e2159130159daa5a0b5c64654b` |
| Original outer resource report | `bad0c210cbf41fba6b7d4d2d24fcd9c61dbbcd634c6efb7cc1d1bed95e3d9014` |

The original independent reader must still reconstruct its failed outcome;
the separately admitted count requires exact expected97/header/error grammar,
94,544 panels, 600,919,256 links, empty count scratch, reaped process, strict
cgroup/resource seals and unchanged geometry/runtime. Its original solve
remains timed out, exit -9, with no accepted matrix. The count is historical
resource evidence, explicitly not a fresh numerical observation.

The new Native admission retains actual `/proc/meminfo` before execution and
requires its `MemTotal` to equal the authenticated original 8,214,323,200 bytes.
It recomputes the existing source-based projection across every possible
nonzero whole-VM chunk count, rather than reusing an `admitted:true` flag.
Use the larger of the historical count peak and the new admission cgroup peak
as the observed baseline term. With the historical 91,643,904-byte baseline,
the exact existing projection is:

| Quantity | Bytes |
|---|---:|
| Maximum link buffer across 1–97 chunks | 1,627,389,952 |
| Two worst 1,001-vector arrays | 1,514,216,704 |
| 24 work vectors | 18,152,448 |
| Hessenberg reserve | 8,016,000 |
| Additional untracked reserve | 536,870,912 |
| Planning RAM including baseline | 3,796,289,920 |
| Maximum padded scratch | 11,156,848,640 |

The recomputed RAM total must remain strictly below 95% of 6GiB, padded scratch
strictly below 16GiB, and the exact count must force OOC throughout the admitted
VM-free-memory range. Host admission needs at least 28GiB free disk and the
unchanged memory floors. The projection is a conservative source-based planning
gate, not a proof of malloc/RSS bounds. Unexpected MemTotal, larger baseline,
unknown counters, changed source/runtime/geometry, insufficient budget or disk
admission blocks the sole call without selecting another configuration.

## Completion and interpretation

Before the sole launch, the 630s worker must have at least the full 600s leaf
budget plus its declared closeout reserve remaining. The deadline includes
process reaping and scratch custody; exceeding either the leaf or worker
budget is a failed resource observation. The outer 690s guard owns final
cleanup and the exact shared heavy lock/cleanup sentinel.

The new reader independently rejoins the exact plan/proposal/outer argv,
current source/runtime/input hashes, scratch owner, cgroup limits and deltas,
raw terminal log and file membership. A numerical point pass requires exit0,
strict f5/mesh/Galerkin/Jacobi/tolerance/interaction headers, the actual owned
OOC path, exact terminal counts 94,544/600,919,256, both scratch file families,
and every unchanged warning/GMRES/finite full-matrix/sign/reciprocity/ground
gate from the original M1 parser. Header/counts from a killed buffered log
cannot become a successful observation. Resource success separately requires
no max/OOM events, no memory/scratch/disk/deadline stop, confirmed reaping,
empty exact owned stage scratch and successful outer cleanup/input seals.

Retain separate fields for historical count custody, new measurement completion,
new resource feasibility and new numerical point success. Even a successful
point leaves full150, finite-BEM qualification, all-layer qualification, full
RC model qualification, continuum enclosure and qualified timing false.
Any empirical comparison to older mesh points is explicitly diagnostic until
a separately declared complete-universe authority is approved. No previous
timeout or mesh failure is converted to a pass.

The source-backed scratch/memory mechanism and original measured terminal
outcome are documented in
`docs/research/streaming-8x4-rc-ooc-finest-20261023.md`; its frozen executable
helpers are `scripts/streaming_8x4_rc_ooc.py` and its independent reader.
Implementation would reuse their pure count/projection/parser/custody logic
under new authority, with focused controls for wrong historical count, changed
MemTotal, over-budget/guarded execution, missing final counts, incomplete
cleanup and preservation of the old failed outcome. No Native or generator
was run to prepare this proposal.
