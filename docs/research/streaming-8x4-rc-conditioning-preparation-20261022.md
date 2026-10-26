# Two new bounded conditioning experiments

Both packets are HOST prepared and unexecuted. Root alone may admit their exact
commands through the shared resource guard. They retain the failed original
measurements and cannot qualify an RC model, extracted timing, or a full pilot.

The new `streaming_8x4_rc_conditioning{,_parser,_readback}.py` family has two fixed
profiles, with no branch, case or tolerance override:

| Profile | Unchanged physical input | Fixed solver calls | Work / outer limit |
| --- | --- | --- | --- |
| Layered M1 conditioning | Native06 S20 `TYP-w.16-s.18-L10-E20`, first mesh `0.000383703`, 2^-20 m coordinate unit | Jacobi d1 control, then Jacobi d.25 | 270 / 330 s |
| Uniform development mesh continuation | Original `wire_w0p16_L20_M30`, 1e-6 m coordinate unit | Two-level128 (`-pn -ps128`), d.25, all five original meshes | 660 / 720 s |

The M1 profile changes only the interaction ratio of the second call. The original
coarse solve exited zero but printed two diagonal-dominance warnings; its printed
wire row sums are -1.595e-12 and -1.053e-12 raw. Those remain failures. The uniform
profile honors the already declared two-level/d.25 development policy in the
[numerical repair proposal](streaming-8x4-rc-numerical-repair-proposal-20261022.md).
The earlier factorial's two passing d.25 points establish neither mesh stability
nor permission to select a favorable preconditioner after observing this ladder.

Every call keeps Galerkin, GMRES target 0.0005, the exact pinned executable/image,
all geometry/material bytes, one CPU, 6 GiB without additional swap, 512 MiB
scratch, 128 PIDs and a 120-second leaf limit. The parser preserves the unchanged
native warning, complete name/matrix, positive diagonal, nonpositive off-diagonal,
nonnegative Maxwell row-sum, 1% matrix reciprocity, positive symmetric energy and
complete-footer gates. The independent FVM's stricter reciprocity/residual gates
remain separate and unchanged. The uniform ladder still requires its final two
complete matrix changes to be at most 2%; no mesh extension or threshold change
is admitted here.

Printed matrices, row sums, panel/link counts and GMRES traces are retained as raw
observations even when a fatal warning rejects numerical acceptance. A failed
branch can advance only after the actual process group is reaped and exact input,
producer and runtime seals reopen. Measurement packet completion, all-branch
numeric acceptance and five-mesh stability have distinct fields. The independent
HOST reopener reparses every raw log and joins the exact Docker command, source
and plan seals, actual cgroups, terminal exit and empty resource cleanup receipt.
No historical failed receipt is converted into a pass.

Paths below are relative to `build/campaigns/8x4-20261022-01/`:

| Packet | Plan SHA256 | Command proposal SHA256 |
| --- | --- | --- |
| `rc-m1-conditioning-preparation-02/plan.json` | `27c4c124a54b6b6f0bb0c941e73086af0fc79a1448045bf23c563dbc31179417` | `rc-m1-conditioning-command-proposal-01.json`: `29816d568b10eabffb7f7561df069b40e6aaf7e3585667adbcb01320e10d2d9a` |
| `rc-uniform-d025-five-mesh-preparation-02/plan.json` | `2cf4060218b5859cee44249b30a80989a72716808308b35a39f7ffdd7f771a89` | `rc-uniform-d025-five-mesh-command-proposal-01.json`: `c99c8a55bd436d47c6d98653a9dd8dd17eb7f52075ea58e29451cc42c0868f46` |

The first M1 preparation and partial uniform preparation are retained unexecuted.
A strict HOST baseline comparison exposed the original uniform receipt's explicit
`matrix_F` field; preparation02 rederives it with the exact original unit before
comparing the complete numeric payload. This changes only the new adapter's
baseline readback. Nine focused HOST controls pass normally and under Python
`-O`; no Native solver was run by these preparation or test commands.

Even a complete successful packet remains one development geometry. The full
layered case universe, length and finite-boundary comparisons, independent
references, held-out checks, upper-layer/via coverage and qualified final timing
remain open. All model and full-pilot qualification fields stay false.
