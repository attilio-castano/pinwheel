# Two exact in-core resource diagnostics

This is a new HOST-prepared packet, not a replacement receipt for either failed
full pilot. Root alone may admit it. The unchanged full M1 run retained three
strict numerical passes and then an exit-74 file allocation failure; the uniform
run retained four strict passes and then the same failure. Neither completed a
full universe or established a limited pilot pass.

The source-backed cause is storage mode. FasterCap's default `-f5` selected
out-of-core storage for approximately 2,287 MiB / 1,895 MiB of interaction links,
while `/tmp` was capped at 512 MiB. The pinned console parser explicitly supports
`-f0` to disable that mode. In `Autorefine.cpp` 519–540 the decision compares link
memory times the ratio with `wxGetFreeMemory`; the reported VM free memory is not
the container's 6 GiB limit. Lines 573–579 print a fallback message on insufficient
disk space but then set the out-of-core flag true. That explains why the logs'
“trying to continue in-core” text did not mean a successful fallback occurred.

Only these two calls are admitted by the proposed packet:

| Original failed point | Preserved numerical policy | Sole argument addition |
| --- | --- | --- |
| M1 `TYP-w.16-self-L10-E20`, mesh .000086349 | Jacobi, d.25, Galerkin, GMRES .0005 | `-f0` |
| Uniform `historical_U_new_manual`, mesh .0000431745 | Two-level128, d.25, Galerkin, GMRES .0005 | `-f0` |

Exact original geometry, runtime, full-policy plans, failed leaves, parent reports
and resource receipts are retained. Both points keep their original S20 unit.
No tolerance, preconditioner, geometry, memory limit, scratch limit or mesh changes.
The actual native `(-f)` header must equal zero exactly once; the original matrix
parser alone does not establish this. All original warning, convergence, matrix,
physics and terminal-footer gates remain mandatory.

The source allocates 16 bytes per link on arm64, rounded to 1,048,576-link chunks.
A conservative planning estimate includes the complete rounded link storage,
the old failed allocation total including its already allocated link buffers
(deliberate double counting), two worst 1,001-vector Krylov arrays, work vectors,
Hessenberg storage, the actual maximum 4096² SUPER matrix capacity, and another
512 MiB reserve. Totals are 5,179,799,696 and 5,152,309,056 bytes, below the unchanged
95% boundary of 6,120,328,396 bytes. These are planning estimates, not proven bounds
on every allocation or evidence that a finer full-universe point will fit.

Each call remains limited to 120 seconds, one CPU, 6 GiB, no extra swap and 512 MiB
scratch. Work/outer limits are 270/330 seconds. The worker polls actual cgroup
memory at most every .25 seconds and preempts its owned child at 95%; Root's outer
guard remains unchanged. Actual `memory.current`, cumulative `memory.peak`,
`memory.events`, `memory.events.local`, memory limit and swap limit are captured
before and after each leaf. Missing max/OOM counters reject. Counter deltas and
child exit signal distinguish observed OOM from timeout, guard termination or an
unexplained SIGKILL. Peaks are not reset or claimed to be isolated leaf peaks.
Resource feasibility rejects max/OOM events or a cumulative peak at the guard.

Measurement completion, resource feasibility and numerical acceptance have separate
fields. A closed numerical failure may advance the fixed second point; resource,
guard, OOM or custody failure stops the suffix. The independent HOST reopener checks
raw logs, mode, counters, source/input/runtime seals and exact outer cleanup.
Every model, full-pilot and qualified-timing flag stays false. A full rerun requires
another explicit reviewed policy after these measurements.

Relative to `build/campaigns/8x4-20261022-01/`, preparation02 plan SHA256 is
`53393b5c1e68ee4ad3c619dc4622dbb27ca2f3bfbe298dd57565eb1222fb53b6`;
`rc-incore-command-proposal-02.json` is
`ac8dbd09ae5450f9e285fd944a887bbf634862814993b3c7cf9d692c5e17c589`.
`rc-incore-launch-reopen-02.json` contains the exact guard and HOST readback argv,
SHA256 `5d5c134a35b08caf075155a2e0212fe0402458aaf73e5e8fd3a57d04bc9f0795`.
Preparation01 is retained unexecuted and superseded after independent review
required explicit max-counter membership and polled-current/kernel-peak joins.
Seven focused HOST controls pass normally and with Python `-O`. No Native
executable ran during preparation or these tests.

## Actual two-leaf closeout

Root subsequently executed the exact preparation02 packet. Both points passed
their original numerical gates and the new resource/mode gates. M1 took
32.58837564 seconds and U took 22.019938302 seconds. Both actual native headers
reported `-f0`. The cumulative container kernel peak was 2,523,590,656 bytes;
the maximum polled currents were 2,523,066,368 and 2,123,907,072 bytes. The second
leaf's identical kernel peak is the retained cumulative peak, not a claim that
the second leaf independently reached that memory usage.

Every max/OOM counter delta was zero in both `memory.events` and
`memory.events.local`. No child timed out or hit the memory guard. The exact
outer resource receipt completed with exit zero, unchanged inputs and empty
owned process/container cleanup. Frozen independent HOST readback rederived
all source, original-failure, runtime, command, cgroup and numerical joins.

The retained `rc-incore-independent-readback-01.json` SHA256 is
`72d75a4624fb8fb357d9fa96fd3d2bf5a6f560afb6cbc9b5a764babdc0d6713a`;
the actual outer resource receipt SHA256 is
`80ed9b0d475abd0f1420701e671bcc130bbe4dc2a2d8b2090c3729737109e2fb`.
Measurement completion, resource feasibility and point numerical acceptance are
all true. These results establish the two tested leaves only. Finer M1 leaves
and the complete fresh universes remain unmeasured under an in-core policy;
model, full-pilot and qualified-timing fields remain false.
