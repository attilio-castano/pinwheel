# Live routing observations — intermediate snapshot

Observed **2026-10-22 23:34:26.939966 UTC**, using HOST reads only. The repaired
run was active when its bytes were captured. These observations establish no
completed DetailedRouting state, clean routing, final timing, signoff, or proven
short root cause. This is a snapshot, not a campaign final report.

At matched **completed** iterations, the repaired candidate has fewer reported
violations. Counts at `Completing 100%` are not used: the subsequent native
`Number of violations` summary is authoritative for this comparison.

| Completed iteration | Original full01 | Repair02 snapshot | Change |
| --- | ---: | ---: | ---: |
| 0 | 25,755 | 18,329 | −28.83% |
| 1 | 15,900 | 11,059 | −30.45% |
| 2 | 16,802 | 10,936 | −34.91% |

These are early routing improvements. Canonical post-antenna repair inserted
four buffers in the two measured overloaded nets, legalized placement, mirrored
cells, and refreshed global routing. This comparison does not isolate buffer
insertion as the cause of the routing improvement and does not predict zero
violations at completion.

The closed original log shows a floor of 28 Metal2 short labels throughout
completed iterations 13–45, with temporary additional violations. For example,
[the iteration-45 summary](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261022-01/native-full-01/native.log:7075)
reports exactly 28, all `Short` on `Metal2`. Iteration 46 was interrupted at
60%, still reporting 28; it has no completed-iteration count. A persistent
layer/count does not prove the same coordinates or nets persisted. The original
run has no completed DRT ODB/DEF/state or final DRC coordinate file; its owned
stop and terminal receipt remain preserved separately.

The original global-route estimate had zero overflow, 36.74% overall resource
usage and 48.29% on Metal2 ([raw final congestion table](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261022-01/native-full-01/flow/33-openroad-repairdesignpostgrt/openroad-repairdesignpostgrt.log:1166)).
The DRT initialization reported `stdCellPinNoAp=0`
([raw pin-access summary](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261022-01/native-full-01/flow/37-openroad-detailedrouting/openroad-detailedrouting.log:76)).
Those observations do not demonstrate a global routing-capacity failure or a
cell with no enumerated access point. They do not exclude local pin-access,
signal-wire, via-enclosure, power-strap or guide interactions. Metal2 carries
signal routing and [PDN straps](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/physical/streaming_8x4/pdn.tcl:59).
DRC coordinates, participating nets and shape ownership are required to
distinguish these hypotheses. The available evidence does not justify assigning
the short cause to placement density.

The native LEF58-enclosure/CUTCLASS warnings show a separate limitation of the
router's rule coverage. They do not establish why these metal shorts occurred;
independent actual-GDS DRC remains required. Nominal timing, corrected fanout,
global zero overflow, detailed routing and qualified extracted timing remain
separate gates.

The [HOST snapshot receipt](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261022-01/host-routing-observation-01/snapshot.json)
records the complete parsed original and repaired iteration histories, absolute
source paths and hashes. Its SHA256 is
`5bb15da3e9bf4ff0adec3c479642238dbad43785d288283892701dc35430ea52`.
Original raw log hashes below were checked against the terminal original run's
artifact ledger before recording. The repaired row is a retained byte copy of
the active log at the observation time; it does not assert that the active
source file will retain those bytes.

| Evidence | SHA256 |
| --- | --- |
| [Closed original native log](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261022-01/native-full-01/native.log) | `d7b0bd02debebb2b45ff56ffa2000e1fc3995705eab13e267d1be391c0eba7bc` |
| [Closed original receipt](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261022-01/native-full-01/report.json) | `af1aa3b34a124631da57493b27647b09781baeaef670a1028fe099632cf41821` |
| [Original global-route log](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261022-01/native-full-01/flow/33-openroad-repairdesignpostgrt/openroad-repairdesignpostgrt.log) | `c52d8be5ddf966eea1a425aa3325068fe5da93d492bd2ed084aab4bd267b0e97` |
| [Original DRT log](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261022-01/native-full-01/flow/37-openroad-detailedrouting/openroad-detailedrouting.log) | `7ba49aac0da2a373a25be53664e6fffbf623c7c015ce03c3a780bcd20b5867bb` |
| [Retained repaired native-log snapshot, 290,086 bytes](/Users/attiliocastano/.codex/worktrees/dc52/pinwheel/build/campaigns/8x4-20261022-01/host-routing-observation-01/native-repair-02-native.log) | `35976e14e5912b165d45d38824afec5088f754ee9673b8544a099c5a40f66d9d` |
