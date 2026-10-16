"""Freeze exact one-gate placement study; host-only, no CAD."""
import ast,json
from pathlib import Path
from common import ROOT,sha,read,write
H=Path(__file__).resolve().parent;assert not(H/"prepared.json").exists()
S=ROOT/"physical/experiments/tt-buffered-hold30712-selection-01.json";selection=read(S);assert selection["schema"]=="pinwheel-buffered-tt-hold30712-selection-v1";assert sha(S)=="452d91c56f500c1e5a14f46ce4107dc740e543ad798750107b5c478e780efcad"
source=read(H/"plan.json");assert sha(H/"plan.json")==selection["qualified_control"]["exact_plan_sha256"]
qualified=read(H/"qualified-control-source.json");paths=dict(selection["protected_sources_sha256"]);paths.update(qualified["artifacts_sha256"]);paths[str(S)]=sha(S);paths[str(ROOT/source["source_database"])]=source["source_database_sha256"]
prior=ROOT/"build/physical/tt-buffered-timing-eco-control-route-01"
for p in [*[f for f in prior.iterdir() if f.name in ("baseline-env.tcl","corner-env.tcl","core.sdc","before.v","report.json")],*[f for f in (prior/"lib").glob("*.lib")]]:paths[str(p)]=sha(p)
verification_path=ROOT/"build/physical/tt-buffered-incremental-eco-fix-verification-02/report.json";verification=read(verification_path);assert verification["status"]=="passed" and verification["inputs_unchanged"] and verification["container_termination"]["status"]=="absent"
paths[str(verification_path)]=sha(verification_path)
for n,h in verification["artifact_sha256"].items():paths[str(verification_path.parent/n)]=h
G=ROOT/"build/physical/tt-buffered-hold30712-preflight-01/headroom-gate.json";gate=read(G);assert gate["schema"]=="pinwheel-buffered-tt-hold30712-preflight-gate-v1" and gate["status"]=="passed" and gate["admitted_to_move"] is True
P=ROOT/gate["report"];r=read(P);assert sha(P)==gate["report_sha256"] and r["status"]=="passed" and r["exit_code"]==0 and r["inputs_unchanged"] and r["container_termination"]["status"]=="absent"
assert gate["qualified_candidate_database_sha256"]==qualified["control_database_sha256"] and gate["worst_target_setup_ns"]>=1 and gate["worst_target_hold_ns"]>=.05
paths[str(G)]=sha(G);paths[str(P)]=sha(P);paths.update(r["input_sha256"])
for n,h in r["artifact_sha256"].items():paths[str(P.parent/n)]=h
for n,h in paths.items():assert sha(Path(n) if Path(n).is_absolute() else ROOT/n)==h,n
script_hashes=read(ROOT/"build/physical/tt-buffered-incremental-eco-tools-09/native-script-hashes.json");write(H/"native-script-hashes.json",script_hashes)
for p in H.rglob("*.py"):ast.parse(p.read_text())
tools={str(p.relative_to(ROOT)):sha(p) for p in sorted(H.rglob("*")) if p.is_file()}
write(H/"prepared.json",{"schema":"pinwheel-buffered-tt-hold30712-prepared-v1","status":"prepared_not_launched","source_sha256":paths,"tool_sha256":tools,"source_database":source["source_database"],"source_database_sha256":source["source_database_sha256"],"exact_plan_sha256":sha(H/"plan.json"),"qualified_control_database_sha256":qualified["control_database_sha256"],"headroom_gate":{"path":str(G.relative_to(ROOT)),"sha256":sha(G)},"executable_verification":{"path":str(verification_path.relative_to(ROOT)),"sha256":sha(verification_path)},"selection_sha256":sha(S),"native_work_seconds_at_most":240,"all_in_cap_seconds":290,"cpus":4,"memory":"3g","network":"none","native_stop_utc":"2026-10-13T18:49:46Z","deadline_utc":"2026-10-13T18:52:46Z","only_moved_instance":"timing_eco_hold_30712","allowed_move_signal_nets":["_03216_","timing_eco_hold_30712_D"],"boundary":"OriginalR0 warm10route, samequalified2+8ECO reproducedexactly, passed3corner headroom inputsbound, genuinelydirty current-control noop, onegateplacement/twonetlocalroute only. No GPL/DPL/CTS/repair/fullreroutefallback."})
print(json.dumps({"prepared_sha256":sha(H/"prepared.json"),"live_sha256":sha(H/"live.py"),"driver_sha256":sha(H/"driver.py"),"tool_files":len(tools),"source_inputs":len(paths)},indent=2))
