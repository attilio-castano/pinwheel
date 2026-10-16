"""Fresh three-corner route-derived RC STA; no placement fallback or optimization."""
import hashlib,json,os,re,shutil,subprocess,time
from pathlib import Path
from librelane.common import get_script_dir
from segments import roundtrip
root=Path('/work/diagnostic');inputs=json.loads((root/'inputs.json').read_text());scripts=Path(get_script_dir())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(root/'checkpoint.odb')==inputs['routed_database_sha256']
assert sha(root/'after_grt.segments')==inputs['route_segments_sha256']
native=root/'native-scripts';script_hashes={}
for name,expected in inputs['native_script_sha256'].items():
    source=scripts/name;assert sha(source)==expected,(name,sha(source),expected)
    target=native/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target);script_hashes[name]=expected
measurements={};proofs={}
expected_ndr=inputs['post_route_ndr_map']
for entry in inputs['corners']:
    corner=entry['name'];folder=root/corner;folder.mkdir();libs=' '.join('/work/diagnostic/'+name for name in entry['libs'])
    text=('source /work/diagnostic/baseline-env.tcl\n'
          'foreach key [array names ::env _LIB_CORNER_*] {unset ::env($key)}\n'
          'foreach key [array names ::env *SPEF*] {unset ::env($key)}\n'
          'foreach key [array names ::env *SDF*] {unset ::env($key)}\n'
          'set ::env(CURRENT_ODB) /work/diagnostic/checkpoint.odb\n'
          'set ::env(_SDC_IN) /work/diagnostic/core.sdc\n'
          'set ::env(_LIB_CORNER_0) {'+corner+' '+libs+'}\n'
          'set ::env(_PNR_EXCLUDED_CELLS) {}\nset ::env(OPENROAD_THREADS) 3\n')
    env_file=folder/'corner-env.tcl';env_file.write_text(text)
    env=dict(os.environ,SCRIPTS_DIR=str(scripts),_TCL_ENV_IN=str(env_file))
    command=['openroad','-exit','-threads','3','-no_splash','-metrics',str(folder/'metrics.json'),str(root/'route-corner.tcl')]
    started=time.monotonic()
    with (folder/'native.log').open('w') as log:result=subprocess.run(command,env=env,cwd=folder,stdout=log,stderr=subprocess.STDOUT)
    assert result.returncode==0,(corner,result.returncode)
    log=(folder/'native.log').read_text()
    for marker in ('PINWHEEL_ROUTE_SEGMENTS_IMPORTED_AND_GLOBAL_RC_REQUIRED','PINWHEEL_GLOBAL_ROUTE_RC_ESTIMATED','PINWHEEL_ROUTE_TIMING_FINISHED_WITHOUT_OPTIMIZATION'):
        assert log.count(marker)==1,(corner,marker)
    assert not re.search(r'\[(?:WARNING|ERROR) GRT-[^\]]+\]',log),('Segment import warning',corner)
    assert not re.search(r'\[(?:WARNING|ERROR) EST-(?:0025|0026|0350)\]',log),('Invalid route geometry or route-to-pin RC',corner)
    imported=roundtrip(root/'after_grt.segments',folder/'imported.segments')
    assert roundtrip(root/'after_grt.segments',folder/'after-timing.segments')==imported
    ndr_files=[folder/name for name in ('ndr-before-import.txt','ndr-after-import.txt','ndr-after-timing.txt')]
    assert len({sha(p) for p in ndr_files})==1,'DBNDR assignments changed during timing'
    actual={}
    for line in ndr_files[0].read_text().splitlines():
        fields=line.split('\t');assert len(fields)==2 and fields[0] not in actual;actual[fields[0]]=fields[1] or None
    assert actual==expected_ndr,'Reloaded routed DBNDR map differs from producer snapshot'
    widths=[]
    for line in (folder/'ndr-width-equivalence.txt').read_text().splitlines():
        row=line.split();assert len(row)==4 and int(row[2])==int(row[3])>0;widths.append([*row[:2],int(row[2]),int(row[3])])
    assert len(widths)==10 and {row[0] for row in widths}=={'Metal1','Metal2','Metal3','Metal4','TopMetal1'}
    assert sha(folder/'timing-before.v')==sha(folder/'timing-after.v')==inputs['netlist_sha256'],'Timing logical netlist changed'
    spef=folder/'estimated.spef';assert spef.is_file() and spef.stat().st_size>0
    for filename,body in re.findall(r'^%OL_CREATE_REPORT ([^\n]+)\n(.*?)^%OL_END_REPORT',log,re.M|re.S):
        assert Path(filename).name==filename;(folder/filename).write_text(body)
    checks=(folder/'checks.rpt').read_text()
    unannotated=re.findall(r'Found (\d+) unannotated drivers\.',checks)
    partial=re.findall(r'Found (\d+) partially unannotated drivers\.',checks)
    assert len(unannotated)==len(partial)==1,'Native annotation report missing or ambiguous'
    metrics=json.loads((folder/'metrics.json').read_text());setup=float(metrics['timing__setup__ws__corner:'+corner]);hold=float(metrics['timing__hold__ws__corner:'+corner])
    assert corner+' Corner' in log and all('__corner:' not in k or k.endswith('__corner:'+corner) for k in metrics)
    proof=dict(segment_roundtrip=imported,exact_routes_retained_after_timing=True,DBNDR_assignments_preserved=True,DBNDR_map_matches_producer=True,NDR_width_equals_default_on_all_route_and_pin_layers=widths,
        runtime_router_NDR_fallback_serialization='Internal FastRoute fallback may be unpersisted; estimator uses routed-db assignments, and all route/pin-layer resistance width ratios are exactly one. This estimator uses default-layer capacitance and cut-layer via RC and does not model NDR spacing/coupling or detailed via choices; route geometry remains exact.',
        estimated_spef_sha256=sha(spef),annotation=dict(native_report='checks.rpt',unannotated_driver_count=int(unannotated[0]),partially_unannotated_driver_count=int(partial[0]),complete_annotation_claim=False),netlist_unchanged=True)
    proofs[corner]=proof
    measurements[corner]=dict(setup_worst_slack_ns=setup,hold_worst_slack_ns=hold,setup_met=setup>=0,hold_met=hold>=0,qualification=entry['qualification'],fresh_metrics=metrics,route_import=proof,elapsed_seconds=round(time.monotonic()-started,3),command=command)
    print(corner,'global-route setup',setup,'hold',hold,flush=True)
assert sha(root/'checkpoint.odb')==inputs['routed_database_sha256'] and sha(root/'after_grt.segments')==inputs['route_segments_sha256']
measurement=dict(status='measured',corners=measurements,native_script_sha256=script_hashes,route_import=proofs,route_based_only=True,parasitic_model='estimate_parasitics -global_routing',
    route_source_report_sha256=inputs['route_source_report_sha256'],routed_database_sha256=inputs['routed_database_sha256'],route_segments_sha256=inputs['route_segments_sha256'],
    nominal_reference=dict(same_database=None,reproduced=None,reason='Route-derived5/10 RC; no comparison or reproduction of prior placement estimates.'),
    all_three_setup_hold_met=all(v['setup_met'] and v['hold_met'] for v in measurements.values()),scope=inputs['scope'])
(root/'measurement.json').write_text(json.dumps(measurement,indent=2)+'\n')
