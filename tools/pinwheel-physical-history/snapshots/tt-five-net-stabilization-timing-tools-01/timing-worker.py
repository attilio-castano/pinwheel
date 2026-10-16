"""Fresh three-corner route-derived RC STA; no placement fallback or optimization."""
import hashlib,json,os,re,shutil,subprocess,time
from pathlib import Path
from librelane.common import get_script_dir
from segments import roundtrip

root=Path(os.environ['PINWHEEL_TIMING_ROOT']);inputs=json.loads((root/'inputs.json').read_text());scripts=Path(get_script_dir())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def sha_text(text):return hashlib.sha256(text.encode()).hexdigest()
assert sha(root/'checkpoint.odb')==inputs['routed_database_sha256']
assert sha(root/'after_grt.segments')==inputs['route_segments_sha256']
native=root/'native-scripts';script_hashes={}
for name,expected in inputs['native_script_sha256'].items():
    source=scripts/name;assert sha(source)==expected,(name,sha(source),expected)
    target=native/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target);script_hashes[name]=expected
measurements={};proofs={}
assert {entry['name'] for entry in inputs['corners']} == {'nom_typ_1p20V_25C','nom_slow_1p08V_125C','nom_fast_1p32V_m40C'} and len(inputs['corners'])==3
expected_ndr=inputs['post_route_ndr_map']
for entry in inputs['corners']:
    corner=entry['name'];folder=root/corner;folder.mkdir();libs=' '.join('__PINWHEEL_STAGE__/'+name for name in entry['libs'])
    text=('source __PINWHEEL_STAGE__/baseline-env.tcl\n'
          'foreach key [array names ::env _LIB_CORNER_*] {unset ::env($key)}\n'
          'foreach key [array names ::env *SPEF*] {unset ::env($key)}\n'
          'foreach key [array names ::env *SDF*] {unset ::env($key)}\n'
          'set ::env(CURRENT_ODB) __PINWHEEL_STAGE__/checkpoint.odb\n'
          'set ::env(_SDC_IN) __PINWHEEL_STAGE__/core.sdc\n'
          'set ::env(_LIB_CORNER_0) {'+corner+' '+libs+'}\n'
          'set ::env(_PNR_EXCLUDED_CELLS) {}\nset ::env(OPENROAD_THREADS) 3\n')
    text=text.replace('__PINWHEEL_STAGE__',str(root))
    env_file=folder/'corner-env.tcl';env_file.write_text(text)
    env=dict(os.environ,SCRIPTS_DIR=str(scripts),_TCL_ENV_IN=str(env_file),PINWHEEL_TIMING_ROOT=str(root))
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
    sections=re.findall(r'(?ms)^NONDEFAULTRULES\s+\d+\s*;.*?^END NONDEFAULTRULES', (folder/'timing-input.def').read_text())
    assert len(sections)==1 and sha_text(sections[0])==inputs['canonical_block_NDR_DEF_sha256'],'Canonical blockNDR definitions changed during timing load'
    assert not re.search(r'\+\s+(?:VIA|USEVIA|USEVIARULE)\b',sections[0]),'Unexpected NDR via list'
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
    headroom={}
    for endpoint in inputs['endpoints']:
        inst=endpoint.split('/')[0];row={}
        for kind,label in [('max','setup'),('min','hold')]:
            report_path=folder/('endpoint-'+inst+'-'+kind+'.rpt');body=report_path.read_text()
            assert body.count('Startpoint:')==body.count('Endpoint:')==1,(corner,endpoint,kind,'Missing/ambiguous path')
            assert re.search(r'Endpoint: '+re.escape(inst)+r'\b',body),(corner,endpoint,kind,'Wrong endpoint')
            data=body.split('data arrival time')[0];pins=re.findall(r'[\^v] (\S+) \(',data)
            assert pins[-1]==endpoint and 'timing_eco_hold_30712/A' in pins,(corner,endpoint,'Terminal delay path absent')
            values=re.findall(r'(-?\d+\.\d+)\s+slack \((VIOLATED|MET)\)',body);assert len(values)==1
            row[label+'_slack_ns']=float(values[0][0]);row[label+'_report']=report_path.name;row[label+'_startpoint']=re.search(r'Startpoint: (.*)',body)[1]
        headroom[endpoint]=row

    terminal_headroom={}
    for endpoint in inputs['terminal_endpoints']:
        inst=endpoint.split('/')[0]; contexts={}
        for edge in ['rise','fall']:
            for kind in ['max','min']:
                report=folder/('terminal-'+inst+'-'+edge+'-'+kind+'.rpt');body=report.read_text()
                assert body.count('Startpoint:')==body.count('Endpoint:')==1,(corner,endpoint,edge,kind,'No unique worst context')
                pins=re.findall(r'[\^v]\s+(\S+)\s+\(',body.split('data arrival time')[0]);assert pins[-1]==endpoint
                matches=re.findall(r'(-?\d+\.\d+)\s+slack \((VIOLATED|MET)\)',body);assert len(matches)==1
                contexts[edge+'/'+kind]=dict(slack_ns=float(matches[0][0]),report=report.name,startpoint=re.search(r'Startpoint: (.*)',body)[1])
        terminal_headroom[endpoint]=dict(contexts=contexts,minimum_setup_ns=min(v['slack_ns'] for k,v in contexts.items() if k.endswith('/max')),minimum_hold_ns=min(v['slack_ns'] for k,v in contexts.items() if k.endswith('/min')))
    reproduced=None
    if inputs['reproduction_required']:
        reference=inputs['retained_reference_corners'][corner]
        assert abs(setup-reference['setup_worst_slack_ns'])<=.001 and abs(hold-reference['hold_worst_slack_ns'])<=.001,(corner,'Priorqualified route timing didnot reproduce')
        for endpoint, actual_headroom in headroom.items():
            for metric in ['setup_slack_ns','hold_slack_ns']:
                assert abs(actual_headroom[metric]-reference['endpoint_headroom'][endpoint][metric])<=.001, (corner,endpoint,metric,'Fresh control targeted timing did not reproduce')
        assert set(terminal_headroom)==set(reference['terminal_headroom']), (corner,'Five terminal endpoint scope differs')
        for endpoint,row in terminal_headroom.items():
            assert set(row['contexts'])==set(reference['terminal_headroom'][endpoint]['contexts'])
            for context,value in row['contexts'].items():
                assert abs(value['slack_ns']-reference['terminal_headroom'][endpoint]['contexts'][context]['slack_ns'])<=.001,(corner,endpoint,context,'Fresh five terminal control exceeds1ps')
        for metric_name,value in metrics.items():
            if 'violation__count__corner:' in metric_name or 'vio__count__corner:' in metric_name:
                assert value==reference['fresh_metrics'][metric_name], (corner,metric_name,'Fresh control electrical/count reproduction failed')
        assert proof['annotation']==reference['route_import']['annotation'], (corner,'Fresh control annotation differs')
        spef_lines=spef.read_text().splitlines(keepends=True);assert len([line for line in spef_lines if line.startswith('*DATE ')])==1
        normalized_spef=sha_text(''.join(line for line in spef_lines if not line.startswith('*DATE ')))
        assert normalized_spef==inputs['retained_control_normalized_spef_sha256'][corner], (corner,'Fresh control fullSPEF differs exceptDATE')
        proof['fresh_control_electrical_annotation_and_full_SPEF_reproduced']=True
        proof['normalized_SPEF_sha256']=normalized_spef
        reproduced=True
    contexts={}; native_ledger={}; reach={driver:{trace:set() for trace in ['all','timing']} for driver in ['fanout914','fanout913']}
    for line in (folder/'resetpair-coverage.tsv').read_text().splitlines():
        fields=line.split('\t')
        if fields[0]=='API':continue
        if fields[0]=='REACH':reach[fields[1]][fields[2]].add(fields[3])
        elif fields[0]=='PATH':native_ledger.setdefault('/'.join(fields[1:4]),{})[fields[4]]=float(fields[6])
        else:raise AssertionError(('Unexpected or empty affected context',fields))
    for driver in ['fanout914','fanout913']:
        assert reach[driver]['all']==reach[driver]['timing'] and len(reach[driver]['all'])==257
        for edge in ['rise','fall']:
            for kind in ['max','min']:
                key=driver+'/'+edge+'/'+kind;rows={}
                text=(folder/('resetpair-'+driver+'-'+edge+'-'+kind+'.rpt')).read_text()
                for body in re.findall(r'(?ms)^Startpoint: .*?(?=^Startpoint:|\Z)',text):
                    data=body.split('data arrival time')[0];pins=re.findall(r'[\^v]\s+(\S+)\s+\(',data);assert pins
                    endpoint=pins[-1];assert endpoint not in rows
                    values=re.findall(r'(-?\d+\.\d+)\s+slack',body);assert len(values)==1;rows[endpoint]=float(values[0])
                assert set(rows)==reach[driver]['all']==set(native_ledger[key])
                assert all(abs(value-native_ledger[key][endpoint])<=1e-5 for endpoint,value in rows.items())
                contexts[key]=rows
                if True:
                    expected=inputs['affected_reference'][corner][key];assert set(rows)==set(expected)
                    if inputs['reproduction_required']:assert all(abs(value-expected[endpoint])<=.001 for endpoint,value in rows.items()),(corner,key,'Affected control exceeds1ps')
    global_failures={'max':{},'min':{}}
    for line in (folder/'global-violations.tsv').read_text().splitlines():
        kind,endpoint,startpoint,slack=line.split('\t');assert kind in global_failures and endpoint not in global_failures[kind] and float(slack)<0
        global_failures[kind][endpoint]=dict(startpoint=startpoint,slack_ns=float(slack))
    global_counts={kind:int(re.search(r'PINWHEEL_GLOBAL_FAILURE_COUNT '+kind+r' (\d+)',log)[1]) for kind in global_failures}
    assert all(global_counts[kind]==len(rows) for kind,rows in global_failures.items())
    affected_worst={}
    for key,rows in contexts.items():
        if key.endswith('/max'):
            for endpoint,value in rows.items():affected_worst[endpoint]=min(affected_worst.get(endpoint,value),value)
    ref_worst={}
    for key,rows in inputs['affected_reference'][corner].items():
        if key.endswith('/max'):
            for endpoint,value in rows.items():ref_worst[endpoint]=min(ref_worst.get(endpoint,value),value)
    formerly_negative={endpoint:dict(reference_setup_ns=value,current_setup_ns=affected_worst[endpoint],delta_ns=affected_worst[endpoint]-value,current_met=affected_worst[endpoint]>=0) for endpoint,value in ref_worst.items() if value<0}
    if inputs['reproduction_required']:
        expected_setup_count=inputs['retained_reference_corners'][corner]['fresh_metrics']['timing__setup_vio__count__corner:'+corner]
        assert global_counts==reference['global_failure_counts']
        assert global_counts==reference['global_failure_counts']
        for kind in ['max','min']:
            assert set(global_failures[kind])==set(reference['global_failure_endpoints'][kind])
            for endpoint,row in global_failures[kind].items():
                assert abs(row['slack_ns']-reference['global_failure_endpoints'][kind][endpoint]['slack_ns'])<=.001
    reference=inputs['retained_reference_corners'][corner]
    reference_comparison=dict(reference_only=True,prior_original_reproduction_required=False,
        reference_setup_worst_slack_ns=reference['setup_worst_slack_ns'],reference_hold_worst_slack_ns=reference['hold_worst_slack_ns'],
        setup_delta_ns=setup-reference['setup_worst_slack_ns'],hold_delta_ns=hold-reference['hold_worst_slack_ns'],
        affected_contexts={key:dict(endpoint_count=len(rows),worst_slack_ns=min(rows.values()),
            reference_worst_slack_ns=min(inputs['affected_reference'][corner][key].values()),
            minimum_endpoint_delta_ns=min(value-inputs['affected_reference'][corner][key][endpoint] for endpoint,value in rows.items()),
            maximum_endpoint_delta_ns=max(value-inputs['affected_reference'][corner][key][endpoint] for endpoint,value in rows.items())) for key,rows in contexts.items()},
        electrical_violation_counts={key:dict(actual=value,reference=reference['fresh_metrics'][key],delta=value-reference['fresh_metrics'][key])
            for key,value in metrics.items() if ('violation__count__corner:' in key or 'vio__count__corner:' in key) and key in reference['fresh_metrics']})
    pair_coverage={'coverage_complete':True,'context_count':8,'endpoint_count_per_context':257,'contexts':contexts,'minimum_affected_setup_ns':min(value for key,rows in contexts.items() if key.endswith('/max') for value in rows.values()),'minimum_affected_hold_ns':min(value for key,rows in contexts.items() if key.endswith('/min') for value in rows.values())};
    measurements[corner]=dict(global_failure_counts=global_counts,global_failure_endpoints=global_failures,formerly_negative_affected_setup_endpoints=formerly_negative,prior_qualified_reference_comparison=reference_comparison,pair_headroom=pair_coverage,setup_worst_slack_ns=setup,hold_worst_slack_ns=hold,setup_met=setup>=0,hold_met=hold>=0,qualification=entry['qualification'],fresh_metrics=metrics,route_import=proof,endpoint_headroom=headroom,terminal_headroom=terminal_headroom,prior_qualified_global_timing_reproduced=reproduced,elapsed_seconds=round(time.monotonic()-started,3),command=command)
    print(corner,'global-route setup',setup,'hold',hold,flush=True)
assert sha(root/'checkpoint.odb')==inputs['routed_database_sha256'] and sha(root/'after_grt.segments')==inputs['route_segments_sha256']
measurement=dict(status='measured',corners=measurements,native_script_sha256=script_hashes,route_import=proofs,route_based_only=True,parasitic_model='estimate_parasitics -global_routing',
    route_source_report_sha256=inputs['route_source_report_sha256'],routed_database_sha256=inputs['routed_database_sha256'],route_segments_sha256=inputs['route_segments_sha256'],
    nominal_reference=dict(same_database=None,reproduced=None,reason='Fresh saved-global-route RC; reference reproduction is recorded separately and never uses placement estimates.'),
    all_three_setup_hold_met=all(v['setup_met'] and v['hold_met'] for v in measurements.values()),scope=inputs['scope'])
(root/'measurement.json').write_text(json.dumps(measurement,indent=2)+'\n')
