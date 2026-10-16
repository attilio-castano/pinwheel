"""Host-only mandatory headroom/coverage diagnostic. No CAD or mutation."""
import hashlib,json,re,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
CASE=ROOT/'build/physical/tt-buffered-holdreset-pair-preflight-01'
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path):return json.loads(Path(path).read_text())

def main():
    started=time.monotonic();report=read(CASE/'report.json')
    assert report['status']=='passed' and report['exit_code']==0 and report['inputs_unchanged']
    assert report['container_termination']['status']=='absent' and not report['container_termination']['owned_container_ids']
    assert report['measurement']['native_process_count']==3
    bindings={**report['input_sha256'],**{str(CASE/name):digest for name,digest in report['artifact_sha256'].items()},str(CASE/'report.json'):sha(CASE/'report.json'),str(Path(__file__).resolve()):sha(Path(__file__))}
    for name,digest in bindings.items():assert sha(name)==digest,('Changed source',name)
    corners={};all_holds=[];all_setup=[];complete=True
    for corner,measurement in report['measurement']['corners'].items():
        folder=CASE/'preflight'/corner;reach={driver:{trace:set() for trace in ['all','timing']} for driver in ['fanout914','fanout913']}
        ledger={(driver,edge,kind):{} for driver in reach for edge in ['rise','fall'] for kind in ['max','min']};api=None
        for line in (folder/'resetpair-coverage.tsv').read_text().splitlines():
            fields=line.split('\t')
            if fields[0]=='API':assert len(fields)==2;api=fields[1]
            elif fields[0]=='REACH':assert len(fields)==4;reach[fields[1]][fields[2]].add(fields[3])
            elif fields[0]=='PATH':
                assert len(fields)==7;key=tuple(fields[1:4]);assert fields[4] not in ledger[key]
                ledger[key][fields[4]]={'startpoint':fields[5],'slack_ns':float(fields[6])}
            else:assert fields[0]=='EMPTY' and len(fields)==4
        contexts={};async_clock=set()
        for key,paths in ledger.items():
            driver,edge,kind=key;path=folder/('resetpair-'+driver+'-'+edge+'-'+kind+'.rpt')
            body=path.read_text();actual={}
            for match in re.finditer(r'(?ms)^Startpoint: .*?(?=^Startpoint:|\Z)',body):
                block=match.group();data=block.split('data arrival time')[0]
                pins=re.findall(r'[\^v]\s+(\S+)\s+\(',data);assert pins
                endpoint=pins[-1];assert endpoint in paths and endpoint not in actual
                assert driver+'/X' in pins
                if driver=='fanout913':assert 'fanout914/X' in pins and pins.index('fanout914/X')<pins.index('fanout913/X')
                slack=float(re.findall(r'(-?\d+\.\d+)\s+slack \((?:MET|VIOLATED)\)',block)[-1]);assert abs(slack-paths[endpoint]['slack_ns'])<=1e-5
                startpoint=re.search(r'^Startpoint: (\S+)',block,re.M)[1];native_start=paths[endpoint]['startpoint'];assert startpoint==(native_start.rsplit('/',1)[0] if '/' in native_start else native_start);assert '/' not in native_start or native_start in pins
                actual[endpoint]={**paths[endpoint],'report':str(path.relative_to(CASE)),'report_line':body[:match.start()].count('\n')+1,'serial914_before913_proven':driver!='fanout913' or pins.index('fanout914/X')<pins.index('fanout913/X')}
                if re.search(r'/(?:CLK|A_CLK|RESET_B|SET_B|GATE)$',endpoint):async_clock.add(endpoint)
            assert set(actual)==set(paths),('Native ledger/full report differ',corner,key)
            assert actual,('No constrained paths',corner,key)
            worst_endpoint=min(actual,key=lambda endpoint:actual[endpoint]['slack_ns']);worst=actual[worst_endpoint]
            contexts['/'.join(key)]={'endpoint_count':len(actual),'worst_endpoint':worst_endpoint,'worst_path':worst,'all_endpoints':actual}
            (all_holds if kind=='min' else all_setup).extend(row['slack_ns'] for row in actual.values())
        coverage=[]
        for driver,traces in reach.items():
            covered={kind:set().union(*(set(ledger[(driver,edge,kind)]) for edge in ['rise','fall'])) for kind in ['max','min']}
            missing=sorted(traces['all']-(covered['max']&covered['min']))
            complete=complete and bool(traces['all']) and not missing
            coverage.append({'driver':driver,'structural_all_endpoints':sorted(traces['all']),'timing_enabled_endpoints':sorted(traces['timing']),'structural_all_count':len(traces['all']),'timing_enabled_count':len(traces['timing']),'disabled_or_constant_only_endpoints':sorted(traces['all']-traces['timing']),'uncovered_unknown_endpoints':missing})
        complete=complete and not async_clock
        corners[corner]={'native_fanout_command':api,'global_setup_ns':measurement['setup_worst_slack_ns'],'global_hold_ns':measurement['hold_worst_slack_ns'],'coverage':coverage,'contexts':contexts,'async_or_clock_endpoints_requiring_further_guard':sorted(async_clock),'global_reference_reproduced':measurement['prior_qualified_global_timing_reproduced']}
    assert len(corners)==3
    minimum_hold=min(all_holds);minimum_setup=min(all_setup);hold_ok=minimum_hold>=1.05;setup_ok=minimum_setup>=0
    result={'schema':'pinwheel-buffered-tt-holdreset-pair-host-diagnostic-v1','status':'passed','no_CAD_launched':True,'source_sha256':bindings,'all_sources_and_artifacts_current':True,'corners':corners,'all_context_native_ledger_report_identity':True,'all_corner_coverage_complete':complete,'minimum_through_hold_ns':minimum_hold,'minimum_through_setup_ns':minimum_setup,'hold_guard_before_ns':1.05,'hold_speedup_loading_allowance_ns':1,'required_residual_hold_ns':.05,'mandatory_hold_guard_passed':hold_ok,'mandatory_setup_guard_passed':setup_ok,'NLDM_assessment':'Not performed after mandatory measured hold guard rejection; frozen02 model is preserved and no model-based safety claim is made.','admitted_to_resize':False,'physical_trial_run':False,'physical_window_closed':True,'elapsed_seconds':round(time.monotonic()-started,3),'scope':'All3 fresh corners and separate914/913 rise/fall contexts with complete native endpoint/report identity; holdguard rejection is independent of closedphysicalwindow. No resize or postcandidate measurement occurred.'}
    assert not hold_ok,'Safe mandatoryheadroom would require reviewedNLDM analysis before any possible admission'
    output=ROOT/'build/physical/tt-buffered-holdreset-pair-diagnostic-01';output.mkdir()
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n')
    gate={'schema':'pinwheel-buffered-tt-holdreset-pair-headroom-gate-v1','status':'failed','admitted_to_resize':False,'source_database_sha256':'8c3079c61f73f0f2819d4e0d21d0af2775d4afb76c620494e2841ace4b1dd063','all_corner_coverage_complete':complete,'minimum_through_hold_ns':minimum_hold,'minimum_through_setup_ns':minimum_setup,'hold_loss_allowance_ns':1,'minimum_conservative_residual_hold_ns':minimum_hold-1,'mandatory_hold_guard_passed':hold_ok,'mandatory_setup_guard_passed':setup_ok,'NLDM_loss_bound_within_allowance':None,'NLDM_not_run_due_to_mandatory_guard_failure':True,'preflight_report_sha256':sha(CASE/'report.json'),'host_diagnostic_report_sha256':sha(output/'report.json'),'physical_window_closed':True,'physical_candidate_count':0,'exact_target_pins':['fanout914/X','fanout913/X']}
    (CASE/'gate.json').write_text(json.dumps(gate,indent=2)+'\n')
    print(output/'report.json',sha(output/'report.json'),'minimumhold',minimum_hold,'minimumsetup',minimum_setup,'elapsed',result['elapsed_seconds'])

if __name__=='__main__':main()
