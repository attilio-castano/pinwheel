"""Fresh standalone no-edit control then electrical counterfactual; no physical IO."""
import hashlib,json,os,re,subprocess,time
from pathlib import Path
ROOT=Path('/work/diagnostic')
read=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
plan=read(ROOT/'inputs.json')
clock_pins=set(plan['clock_pins'])

def parse_paths(text,kind):
    paths={};clock_values={};loads={}
    for block in re.findall(r'(?ms)^Startpoint: .*?(?=^Startpoint:|\Z)',text):
        data=block.split('data arrival time')[0];pins=re.findall(r'[\^v]\s+(\S+)\s+\(',data);assert pins
        endpoint=pins[-1];assert endpoint not in paths
        values=re.findall(r'(-?\d+\.\d+)\s+slack \((?:MET|VIOLATED)\)',block);assert len(values)==1
        paths[endpoint]=float(values[0])
        role='launch'
        for line in block.splitlines():
            if 'data arrival time' in line:role='capture'
            match=re.match(r'^\s*(?:(\d+)\s+(\d+\.\d+)\s+)?(\d+\.\d+)\s+(-?\d+\.\d+)\s+(-?\d+\.\d+)\s+([\^v])\s+(\S+)\s+\(',line)
            if not match:continue
            pin=match[7]
            if pin in clock_pins:
                # Clock roles differ by launch cycle/capture cycle. Normalize
                # absolute arrivals modulo20ns before comparing fixed clock RC.
                arrival=float(match[5])%20;key=pin+'/'+match[6]+'/'+kind+'/'+role
                clock_values.setdefault(key,[]).append([arrival,float(match[3])])
            if pin in ['_17772_/Y','fanout914/X','fanout913/X'] and match[2]:
                loads.setdefault(pin+'/'+match[6],[]).append([float(match[2]),float(match[3])])
    return paths,clock_values,loads

def run(scenario,entry):
    corner=entry['name'];folder=ROOT/scenario/corner;folder.mkdir(parents=True)
    env=dict(os.environ,PINWHEEL_CORNER=corner,PINWHEEL_LIBRARIES=' '.join(str(ROOT/name) for name in entry['libs']),PINWHEEL_NETLIST=str(ROOT/(scenario+'.v')),PINWHEEL_SDC=str(ROOT/'core.sdc'),PINWHEEL_SPEF=str(ROOT/entry['spef']))
    command=[plan['sta_binary'],'-no_init','-exit',str(ROOT/'scenario.tcl')];started=time.monotonic()
    with (folder/'native.log').open('w') as output:result=subprocess.run(command,env=env,cwd=folder,stdout=output,stderr=subprocess.STDOUT)
    assert result.returncode==0,(scenario,corner,result.returncode)
    text=(folder/'native.log').read_text();assert text.count('PINWHEEL_COMPLETE_FIXED_WIRE_TIMING_SCENARIO')==1
    assert not re.search(r'(?im)^(?:Error:|.*(?:SPEF.*(?:warning|error)|(?:warning|error).*SPEF))',text),('Native parse/timing error',scenario,corner)
    for filename,body in re.findall(r'^%OL_CREATE_REPORT ([^\n]+)\n(.*?)^%OL_END_REPORT',text,re.M|re.S):
        assert Path(filename).name==filename;(folder/filename).write_text(body)
    expected_master='sg13cmos5l_buf_1' if scenario=='control' else 'sg13cmos5l_buf_4'
    for instance in ['fanout914','fanout913']:assert 'PINWHEEL_MASTER '+instance+' '+expected_master in text
    checks=(folder/'checks.rpt').read_text();annotation=re.findall(r'Found (\d+) unannotated drivers\.',checks);partial=re.findall(r'Found (\d+) partially unannotated drivers\.',checks)
    assert annotation==['167'] and partial==['0'],('Parasitic coverage differs from source',scenario,corner,annotation,partial)
    contexts={};clocks={};loads={}
    for driver in ['fanout914','fanout913']:
        for edge in ['rise','fall']:
            for kind in ['max','min']:
                name='resetpair-'+driver+'-'+edge+'-'+kind+'.rpt';paths,cvalues,lvalues=parse_paths((folder/name).read_text(),kind);assert len(paths)==257
                contexts[driver+'/'+edge+'/'+kind]=paths
                for key,values in cvalues.items():clocks.setdefault(key,set()).update(tuple(value) for value in values)
                for key,values in lvalues.items():loads.setdefault(key,set()).update(tuple(value) for value in values)
    structural={driver:{trace:set() for trace in ['all','timing']} for driver in ['fanout914','fanout913']};native_paths={}
    for line in (folder/'coverage.tsv').read_text().splitlines():
        fields=line.split('\t')
        if fields[0]=='REACH':structural[fields[1]][fields[2]].add(fields[3])
        elif fields[0]=='PATH':
            key='/'.join(fields[1:4]);native_paths.setdefault(key,{})[fields[4]]=float(fields[6])
        else:raise AssertionError('Unknownnativecoverage')
    for driver,trace in structural.items():
        assert trace['all']==trace['timing'] and len(trace['all'])==257
        assert all(set(contexts[driver+'/'+edge+'/'+kind])==trace['all'] for edge in ['rise','fall'] for kind in ['max','min'])
    for key,paths in contexts.items():
        assert set(paths)==set(native_paths[key]);assert all(abs(value-native_paths[key][endpoint])<=1e-5 for endpoint,value in paths.items())
    global_setup=float(re.search(r'PINWHEEL_GLOBAL_SETUP (\S+)',text)[1]);global_hold=float(re.search(r'PINWHEEL_GLOBAL_HOLD (\S+)',text)[1])
    sections=re.split(r'(?m)^max (slew|fanout|capacitance)\s*$',checks);violators={}
    for index in range(1,len(sections),2):violators[sections[index]]=re.findall(r'^(\S+).*?\(VIOLATED\)$',sections[index+1],re.M)
    result=dict(native_endpoint_ledger_report_identity=True,structural_all_timing_coverage_exact=True,electrical_violator_identities=violators,status='measured',global_setup_ns=global_setup,global_hold_ns=global_hold,contexts=contexts,clock_waveforms={key:sorted(values) for key,values in clocks.items()},observed_driver_load_slew={key:sorted(values) for key,values in loads.items()},annotation=dict(unannotated=167,partial=0),elapsed_seconds=round(time.monotonic()-started,3),command=command)
    (folder/'measurement.json').write_text(json.dumps(result,indent=2)+'\n');return result

results={'control':{},'virtual':{}};control_errors=[]
for entry in plan['corners']:
    corner=entry['name'];measured=run('control',entry);reference=plan['references'][corner]
    errors=[abs(measured['global_setup_ns']-reference['global_setup_ns']),abs(measured['global_hold_ns']-reference['global_hold_ns'])]
    for key,paths in measured['contexts'].items():
        expected=reference['contexts'][key];assert set(paths)==set(expected)
        errors.extend(abs(value-expected[endpoint]) for endpoint,value in paths.items())
    for key,values in reference['clock_waveforms'].items():
        assert key in measured['clock_waveforms'];actual=measured['clock_waveforms'][key]
        assert len(actual)==len(values),(corner,key,'Clock waveform multiplicity differs')
        errors.extend(abs(left-right) for pair_a,pair_b in zip(actual,values) for left,right in zip(pair_a,pair_b))
    maximum=max(errors);control_errors.append(maximum);measured['maximum_reference_error_ns']=maximum
    results['control'][corner]=measured
    # Allthree controls are collected before deciding model-transfer admission.
    print('CONTROL',corner,'maximum_reference_error_ns',maximum,flush=True)
(ROOT/'control-validation.json').write_text(json.dumps(dict(status='passed' if max(control_errors)<=.001 else 'failed',results=results['control'],maximum_control_error_ns=max(control_errors),native_process_count=3),indent=2)+'\n')
assert max(control_errors)<=.001,('FixedSPEF model failed1ps reproduction',max(control_errors))
for entry in plan['corners']:
    corner=entry['name'];measured=run('virtual',entry);control=results['control'][corner]
    assert set(measured['contexts'])==set(control['contexts'])
    for key,paths in measured['contexts'].items():assert set(paths)==set(control['contexts'][key])
    shared=set(measured['clock_waveforms'])&set(control['clock_waveforms']);assert shared
    clock_errors=[]
    for key in shared:
        for value in measured['clock_waveforms'][key]:
            nearest=min(max(abs(left-right) for left,right in zip(value,old)) for old in control['clock_waveforms'][key]);clock_errors.append(nearest)
    assert max(clock_errors)<=.001,(corner,'Sharedclockwaveform drift',max(clock_errors))
    measured['clock_sample_changes']=dict(added=sorted(set(measured['clock_waveforms'])-set(control['clock_waveforms'])),removed=sorted(set(control['clock_waveforms'])-set(measured['clock_waveforms'])),shared_samples_checked=len(shared),maximum_shared_clock_error_ns=max(clock_errors),structural_clock_inputs_unchanged=True)

    for key,expected_deltas in plan['pin_cap_deltas'][corner].items():
        assert key in measured['observed_driver_load_slew'] and key in control['observed_driver_load_slew'],(corner,'Driverload observation missing',key)
        old_caps=sorted({value[0] for value in control['observed_driver_load_slew'][key]});new_caps=sorted({value[0] for value in measured['observed_driver_load_slew'][key]})
        assert len(old_caps)==len(new_caps)
        assert all(min(abs((new-old)-expected_delta) for expected_delta in expected_deltas.values())<=.000002 for old,new in zip(old_caps,new_caps)),(corner,key,'Native Libertycap change not observed',old_caps,new_caps,expected_deltas)
        measured.setdefault('observed_load_delta_proof',{})[key]=dict(old_caps_pf=old_caps,new_caps_pf=new_caps,observed_deltas_pf=[new-old for old,new in zip(old_caps,new_caps)],allowed_scalar_edge_minmax_Liberty_deltas_pf=expected_deltas)
    measured['native_new_inputcap_load_update_confirmed']=True
    results['virtual'][corner]=measured;print('VIRTUAL',corner,'minimumhold',min(value for key,paths in measured['contexts'].items() if key.endswith('/min') for value in paths.values()),flush=True)
minimum_hold=min(value for corner in results['virtual'].values() for key,paths in corner['contexts'].items() if key.endswith('/min') for value in paths.values())
measurement=dict(status='measured',results=results,native_process_count=6,maximum_control_error_ns=max(control_errors),minimum_virtual_affected_hold_ns=minimum_hold,conservative_local_hold_reserve_ns=minimum_hold-.001,assessment_local_hold_at_least50ps=minimum_hold-.001>=.05,scope='Electrical fixedwire model only: exact unchanged SPEF and clocks, two virtual Liberty master substitutions; no physicalODB/placement/routes resized. Full native loading/slew/endpointconstraints propagated; finalphysicaltrial wouldneed independentgeometry/routing/STA.')
(ROOT/'measurement.json').write_text(json.dumps(measurement,indent=2)+'\n')
