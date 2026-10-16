"""Bounded standalone fixed-wire electrical assessment, never physical sizing."""
import argparse,hashlib,json,re,shutil,time
from pathlib import Path
from common import ROOT,read,sha,write,execute
TOOLS=Path(__file__).resolve().parent
SOURCE=ROOT/'build/physical/tt-buffered-pair-stabilization-route-01'
REFERENCE=ROOT/'build/physical/tt-buffered-pair-stabilization-headroom-01'

def parse_reference(text,clock_pins,kind):
    paths={};clocks={}
    for block in re.findall(r'(?ms)^Startpoint: .*?(?=^Startpoint:|\Z)',text):
        data=block.split('data arrival time')[0];pins=re.findall(r'[\^v]\s+(\S+)\s+\(',data);assert pins
        endpoint=pins[-1];assert endpoint not in paths
        slack=re.findall(r'(-?\d+\.\d+)\s+slack \((?:MET|VIOLATED)\)',block);assert len(slack)==1;paths[endpoint]=float(slack[0])
        role='launch'
        for line in block.splitlines():
            if 'data arrival time' in line:role='capture'
            match=re.match(r'^\s*(?:(\d+)\s+(\d+\.\d+)\s+)?(\d+\.\d+)\s+(-?\d+\.\d+)\s+(-?\d+\.\d+)\s+([\^v])\s+(\S+)\s+\(',line)
            if match and match[7] in clock_pins:clocks.setdefault(match[7]+'/'+match[6]+'/'+kind+'/'+role,set()).add((round(float(match[5])%20,6),round(float(match[3]),6)))
    return paths,clocks

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--selection',type=Path,required=True);parser.add_argument('--selection-sha256',required=True);parser.add_argument('--corrected-export-report',type=Path,required=True);parser.add_argument('--corrected-export-sha256',required=True)
    cli=parser.parse_args();started=time.monotonic();selection=cli.selection.resolve();assert selection.is_relative_to(ROOT)
    assert sha(selection)==cli.selection_sha256;selected=read(selection)
    stop=__import__('datetime').datetime.fromisoformat(selected['native_stop_utc'].replace('Z','+00:00')).timestamp();deadline=__import__('datetime').datetime.fromisoformat(selected['deadline_utc'].replace('Z','+00:00')).timestamp()
    assert time.time()+220<=stop and deadline-stop>=120
    export_path=cli.corrected_export_report.resolve();assert export_path.is_relative_to(ROOT) and sha(export_path)==cli.corrected_export_sha256
    exported=read(export_path)
    assert exported['status']=='passed' and exported['source_database_sha256']=='1304b736e051f2143b1449e76ad25bc1b9dfd2996afcc4bcf9294416b1ebe078'
    assert exported['source_segments_sha256']=='f66af983f7de67bf266964eb7b67c02a71c6cfc517c64dc8afc0e7cd5f6917a5'
    assert all(exported['invariants'][name] is True for name in ['native_pin_node_wire_caps_exact','all_D_NET_totals_conserved','all_non_CAP_sections_unchanged','original_SPEFs_unchanged'])
    assert set(exported['corrected_spef_by_corner'])=={'nom_typ_1p20V_25C','nom_slow_1p08V_125C','nom_fast_1p32V_m40C'}
    prepared=read(TOOLS/'prepared.json');source_report=read(SOURCE/'report.json');reference_report=read(REFERENCE/'report.json')
    assert source_report['status']=='failed' and source_report['exit_code']==1 and source_report['inputs_unchanged'] and reference_report['status']=='passed' and reference_report['exit_code']==0 and reference_report['inputs_unchanged']
    assert reference_report['diagnostic_only'] is True and reference_report['source_producer_status']=='failed' and reference_report['producer_report_sha256']==sha(SOURCE/'report.json')
    assert reference_report['stable_database_sha256']==sha(SOURCE/'pass2/routed.odb') and reference_report['stable_segments_sha256']==sha(SOURCE/'pass2/after_grt.segments')
    assert sha(SOURCE/'pass2/routed.odb')=='1304b736e051f2143b1449e76ad25bc1b9dfd2996afcc4bcf9294416b1ebe078'
    paths={}
    def bind(path,digest=None):
        path=Path(path).resolve();digest=digest or sha(path);assert paths.get(str(path),digest)==digest;paths[str(path)]=digest
    for document,folder in [(source_report,SOURCE),(reference_report,REFERENCE)]:
        for path,digest in document['input_sha256'].items():bind(path,digest)
        for path,digest in document['artifact_sha256'].items():bind(folder/path,digest)
        bind(folder/'report.json')
    for path,digest in prepared['source_sha256'].items():bind(path,digest)
    for path,digest in prepared['tool_sha256'].items():bind(TOOLS/path,digest)
    bind(TOOLS/'prepared.json');bind(selection);bind(export_path,cli.corrected_export_sha256)
    for path,digest in exported['input_sha256'].items():bind(ROOT/path,digest)
    for path,digest in exported['artifact_sha256'].items():bind(export_path.parent/path,digest)
    for path,digest in selected['source_bindings_sha256'].items():bind(ROOT/path,digest)
    for path,digest in selected['protected_sources_sha256'].items():bind(ROOT/path,digest)
    assert len(selected['protected_sources_sha256'])==507
    for path,digest in paths.items():assert sha(path)==digest,('Changed source',path)
    out=ROOT/'build/physical/tt-buffered-stable-pair4-fixedrc-01';out.mkdir()
    def copy(source,name):
        target=out/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target);bind(source);bind(target);assert sha(source)==sha(target)
    for name in ['worker.py','scenario.tcl']:copy(TOOLS/name,name)
    copy(SOURCE/'pass2/after.v','control.v');copy(REFERENCE/'stable/core.sdc','core.sdc')
    original=(out/'control.v').read_text();virtual=original
    for instance in ['fanout914','fanout913']:
        pattern=r'\bsg13cmos5l_buf_1(\s+'+instance+r'\s*\()'
        virtual,count=re.subn(pattern,r'sg13cmos5l_buf_4\1',virtual);assert count==1
    assert virtual.replace('sg13cmos5l_buf_4 fanout914','sg13cmos5l_buf_1 fanout914').replace('sg13cmos5l_buf_4 fanout913','sg13cmos5l_buf_1 fanout913')==original
    (out/'virtual.v').write_text(virtual);bind(out/'virtual.v')
    inventory=read(SOURCE/'pass2/native-inventory.json')
    assert all(inventory['nets'][net]['sig_type']=='SIGNAL' for net in ['_11039_','net914','net913'])
    assert all(not any(row[0] in ['fanout914','fanout913'] for row in net['terminals']) for net in inventory['nets'].values() if net['sig_type']=='CLOCK')
    clock_pins={'clk'}
    for net in inventory['nets'].values():
        if net['sig_type']=='CLOCK':clock_pins.update(instance+'/'+pin for instance,pin,direction in net['terminals'] if direction=='INPUT')
    base_inputs=read(REFERENCE/'stable/inputs.json');corners=[];references={};cap_deltas={}
    for entry in base_inputs['corners']:
        corner=entry['name'];references[corner]=dict(global_setup_ns=reference_report['measurement']['corners'][corner]['setup_worst_slack_ns'],global_hold_ns=reference_report['measurement']['corners'][corner]['hold_worst_slack_ns'],contexts={},clock_waveforms={})
        clocks={}
        for driver in ['fanout914','fanout913']:
            for edge in ['rise','fall']:
                for kind in ['max','min']:
                    filename='resetpair-'+driver+'-'+edge+'-'+kind+'.rpt';values,cvalues=parse_reference((REFERENCE/'stable'/corner/filename).read_text(),clock_pins,kind);assert len(values)==257
                    references[corner]['contexts'][driver+'/'+edge+'/'+kind]=values
                    for key,pairs in cvalues.items():clocks.setdefault(key,set()).update(pairs)
        references[corner]['clock_waveforms']={key:sorted(values) for key,values in clocks.items()}
        libs=[]
        for name in entry['libs']:
            target='lib/'+Path(name).name;copy(REFERENCE/'stable'/name,target);libs.append(target)
        spef='spef/'+corner+'.spef';corrected=exported['corrected_spef_by_corner'][corner];spef_source=(ROOT/corrected['path']).resolve();assert spef_source.is_relative_to(ROOT) and sha(spef_source)==corrected['sha256'];copy(spef_source,spef)
        assert '*DESIGN_FLOW "NAME_SCOPE LOCAL" "PIN_CAP NONE"' in (out/spef).read_text()[:600]
        corners.append(dict(name=corner,libs=libs,spef=spef,qualification=entry['qualification']))
        standard=(out/libs[0]).read_text()
        def group_at(text,start):
            position=text.index('{',start);depth=1;end=position+1
            while depth:depth+=(text[end]=='{')-(text[end]=='}');end+=1
            return text[start:end]
        cap_models={}
        for master in ['sg13cmos5l_buf_1','sg13cmos5l_buf_4']:
            cell=group_at(standard,standard.index('cell ('+master+')'));pin=group_at(cell,cell.index('pin (A)'));values={}
            for attribute in ['capacitance','rise_capacitance','fall_capacitance']:
                match=re.search(r'(?m)^\s*'+attribute+r'\s*:\s*([\d.eE+-]+)',pin);assert match;values[attribute]=float(match[1])
            for edge in ['rise','fall']:
                match=re.search(edge+r'_capacitance_range\s*\(([^)]+)\)',pin);assert match
                limits=list(map(float,match[1].split(',')));assert len(limits)==2
                values[edge+'_min'],values[edge+'_max']=limits
            cap_models[master]=values
        deltas={key:cap_models['sg13cmos5l_buf_4'][key]-value for key,value in cap_models['sg13cmos5l_buf_1'].items()}
        cap_deltas[corner]={pin+'/'+edge:({key:value for key,value in deltas.items() if key=='capacitance' or key.startswith('rise' if edge=='^' else 'fall')} if pin!='fanout913/X' else {'unchanged':0}) for pin in ['_17772_/Y','fanout914/X','fanout913/X'] for edge in ['^','v']}
    write(out/'inputs.json',dict(corners=corners,references=references,pin_cap_deltas=cap_deltas,clock_pins=sorted(clock_pins),sta_binary='/nix/store/arn1fw4jayhhjyg7839qb77kjyxfxpfw-opensta/bin/sta',scope='Noedit standalone control thenvirtualtwo-master timing model usingtheexactsame faithfullyaugmentedperpinwireSPEF PINCAPNONE; no physicalDB.'))
    bind(out/'inputs.json');assert time.time()+220<=stop,'Insufficient native window after staging'
    result=execute(out,list(paths),['python3','-B','/work/diagnostic/worker.py'],seconds=420,cpus=3,memory='3g',schema='pinwheel-buffered-tt-stable-pair4-fixedrc-assessment-v1',scope='Six standaloneSTA processes: fresh3corner unmodified control verifiedagainst6168affectedsourcepaths/global/clockwaveforms, then3corner virtualpair; no ODB/physicaledit/reroute.',expected_hashes=paths,absolute_work_stop=stop,all_in_deadline_monotonic=started+min(540,deadline-time.time()+time.monotonic()-started),phase_started_monotonic=started,host_stage_seconds=60,extra=dict(selection_sha256=cli.selection_sha256,prepared_sha256=sha(TOOLS/'prepared.json'),physical_candidate=False,source_producer_status='failed',source_producer_exit_code=1,source_native_reference_report_sha256=sha(REFERENCE/'report.json'),corrected_export_report_sha256=cli.corrected_export_sha256,source_database_sha256=sha(SOURCE/'pass2/routed.odb'),source_netlist_sha256=sha(out/'control.v'),virtual_netlist_sha256=sha(out/'virtual.v')))
    result['all_in_elapsed_seconds']=round(time.monotonic()-started,3);write(out/'report.json',result);print(out/'report.json',result['status'],result['all_in_elapsed_seconds'],flush=True)
    return 0 if result['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
