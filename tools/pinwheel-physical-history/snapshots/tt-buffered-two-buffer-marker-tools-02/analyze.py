"""Source-bound paired native marker participation. Host-only; counts are not causal allocations."""
import argparse,collections,hashlib,json,pathlib,re,time
ROOT=pathlib.Path(__file__).resolve().parents[3]
TOOLS=pathlib.Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(pathlib.Path(p).read_text())
def bind(files,p,digest=None):
    p=pathlib.Path(p).resolve();assert p.is_relative_to(ROOT) and p.is_file()
    value=sha(p);assert digest is None or value==digest,(str(p),'Hash changed')
    assert str(p) not in files or files[str(p)]==value
    files[str(p)]=value;return p
def norm(n):return n.replace('\\','')
def markers(path):
    result=[]
    text=path.read_text()
    for q in text.split('violation type: ')[1:]:
        lines=q.splitlines();assert lines[0] in ('Horizontal congestion','Vertical congestion')
        names=[norm(n) for n in re.findall(r'net:(\S+)',lines[1])]
        v=re.search(r'capacity:(\d+) usage:(\d+) overflow:(\d+)',q)
        bb=re.search(r'bbox = \(([-\d.]+), ([-\d.]+)\) - \(([-\d.]+), ([-\d.]+)\)',q)
        assert v and bb
        capacity,usage,overflow=map(int,v.groups())
        assert overflow==usage-capacity>0 and len(names)==usage and len(set(names))==len(names)
        result.append(dict(direction=lines[0].split()[0],nets=set(names),capacity=capacity,usage=usage,
            overflow=overflow,bbox_dbu=[round(float(x)*1000) for x in bb.groups()]))
    assert result;return result

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--selection',type=pathlib.Path,required=True)
    parser.add_argument('--out',type=pathlib.Path,required=True);args=parser.parse_args();started=time.monotonic();files={}
    prepared=read(TOOLS/'prepared.json');assert sha(__file__)==prepared['script_sha256']
    bind(files,TOOLS/'prepared.json');bind(files,pathlib.Path(__file__))
    for name,digest in prepared['derivation_sha256'].items():bind(files,ROOT/name,digest)
    selection=read(bind(files,args.selection,prepared['selection_sha256']))
    assert selection['schema']=='pinwheel-buffered-tt-two-buffer-selection-v1'
    for ref in selection['references'].values():bind(files,ROOT/ref['path'],ref['sha256'])
    policy=read(ROOT/selection['references']['policy']['path']);assert set(policy['allowed_movable_instances'])=={'fanout2803','fanout2903'}
    powerdir=ROOT/'build/physical/tt-buffered-two-buffer-power-01';power=read(bind(files,powerdir/'report.json'))
    assert power['status']=='passed' and power['exit_code']==0 and power['inputs_unchanged']
    assert power['container_termination']['status']=='absent'
    for name in ('reference-native.def','metadata.json','measurement.json'):
        bind(files,powerdir/name,power['artifact_sha256'][name])
    assert power['measurement']==read(powerdir/'measurement.json')
    text=(powerdir/'reference-native.def').read_text();section=re.search(r'\nNETS \d+ ;\n(.*?)\nEND NETS',text,re.S)[1]
    netrecords={}
    for m in re.finditer(r'(?m)^\s*- (\S+)\s.*?;',section,re.S):netrecords[norm(m[1])]=m[0]
    clock={n for n,r in netrecords.items() if '+ USE CLOCK' in r};ndr={n for n,r in netrecords.items() if '+ NONDEFAULTRULE' in r}
    assert len(clock)==332 and len(ndr)==10 and ndr.issubset(clock)
    focus=set(policy['full_incident_HPWL_proxy_um']['net_names']);assert focus=={'_05129_','_09502_','net2803','net2903'}
    arms={}
    for arm in ('control','candidate'):
        directory=ROOT/('build/physical/tt-buffered-two-buffer-'+arm+'-route-01')
        report=read(bind(files,directory/'report.json'))
        assert report['status']=='passed' and report['exit_code']==0 and report['inputs_unchanged']
        assert report['native_extra_iterations']==5 and report['accepted_route'] is False
        assert report['container_termination']['status']=='absent'
        for name in ('congestion.json','native.log','geometry.json','after_grt.guide','measurement.json'):
            bind(files,directory/name,report['artifact_sha256'][name])
        assert report['measurement']==read(directory/'measurement.json')
        assert report['source_database_sha256']==(power['reference_database_sha256'] if arm=='control' else power['source_database_sha256'])
        geometry=read(directory/'geometry.json');mm=markers(directory/'congestion.json')
        macrorects=[m['bbox_dbu'] for m in geometry['macros'].values()]
        macrotypes=collections.defaultdict(set)
        for pin in geometry['macro_pins']:macrotypes[norm(pin['net'])].add(pin['pin'].split('[')[0])
        categories={'CLOCK':clock,'NDR_assigned_clock':ndr,'SRAM_terminal':set(macrotypes),
            'SRAM_ADDR':{n for n,t in macrotypes.items() if 'A_ADDR' in t},
            'SRAM_DIN_DOUT':{n for n,t in macrotypes.items() if t&{'A_DIN','A_DOUT'}},'focused_four_nets':focus}
        summary=collections.Counter();participation={k:collections.Counter() for k in categories}
        pernet=collections.defaultdict(collections.Counter);direction=collections.defaultdict(collections.Counter)
        for m in mm:
            o,b=m['overflow'],m['bbox_dbu'];zero=m['capacity']==0
            summary['marker_count']+=1;summary['native_marker_overflow']+=o
            summary['zero_capacity_overflow']+=o*zero;summary['zero_capacity_marker_count']+=zero
            summary['fully_inside_macro_overflow']+=o*any(b[0]>=r[0] and b[1]>=r[1] and b[2]<=r[2] and b[3]<=r[3] for r in macrorects)
            summary['all_source_incidences']+=m['usage']
            label=m['direction']+('_zero_capacity' if zero else '_positive_capacity')+('_above216um' if b[1]>=216000 else '')
            direction[label]['marker_count']+=1;direction[label]['overflow']+=o;direction[label]['source_incidences']+=m['usage']
            direction[label]['CLOCK_source_incidences']+=len(m['nets']&clock)
            for k,ns in categories.items():
                present=m['nets']&ns;participation[k]['marker_count']+=bool(present)
                participation[k]['cooccurring_overflow']+=o*bool(present)
                participation[k]['source_incidences']+=len(present);participation[k]['zero_capacity_source_incidences']+=len(present)*zero
                participation[k]['zero_capacity_marker_count']+=bool(present)*zero
            for n in m['nets']:
                pernet[n]['marker_count']+=1;pernet[n]['cooccurring_overflow']+=o;pernet[n]['zero_capacity_source_incidences']+=zero
        assert summary['native_marker_overflow']==report['measurement']['native_overflow']
        native=(directory/'native.log').read_text();fallback=re.findall(r'Disabled NDR \(to reduce congestion\) for net: (\S+)',native)
        assert len(fallback)==report['measurement']['native_clock_ndr_fallback_retries'], 'Native fallback count disagrees with route receipt'
        arms[arm]={'route_report_sha256':sha(directory/'report.json'),'source_database_sha256':report['source_database_sha256'],
            'native_layers':report['measurement']['native_layers'],'saved_grid_overflow':report['measurement']['saved_preferred_grid_overflow'],
            'summary':dict(summary),'directions':{k:dict(v) for k,v in direction.items()},
            'participation':{k:dict(v) for k,v in participation.items()},
            'focused_nets':{n:dict(pernet[n]) for n in sorted(focus)},
            'native_NDR_fallback_count':len(fallback),'native_NDR_fallback_net_order':fallback,
            'top_zero_capacity_nets':[dict(net=n,**dict(v)) for n,v in sorted(pernet.items(),key=lambda t:(-t[1]['zero_capacity_source_incidences'],t[0]))[:15]]}
    assert arms['control']['source_database_sha256']=='95f0fdb260de137d5b4f77669c9aaa5eb3bf56e7dc55f4c9b7d51b2b8a16556e'
    assert all(sha(p)==v for p,v in files.items()),'Sources changed during host analysis'
    out=args.out.resolve();assert out.is_relative_to(ROOT/'build/physical') and not out.exists();out.mkdir()
    result={'schema':'pinwheel-buffered-tt-two-buffer-native-marker-participation-v1','status':'passed',
        'CAD_launched':False,'source_sha256':files,'CLOCK_net_count':len(clock),'NDR_assigned_clock_net_count':len(ndr),
        'arms':arms,'host_elapsed_seconds':round(time.monotonic()-started,3),
        'boundary':'Native text marker sources equal usage per marker; categories overlap, cooccurring overflow is not causal allocation. Zero-capacity source incidences are net-edge occurrences, not guaranteed removable overflow. Preferred saved grids and native directional markers are different representations. Clock NDR warnings do not establish residual dominance. This is host-only analysis of completed coarse diagnostics, not accepted routing/signoff.'}
    target=out/'report.json';target.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'report':str(target.relative_to(ROOT)),'sha256':sha(target),'host_elapsed_seconds':result['host_elapsed_seconds']}))
if __name__=='__main__':main()
