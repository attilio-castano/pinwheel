"""HOST observation of exact driver loads in pre/post antenna OpenROAD DEF.

No guessed name translation, CAD execution, mutation or repair acceptance.
The netlist view may be inherited; the actual DEF view is compared explicitly.
"""
import argparse
from datetime import datetime,timezone
from pathlib import Path
import re

import streaming_8x4_prepare as P
from streaming_8x4_geometry import regular,require,sha

DRIVERS=('fanout1772','fanout1699')


def parse_def(path):
    text=regular(path).read_text()
    def section(kind):
        match=re.search(r'^'+kind+r'\s+(\d+)\s*;\s*\n(.*?)^END '+kind+r'\s*$',text,re.M|re.S)
        require(match is not None,'Missing DEF section: '+kind)
        rows=re.findall(r'^\s*-\s+(.*?)\s*;\s*$',match[2],re.M|re.S)
        require(len(rows)==int(match[1]),'DEF declared record count differs: '+kind)
        return rows
    components={}
    for row in section('COMPONENTS'):
        match=re.match(r'(\S+)\s+(\S+)',row);require(match is not None,'Unsupported component grammar')
        name,master=match.groups();require(name not in components,'Duplicate DEF component');components[name]=master
    nets={}
    for row in section('NETS'):
        name=re.match(r'(\S+)',row)[1];prefix=row[len(name):].split('+',1)[0]
        endpoints=re.findall(r'\(\s*(\S+)\s+(\S+)\s*\)',prefix)
        remainder=re.sub(r'\(\s*\S+\s+\S+\s*\)','',prefix)
        require(not remainder.strip() and name not in nets and len(set(endpoints))==len(endpoints),'Unsupported/duplicate net grammar')
        nets[name]=set(endpoints)
    return components,nets


def observe(flow,state_path):
    state_path=regular(state_path).resolve();state=P.read(state_path);frozen={str(state_path):sha(state_path)}
    def bind(key):
        name=Path(state[key]);require(name.is_relative_to('/work/run'),'View outside exact source flow mount')
        path=(flow/name.relative_to('/work/run')).resolve();require(path.is_relative_to(flow),'View escapes flow')
        frozen[str(path)]=sha(path);return dict(path=str(path),sha256=sha(path))
    view=bind('def');netlist=bind('nl');components,nets=parse_def(view['path']);drivers={}
    for name in DRIVERS:
        matches=[(net,points) for net,points in nets.items() if (name,'X') in points]
        require(len(matches)==1 and name in components,'Driver does not bind exactly once: '+name)
        net,points=matches[0]
        require(all(instance=='PIN' or instance in components for instance,pin in points),'Unresolved endpoint component')
        drivers[name]=dict(net=net,master=components[name],load_count=len(points)-1,
            endpoints=[dict(instance=i,pin=p,master=components.get(i)) for i,p in sorted(points)])
    return dict(state=dict(path=str(state_path),sha256=sha(state_path)),def_view=view,netlist=netlist,
        component_count=len(components),net_count=len(nets),drivers=drivers),frozen


def compare(flow,before,after,output):
    flow=Path(flow).resolve(strict=True);output=Path(output).absolute();require(not output.exists(),'Preserve prior observation')
    first,frozen=observe(flow,before);second,other=observe(flow,after);frozen.update(other);deltas={}
    for name in DRIVERS:
        a,b=first['drivers'][name],second['drivers'][name]
        require(a['master']==b['master'] and a['net']==b['net'],'Driver/master/net changed')
        endpoints=lambda x:{(e['instance'],e['pin'],e['master']) for e in x['endpoints']}
        aa,bb=endpoints(a),endpoints(b)
        deltas[name]=dict(net=a['net'],master=a['master'],before_loads=a['load_count'],after_loads=b['load_count'],
            added=sorted(bb-aa),removed=sorted(aa-bb))
    require(all(sha(path)==value for path,value in frozen.items()),'Stage evidence changed during HOST observation')
    result=dict(schema='pinwheel.streaming-8x4-antenna-fanout-observation.v1',observed_utc=datetime.now(timezone.utc).isoformat(),
        producer_sha256=sha(__file__),before=first,after=second,deltas=deltas,input_sha256=frozen,
        inputs_unchanged_during_read=True,active_parent_run=True,qualified=False,physical_acceptance=False,
        boundary='Exact stage DEF connectivity delta only. Fresh STA can attribute added load count; no repair or final signoff acceptance follows. Parent run seal remains pending.')
    P.write(output,result);return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('flow','before','after','output'):parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args();compare(args.flow,args.before,args.after,args.output);print(args.output)


if __name__=='__main__':main()
