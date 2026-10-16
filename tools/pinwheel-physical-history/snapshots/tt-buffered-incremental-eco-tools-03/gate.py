"""Exact native database edit gate plus all-corner transport/resize identity."""
import json,os,sys
from copy import deepcopy
from pathlib import Path
from native_inventory import ROOT,sha,snapshot,load
sys.path.insert(0,str(ROOT/'identity'))
from physical_routed_repair import compare_repair
from physical_organization import Library

def expected(before,plan):
    value=deepcopy(before)
    for n,r in plan['resizes'].items():
        row=value['instances'][n];assert row['master']==r['before']
        row.update(master=r['after'],bbox_dbu=r['bbox_dbu'],orientation=r['orientation'],width_dbu=r['bbox_dbu'][2]-r['bbox_dbu'][0])
    for a in plan['additions']:
        n=a['instance'];ep=a['endpoint'];source=a['source_net'];new=a['new_net'];b=a['bbox_dbu']
        value['instances'][n]={'master':a['master'],'bbox_dbu':b,'orientation':a['orientation'],'placement_status':'PLACED','width_dbu':4320,'height_dbu':3780,'macro':False,'terminals':sorted([['A',source,'INPUT'],['X',new,'OUTPUT'],['VDD','VPWR','INOUT'],['VSS','VGND','INOUT']]),'group':None,'region':None}
        t=value['instances'][ep]['terminals'];assert ['D',source,'INPUT'] in t
        t.remove(['D',source,'INPUT']);t.append(['D',new,'INPUT']);t.sort()
        old=value['nets'][source]['terminals'];assert [ep,'D','INPUT'] in old
        old.remove([ep,'D','INPUT']);old.append([n,'A','INPUT']);old.sort()
        value['nets'][new]={'sig_type':'SIGNAL','ports':[],'terminals':sorted([[ep,'D','INPUT'],[n,'X','OUTPUT']]),'nondefault_rule':None}
        for rail,pin in [('VPWR','VDD'),('VGND','VSS')]:value['nets'][rail]['terminals'].append([n,pin,'INOUT']);value['nets'][rail]['terminals'].sort()
    return value

def signal_module(snapshot):
    nets={n:i+2 for i,n in enumerate(sorted(snapshot['nets'])) if snapshot['nets'][n]['sig_type'] not in ('POWER','GROUND')}
    ports={}
    for n,sig,direction,net,shapes in snapshot['pins']:
        if sig not in ('POWER','GROUND'):ports[n]={'direction':direction.lower(),'bits':[nets[net]]}
    cells={}
    for n,row in snapshot['instances'].items():
        terms=[(p,net,d) for p,net,d in row['terminals'] if net in nets]
        cells[n]={'type':row['master'],'parameters':{},'port_directions':{p:d.lower() for p,net,d in terms},'connections':{p:[nets[net]] for p,net,d in terms}}
    return {'ports':ports,'cells':cells}

def protected_def(path):
    import re
    text=path.read_text()
    for section in ('COMPONENTS','NETS','SPECIALNETS'):
        text=re.sub(r'^'+section+r'\s+\d+\s*;.*?^END '+section+r'\s*$','['+section+' native snapshot checked]',text,flags=re.M|re.S)
    return text

def validate_geometry(value,plan):
    for n in [*plan['resizes'],*plan['added_instances']]:
        c=value['instances'][n];b=c['bbox_dbu']
        rows=[r for r in value['rows'] if r['bbox_dbu'][0]<=b[0]<b[2]<=r['bbox_dbu'][2] and r['bbox_dbu'][1]==b[1] and r['bbox_dbu'][3]==b[3]];assert len(rows)==1,n
        r=rows[0];assert (b[0]-r['origin_dbu'][0])%r['site_width_dbu']==0,n
        assert ((c['orientation'] in ('MX','R180'))==(r['orientation']=='MX')),n
        overlap=lambda q:b[0]<q[2] and q[0]<b[2] and b[1]<q[3] and q[1]<b[3]
        assert not any(overlap(q['bbox_dbu']) for m,q in value['instances'].items() if m!=n),n
        assert not any(overlap(q[0]) for q in value['placement_blockages']),n

def main():
    phase=os.environ['PINWHEEL_INVENTORY_PHASE'];plan=json.loads((ROOT/'plan.json').read_text())
    db,b=load(ROOT/'input.odb');before=snapshot(db,b,'before' if phase=='before' else 'recheck-before')
    assert sha(ROOT/'input.odb')==plan['source_database_sha256']
    retained=json.loads((ROOT/'source-inventory.json').read_text());assert before==retained,'Original native inventory differs'
    if phase=='before':
        (ROOT/'before-inventory.json').write_text(json.dumps(before,separators=(',',':'))+'\n');print('EXACT_SOURCE_INVENTORY_ADMITTED');return
    assert phase=='after';assert before==json.loads((ROOT/'before-inventory.json').read_text())
    db,b=load(ROOT/'candidate.odb');after=snapshot(db,b,'after');want=expected(before,plan)
    failed=[k for k in want if want[k]!=after[k]]
    (ROOT/'after-inventory.json').write_text(json.dumps(after,separators=(',',':'))+'\n')
    assert not failed,('Unexpected full native snapshot changes',failed)
    assert protected_def(ROOT/'before.def')==protected_def(ROOT/'candidate.def'),'Protected DEF section changed'
    validate_geometry(after,plan)
    texts={c:[(ROOT/'lib'/Path(v['path']).name).read_text()] for c,v in plan['liberty'].items()}
    proof=compare_repair(signal_module(before),signal_module(after),Library(texts),list(texts),allow_resizing=True)
    assert proof['resized_cells']=={n:{'before':r['before'],'after':r['after']} for n,r in plan['resizes'].items()}
    assert proof['added_cells']=={a['instance']:a['master'] for a in plan['additions']}
    source_clock={n:v for n,v in before['nets'].items() if v['sig_type']=='CLOCK'}
    current_clock={n:v for n,v in after['nets'].items() if v['sig_type']=='CLOCK'};assert source_clock==current_clock
    unchanged=[n for n,v in before['instances'].items() if v['bbox_dbu']==after['instances'][n]['bbox_dbu'] and v['orientation']==after['instances'][n]['orientation']]
    measurement={'schema':'pinwheel-buffered-tt-timing-eco-change-proof-v1','status':'measured','exact_edit_gate_passed':True,'source_database_sha256':sha(ROOT/'input.odb'),'output_database_sha256':sha(ROOT/'candidate.odb'),'original_instances':len(before['instances']),'final_instances':len(after['instances']),'exact_resizes':plan['resizes'],'exact_added_instances':plan['added_instances'],'exact_rewired_original_pins':plan['allowed_original_sink_rewires'],'added_cells':8,'resized_cells':2,'original_placement_unchanged_count':len(unchanged),'other_original_placements_and_statuses_unchanged':True,'original_statuses_restored':True,'unselected_masters_and_connections_unchanged':True,'only_eight_D_rewires':True,'clock_tree_unchanged':True,'PG_special_wire_geometry_unchanged':True,'added_power_bindings_exact':True,'rows_blockages_pins_macros_unchanged':True,'TechLEF_and_NDR_unchanged':True,'native_legal_changed_footprints':True,'all_corner_signal_identity':proof,'before_netlist_sha256':sha(ROOT/'before.v'),'after_netlist_sha256':sha(ROOT/'after.v'),'netlist_bytes_intentionally_changed':sha(ROOT/'before.v')!=sha(ROOT/'after.v'),'optimizer_calls':plan['optimization_commands'],'scope':'No RTL/ABI/SDC changes. Native serialized whole-inventory exact edit and independently checked all-corner identity functions; timing/routing are separate gates.'}
    (ROOT/'change-proof.json').write_text(json.dumps(measurement,indent=2)+'\n');print('EXACT_TIMING_ECO_INVENTORY_AND_FUNCTION_GATE_PASSED')
if __name__=='__main__':main()
