"""Prepare the exact terminal timing ECO; host only, no CAD execution."""
import ast,hashlib,json,re,shutil,sys
from copy import deepcopy
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
def overlap(a,b):return a[0]<b[2] and b[0]<a[2] and a[1]<b[3] and b[1]<a[3]
def main():
    source=ROOT/'build/physical/tt-buffered-locality-recovery-02/runs/tt-buffered-physical-05-recovery-01/10-openroad-resizertimingpostcts/tt_um_pinwheel_buffered.odb'
    inventory=ROOT/'build/physical/tt-buffered-route-effort-control-route-01/before-inventory.json'
    assert sha(source)=='95f0fdb260de137d5b4f77669c9aaa5eb3bf56e7dc55f4c9b7d51b2b8a16556e'
    before=json.loads(inventory.read_text())
    pockets=[('_30685_',[532800,245700,537120,249480],'R0'),('_30753_',[262560,219240,266880,223020],'MX'),('_30779_',[181440,313740,185760,317520],'R0'),('_30684_',[463680,241920,468000,245700],'MX'),('_30686_',[458400,257040,462720,260820],'MX'),('_30712_',[358560,291060,362880,294840],'R0'),('_30617_',[533280,291060,537600,294840],'R0'),('_30616_',[511200,287280,515520,291060],'MX')]
    resizes={'fanout1946':dict(before='sg13cmos5l_buf_1',after='sg13cmos5l_buf_4',bbox_dbu=[608640,366660,612480,370440],orientation='MY'),'_18965_':dict(before='sg13cmos5l_or3_1',after='sg13cmos5l_or3_2',bbox_dbu=[770400,11340,774240,15120],orientation='R0')}
    occupied=[(n,v['bbox_dbu']) for n,v in before['instances'].items()]+[('blockage'+str(i),v[0]) for i,v in enumerate(before['placement_blockages'])]
    additions=[]
    for endpoint,box,orientation in pockets:
        assert not any(overlap(box,b) for n,b in occupied)
        rows=[r for r in before['rows'] if r['bbox_dbu'][0]<=box[0]<box[2]<=r['bbox_dbu'][2] and r['bbox_dbu'][1]==box[1] and r['bbox_dbu'][3]==box[3]];assert len(rows)==1
        row=rows[0];assert (box[0]-row['origin_dbu'][0])%480==0 and orientation==row['orientation']
        old=before['instances'][endpoint];assert old['master']=='sg13cmos5l_dfrbpq_1'
        source_net=next(n for p,n,d in old['terminals'] if p=='D');net=before['nets'][source_net]
        assert net['sig_type']=='SIGNAL' and net['nondefault_rule'] is None
        name='timing_eco_hold_'+endpoint.strip('_');newnet=name+'_D'
        assert name not in before['instances'] and newnet not in before['nets']
        additions.append(dict(instance=name,master='sg13cmos5l_dlygate4sd3_1',endpoint=endpoint,pin='D',source_net=source_net,new_net=newnet,bbox_dbu=box,orientation=orientation,row=row['name'],original_endpoint=old,source_net_inventory=net))
        occupied.append((name,box))
    for n,r in resizes.items():
        old=before['instances'][n];assert old['master']==r['before'] and old['orientation']==r['orientation']
        assert not any(overlap(r['bbox_dbu'],b) for m,b in occupied if m!=n)
        rows=[v for v in before['rows'] if v['bbox_dbu'][0]<=r['bbox_dbu'][0]<r['bbox_dbu'][2]<=v['bbox_dbu'][2] and v['bbox_dbu'][1]==r['bbox_dbu'][1] and v['bbox_dbu'][3]==r['bbox_dbu'][3]];assert len(rows)==1
        assert (r['bbox_dbu'][0]-rows[0]['origin_dbu'][0])%480==0
        assert ((r['orientation'] in ('MX','R180'))==(rows[0]['orientation']=='MX'))
        r['original_instance']=old;r['row']=rows[0]['name']
    libs={}
    for corner in ['nom_typ_1p20V_25C','nom_slow_1p08V_125C','nom_fast_1p32V_m40C']:
        file=ROOT/'build/physical/tt-buffered-route-effort-probe-timing-01/lib'/('sg13cmos5l_stdcell_'+corner.removeprefix('nom_')+'.lib')
        assert file.exists();libs[corner]={'path':str(file.relative_to(ROOT)),'sha256':sha(file)}
    policy=dict(schema='pinwheel-buffered-tt-timing-eco-policy-v1',source_database=str(source.relative_to(ROOT)),source_database_sha256=sha(source),source_native_inventory=str(inventory.relative_to(ROOT)),source_native_inventory_sha256=sha(inventory),source_original_state='build/physical/tt-buffered-locality-recovery-02/runs/tt-buffered-physical-05-recovery-01/11-openroad-stamidpnr-2/state_out.json',resizes=resizes,additions=additions,allowed_original_master_changes=sorted(resizes),allowed_original_sink_rewires=sorted(a['endpoint']+'/D' for a in additions),allowed_original_position_changes=['fanout1946','_18965_'],added_instances=[a['instance'] for a in additions],added_nets=[a['new_net'] for a in additions],power_bindings={'VDD':'VPWR','VSS':'VGND'},liberty=libs,original_instance_count=len(before['instances']),expected_final_instance_count=len(before['instances'])+8,mandatory_neighbors=0,unchanged_original_placement_count=len(before['instances'])-2,require_root_headroom_admission_before_native_edit=True,optimization_commands={'GPL':0,'DPL':0,'CTS':0,'repair_timing':0,'global_route':0},scope='Exactly two same-function drive resizes and eight noninverting one-sink terminal D delay stages; all other original geometry/master/status/clock and all original nonselected terminals unchanged. No timing or power-grid qualification claim.')
    policy['source_original_state_sha256']=sha(ROOT/policy['source_original_state']);write(HERE/'plan.json',policy)
    # Frozen copies of existing reviewed executor/snapshot and actual identity-checker dependencies.
    shutil.copyfile(ROOT/'build/physical/tt-buffered-fanout2803-candidate-01/common.py',HERE/'common.py')
    shutil.copyfile(ROOT/'build/physical/tt-buffered-route-effort-tools-01/native_inventory.py',HERE/'native_inventory.py')
    copied={};pending=['physical_routed_repair','physical_organization'];seen=set();(HERE/'identity').mkdir(exist_ok=True)
    while pending:
        m=pending.pop()
        if m in seen:continue
        seen.add(m);p=ROOT/'scripts'/(m+'.py')
        if not p.exists():continue
        q=HERE/'identity'/p.name;shutil.copyfile(p,q);copied[str(p.relative_to(ROOT))]=sha(p)
        for node in ast.walk(ast.parse(p.read_text())):
            if isinstance(node,ast.ImportFrom) and node.module and (ROOT/'scripts'/(node.module+'.py')).exists():pending.append(node.module)
            elif isinstance(node,ast.Import):
                pending += [v.name for v in node.names if (ROOT/'scripts'/(v.name+'.py')).exists()]
    write(HERE/'identity-source.json',copied)
    (HERE/'lib').mkdir(exist_ok=True)
    for c,v in libs.items():shutil.copyfile(ROOT/v['path'],HERE/'lib'/Path(v['path']).name)
    sys.path.insert(0,str(HERE/'identity'));from physical_organization import Library
    library=Library({c:[(ROOT/v['path']).read_text()] for c,v in libs.items()});functions={}
    for c in libs:
        functions[c]={}
        for n,r in resizes.items():
            pins=[p for p,n,d in r['original_instance']['terminals'] if d in ('INPUT','OUTPUT')]
            for pin in pins:
                bodies=[library.pin(c,k,pin) for k in [r['before'],r['after']]]
                directions=[re.findall(r'\bdirection\s*:\s*"?(\w+)"?\s*;',b) for b in bodies];assert directions[0]==directions[1]
                f=[re.findall(r'\bfunction\s*:\s*"([^"]*)"\s*;',b) for b in bodies]
                if directions[0]==['output']:assert len(f[0])==1 and f[0]==f[1]
                functions[c][n+'/'+pin]={'direction':directions[0],'functions':f}
        assert re.findall(r'\bfunction\s*:\s*"([^"]*)"\s*;',library.pin(c,'sg13cmos5l_dlygate4sd3_1','X'))==['A']
    write(HERE/'host-controls.json',dict(status='passed',legal_empty_pockets=8,exact_resizes=2,neighbors=0,pinned_all_corner_functions=functions,source_inventory_sha256=sha(inventory),source_database_sha256=sha(source),plan_sha256=sha(HERE/'plan.json'),source_sha256={str(p.relative_to(ROOT)):sha(p) for p in [Path(__file__).resolve(),ROOT/'build/physical/tt-buffered-route-effort-tools-01/native_inventory.py',ROOT/'build/physical/tt-buffered-fanout2803-candidate-01/common.py',*[ROOT/k for k in copied],*[ROOT/v['path'] for v in libs.values()]]}))
    print(json.dumps({'plan_sha256':sha(HERE/'plan.json'),'eight_pockets':[(a['endpoint'],a['bbox_dbu'],a['orientation']) for a in additions],'host_controls_sha256':sha(HERE/'host-controls.json'),'copied_identity_modules':len(copied)},indent=2))
if __name__=='__main__':main()
