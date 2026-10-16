"""Native immutable candidate macro/contact and supply-grid readback."""
import hashlib
import json
from pathlib import Path
import re
import odb

ROOT = Path('/work/diagnostic')
def rect(r): return [r.xMin(), r.yMin(), r.xMax(), r.yMax()]
def fingerprint(v): return hashlib.sha256(json.dumps(v,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def load(name):
    db=odb.dbDatabase.create();odb.read_db(db,str(ROOT/name));return db,db.getChip().getBlock()
def grid_inventory(block):
    records=[];counts={}
    for name in ('VPWR','VGND'):
        net=block.findNet(name);assert net is not None,name
        shapes=0;vias=0;bpins=0
        for sw in net.getSWires():
            for r in sw.getWires():
                layer=r.getTechLayer()
                if layer is not None:
                    records.append([name,'metal',layer.getName(),rect(r)]);shapes+=1
                else:
                    via=r.getBlockVia() or r.getTechVia();assert via is not None
                    x,y=r.getViaXY()
                    geometry=sorted([[b.getTechLayer().getName(),rect(b)] for b in via.getBoxes() if b.getTechLayer() is not None])
                    records.append([name,'via',[x,y],geometry]);vias+=1
        for term in net.getBTerms():
            for pin in term.getBPins():
                for r in pin.getBoxes():
                    layer=r.getTechLayer();assert layer is not None
                    records.append([name,'boundary',term.getName(),layer.getName(),rect(r)]);bpins+=1
        counts[name]={'metal_shapes':shapes,'vias':vias,'boundary_shapes':bpins}
    return sorted(records),counts

db,block=load('input.odb');reference_db,reference=load('reference.odb')
expected={'engine.memory.storage0':[252000,30000,1036480,94360],
          'engine.memory.storage1':[252000,144000,1036480,208360]}
macros=[i for i in block.getInsts() if i.getMaster().isBlock()]
assert {i.getName() for i in macros}==set(expected)
plan=json.loads((ROOT/'power-columns.json').read_text())
result={};dbu=block.getDbUnitsPerMicron();assert dbu==1000
for inst in macros:
    master=inst.getMaster();bbox=rect(inst.getBBox())
    assert master.getName()=='RM_IHPSG13_1P_64x64_c2_bm_bist'
    assert str(inst.getOrient())=='R0',inst.getOrient()
    assert bbox==expected[inst.getName()],(inst.getName(),bbox)
    assert (master.getWidth(),master.getHeight())==(784480,64360)
    x,y=bbox[:2];height=master.getHeight();contacts={}
    for netname,pins in {'VPWR':['VDD!','VDDARRAY!'],'VGND':['VSS!']}.items():
        for pinname in pins:
            term=inst.findITerm(pinname)
            assert term is not None and term.getNet() is not None and term.getNet().getName()==netname
            local=[rect(r) for pin in term.getMTerm().getMPins() for r in pin.getGeometry()
                   if r.getTechLayer() is not None and r.getTechLayer().getName()=='Metal4']
            assert local
            assert all(0<=a<c<=master.getWidth() and 0<=b<d<=height for a,b,c,d in local)
            transformed=sorted([[x+a,y+b,x+c,y+d] for a,b,c,d in local])
            actual=sorted([rect(r) for layer,r in term.getGeometries() if layer.getName()=='Metal4'])
            assert actual==transformed,(inst.getName(),pinname,'native transform disagreement')
            count=sum(any(a<=round(cx0*dbu) and round(cx1*dbu)<=c for a,b,c,d in actual)
                      for cx0,cx1 in plan['nets'][netname])
            expected_count={'VDD!':68,'VDDARRAY!':64,'VSS!':68}[pinname]
            assert count==expected_count,(pinname,count)
            contacts[pinname]={'net':netname,'Metal4_rectangles':len(actual),
                               'native_transform_matches_expected':True,'direct_column_contacts':count,
                               'geometry_sha256':fingerprint(actual),
                               'native_y_spans_dbu':sorted({(r[1],r[3]) for r in actual})}
    signal_geometries=[rect(r) for term in inst.getITerms() if str(term.getSigType()) not in ('POWER','GROUND')
                       for layer,r in term.getGeometries() if layer.getName()=='Metal2']
    assert len(signal_geometries)==342
    assert all(r[1]==bbox[1] for r in signal_geometries)
    result[inst.getName()]={'bbox_dbu':bbox,'master':master.getName(),'orientation':'R0',
                           'signal_rectangles':342,'all_signal_rectangles_touch_south_edge':True,
                           'supply_contacts':contacts}
current_grid,current_counts=grid_inventory(block);old_grid,old_counts=grid_inventory(reference)
assert current_grid==old_grid,'Supply special-wire/via/boundary geometry changed'
def signal_pins(b):
    data=[]
    for term in b.getBTerms():
        if str(term.getSigType()) in ('POWER','GROUND'):continue
        boxes=sorted([[r.getTechLayer().getName(),rect(r)] for pin in term.getBPins()
                      for r in pin.getBoxes() if r.getTechLayer() is not None])
        data.append([term.getName(),str(term.getIoType()),boxes])
    return sorted(data)
actual_signal_pins=signal_pins(block);reference_signal_pins=signal_pins(reference)
assert len(actual_signal_pins)==43 and actual_signal_pins==reference_signal_pins,'43 TT signal shapes/placements changed'

policy=json.loads((ROOT/'policy.json').read_text())
allowed=policy['allowed_movable_instances']
assert len(allowed)==len(set(allowed)) and allowed
allowed=set(allowed)
def association(obj):return obj.getName() if obj is not None else None
def cells(b):
    return {i.getName():{'master':i.getMaster().getName(),'bbox_dbu':rect(i.getBBox()),
        'origin_dbu':list(i.getOrigin()),'orientation':str(i.getOrient()),
        'placement_status':str(i.getPlacementStatus()),'group':association(i.getGroup()),
        'region':association(i.getRegion()),
        'terminals':sorted([t.getMTerm().getName(),t.getNet().getName() if t.getNet() else None] for t in i.getITerms())}
        for i in b.getInsts()}
def immutable_layout(b):
    return {'rows':sorted([r.getName(),rect(r.getBBox()),str(r.getOrient()),r.getSite().getName(),list(r.getOrigin())] for r in b.getRows()),
        'regions':sorted([r.getName(),str(r.getRegionType()),sorted(rect(box) for box in r.getBoundaries())] for r in b.getRegions()),
        'groups':sorted([g.getName(),str(g.getType()),association(g.getRegion()),sorted(i.getName() for i in g.getInsts())] for g in b.getGroups()),
        'nets':sorted([n.getName(),str(n.getSigType()),sorted([t.getInst().getName(),t.getMTerm().getName()] for t in n.getITerms()),sorted(t.getName() for t in n.getBTerms())] for n in b.getNets()),
        'die':rect(b.getDieArea()),'core':rect(b.getCoreArea())}
current_cells,old_cells=cells(block),cells(reference)
assert set(current_cells)==set(old_cells),'Instance inventory changed'
assert allowed.issubset(current_cells),'Unknown frozen movable member'
assert immutable_layout(block)==immutable_layout(reference),'Rows/groups/regions/net topology/die changed'
protected_clock={n for n in old_cells if n.startswith(('clkbuf','delaybuf'))}
clock_net_members=set()
for net in reference.getNets():
    if str(net.getSigType())=='CLOCK':
        for term in net.getITerms():
            clock_net_members.add(term.getInst().getName())
            if str(term.getMTerm().getIoType())=='OUTPUT':protected_clock.add(term.getInst().getName())
declared_clock=set(policy.get('protected_clock_instances',[]))
assert protected_clock.issubset(declared_clock),'Frozen clock list omits native CTS instance'
assert not allowed.intersection(declared_clock),'Clock instance admitted to movement'
assert not allowed.intersection(clock_net_members),'Instance on native CLOCK net admitted to movement'
assert declared_clock.issubset(old_cells),'Unknown protected clock instance'
def immutable_DEF_sections(b,name):
    output=ROOT/name
    odb.write_def(b,str(output))
    text=output.read_text()
    data={}
    for section in ('NONDEFAULTRULES','BLOCKAGES','NETS','SPECIALNETS','VIAS','PINS','REGIONS','GROUPS','PROPERTYDEFINITIONS'):
        starts=list(re.finditer(r'^'+section+r'(?:\s+\d+\s*;)?\s*$',text,re.M))
        if not starts:data[section]=None;continue
        assert len(starts)==1,(section,'Repeated DEF section')
        end=re.search(r'^END '+section+r'\s*$',text[starts[0].end():],re.M)
        assert end is not None,(section,'Unterminated DEF section')
        body=text[starts[0].start():starts[0].end()+end.end()]
        data[section]=' '.join(body.split())
    data['tracks_and_grid']=sorted(re.findall(r'^(?:TRACKS|GCELLGRID)\b[^;]*;',text,re.M))
    return data
reference_def=immutable_DEF_sections(reference,'reference-native.def')
candidate_def=immutable_DEF_sections(block,'candidate-native.def')
assert candidate_def==reference_def,'Placement blockages, NDR definitions/associations, routed wires, pins or other immutable DEF sections changed'
def tech_LEFs(database,label):
    techs=list(database.getTechs())
    names=[t.getName() for t in techs]
    assert techs and len(names)==len(set(names)),'Missing or duplicate technology database'
    data={}
    for index,tech in enumerate(sorted(techs,key=lambda t:t.getName())):
        output=ROOT/(label+'-tech-'+str(index)+'.lef')
        odb.write_tech_lef(tech,str(output))
        assert output.is_file() and output.stat().st_size>0
        data[tech.getName()]={'native_bytes_sha256':hashlib.sha256(output.read_bytes()).hexdigest(),
            'canonical_text':' '.join(output.read_text().split())}
    return data
reference_tech=tech_LEFs(reference_db,'reference');candidate_tech=tech_LEFs(db,'candidate')
assert candidate_tech==reference_tech,'Full technology LEF including NDR definitions changed'
def center(box):return [(box[0]+box[2])/2,(box[1]+box[3])/2]
def L1(a,b):return (abs(a[0]-b[0])+abs(a[1]-b[1]))/dbu
member_constraints=[]
assert set(policy['members'])==allowed=={'fanout2803','fanout2903'}
assert policy['mandatory_destination_neighbors']==[]
for name,member in policy['members'].items():
    old,current=old_cells[name],current_cells[name]
    original=member['original']
    assert old['master']==original['master'] and old['bbox_dbu']==original['bbox_dbu']
    assert old['orientation']==original['orientation'] and old['placement_status']==original['placement_status']
    box=current['bbox_dbu']
    assert box==member['seed_bbox_dbu'],(name,'Exact frozen seed bbox not retained')
    assert current['orientation']==member['seed_orientation'],(name,'Exact frozen orientation not retained')
    actual_center,seed_center,old_center=center(box),center(member['seed_bbox_dbu']),center(old['bbox_dbu'])
    member_constraints.append({'instance':name,'actual_bbox_dbu':box,'seed_bbox_dbu':member['seed_bbox_dbu'],
        'actual_orientation':current['orientation'],'seed_orientation':member['seed_orientation'],
        'seed_center_axis_drift_dbu':[abs(actual_center[k]-seed_center[k]) for k in (0,1)],
        'original_center_L1_displacement_um':L1(actual_center,old_center),'constraints_met':True})
incident_names=set()
for name in allowed:
    inst=reference.findInst(name)
    assert inst.getMaster().getName()=='sg13cmos5l_buf_1'
    for t in inst.getITerms():
        net=t.getNet()
        if net is None or str(net.getSigType()) in ('POWER','GROUND'):continue
        assert str(net.getSigType())=='SIGNAL'
        incident_names.add(net.getName())
assert incident_names==set(policy['incident_net_inventory'])=={'_05129_','_09502_','net2803','net2903'}
def native_incident(net):
    return {'sig_type':str(net.getSigType()),'ports':sorted(t.getName() for t in net.getBTerms()),
        'terminals':sorted([{'instance':t.getInst().getName(),'pin':t.getMTerm().getName(),
            'io_type':str(t.getMTerm().getIoType())} for t in net.getITerms()],
            key=lambda t:(t['instance'],t['pin'],t['io_type']))}
def hpwl(net,b):
    assert not list(net.getBTerms()),'Incident net unexpectedly reaches a top-level port'
    names=sorted({t.getInst().getName() for t in net.getITerms()})
    assert names and not any(b.findInst(n).getMaster().isBlock() for n in names)
    points=[center(rect(b.findInst(n).getBBox())) for n in names]
    return (max(p[0] for p in points)-min(p[0] for p in points)+
            max(p[1] for p in points)-min(p[1] for p in points))/dbu
before_proxy={};actual_proxy={};incident_readback={}
for name in sorted(incident_names):
    original_net,current_net=reference.findNet(name),block.findNet(name)
    assert original_net is not None and current_net is not None
    current_record=native_incident(current_net);old_record=native_incident(original_net)
    declared=policy['incident_net_inventory'][name]
    declared={'sig_type':declared['sig_type'],'ports':declared['ports'],
        'terminals':sorted(declared['terminals'],key=lambda t:(t['instance'],t['pin'],t['io_type']))}
    assert current_record==old_record==declared,(name,'Incident terminal inventory mismatch')
    before_proxy[name]=hpwl(original_net,reference);actual_proxy[name]=hpwl(current_net,block)
    incident_readback[name]=current_record
proxy_policy=policy['full_incident_HPWL_proxy_um']
assert sorted(incident_names)==sorted(proxy_policy['net_names'])
assert proxy_policy['final_must_equal_seed'] is True and proxy_policy['final_must_improve_total'] is True
for name in incident_names:
    assert abs(before_proxy[name]-proxy_policy['before_per_net'][name])<=1e-7
    assert abs(actual_proxy[name]-proxy_policy['seed_per_net'][name])<=1e-7,(name,'Exact frozen incident HPWL changed')
before_total=sum(before_proxy.values());actual_total=sum(actual_proxy.values())
assert abs(before_total-proxy_policy['before_total'])<=1e-7
assert abs(actual_total-proxy_policy['seed_total'])<=1e-7
assert before_total>actual_total
assert abs((before_total-actual_total)-proxy_policy['improvement'])<=1e-7
full_incident_proxy={'net_names':sorted(incident_names),'before_per_net':before_proxy,'actual_per_net':actual_proxy,
    'before_total':before_total,'actual_total':actual_total,'improvement':before_total-actual_total,
    'actual_equals_frozen_seed':True,'total_improved':True,
    'metric':'Unique incident-net sum of instance-center HPWL; placement proxy only, not routed length or delay.'}
moved=[];actual_allowed=[]
for name,old in old_cells.items():
    current=current_cells[name]
    assert all(current[k]==old[k] for k in ('master','placement_status','group','region','terminals')),(name,'Immutable cell attribute changed')
    changed=any(current[k]!=old[k] for k in ('origin_dbu','bbox_dbu','orientation'))
    if name not in allowed or name in declared_clock:
        assert current==old,(name,'Protected placement changed')
    if changed:moved.append(name)
    if name in allowed:actual_allowed.append({'instance':name,'source':old,'candidate':current,'placement_changed':changed})
assert set(moved)==allowed,'Both and only the frozen buffers must move'
report={'status':'measured','macros':result,
        'actual_TT_signal_pins_match_reference':43,'TT_signal_pin_geometry_sha256':fingerprint(actual_signal_pins),
        'policy_sha256':hashlib.sha256((ROOT/'policy.json').read_bytes()).hexdigest(),
        'unchanged_special_wire_via_boundary_geometry':True,
        'grid_geometry_sha256':fingerprint(current_grid),'grid_counts':current_counts,'reference_grid_counts':old_counts,
        'movement_gate_passed':True,'allowed_instance_names':sorted(allowed),'moved_instance_names':sorted(moved),
        'actual_allowed_instances':sorted(actual_allowed,key=lambda x:x['instance']),
        'whole_instance_count':len(current_cells),'whole_net_count':len(list(block.getNets())),
        'masters_unchanged':True,'net_connectivity_unchanged':True,'placement_statuses_restored':True,
        'rows_regions_groups_unchanged':True,'outside_allowlist_placement_unchanged':True,
        'protected_clock_instance_names':sorted(declared_clock),'clock_tree_unchanged':True,
        'native_CLOCK_net_member_names':sorted(clock_net_members),
        'routing_rules_and_blockages_unchanged':True,'immutable_DEF_sections_sha256':fingerprint(candidate_def),
        'full_technology_LEF_geometry_and_rules_unchanged':True,
        'technology_names':sorted(candidate_tech),
        'native_technology_LEF_sha256':{n:v['native_bytes_sha256'] for n,v in candidate_tech.items()},
        'reference_native_technology_LEF_sha256':{n:v['native_bytes_sha256'] for n,v in reference_tech.items()},
        'all_frozen_member_windows_and_drift_bounds_met':True,'member_constraint_readback':member_constraints,
        'two_buffer_exact_targets_retained':True,'incident_net_inventory':incident_readback,
        'full_incident_HPWL_proxy_um':full_incident_proxy,
        'immutable_layout_sha256':fingerprint(immutable_layout(block)),
        'source_cells_sha256':fingerprint(old_cells),'candidate_cells_sha256':fingerprint(current_cells),
        'boundary':'Fresh native movement/readback against exact repaired R0 source. Only frozen allowed origin/bbox/orientation changes admitted; all statuses/masters/topology/clock placements/rows/groups/regions/fixed pins/power unchanged. No mutation, extracted timing, DRC/LVS or signoff.'}
(ROOT/'metadata.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'metadata':'passed','movement_gate':True,'moved_instances':len(moved),'unchanged_power_geometry':True},sort_keys=True))

