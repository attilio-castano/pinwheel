"""Native immutable candidate macro/contact and supply-grid readback."""
import hashlib
import json
from pathlib import Path
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
policy=json.loads((ROOT/'policy.json').read_text())
fences=[];seen=set();fence_errors=[]
def require_fence(condition,message):
    if not condition:fence_errors.append(message)
    return condition
def net_drivers(net):
    if net is None:return []
    return sorted([{'instance':t.getInst().getName(),'pin':t.getMTerm().getName(),
                    'master':t.getInst().getMaster().getName()}
                   for t in net.getITerms() if str(t.getMTerm().getIoType())=='OUTPUT'],
                  key=lambda item:(item['instance'],item['pin']))
for entry in policy['regions']:
    region=next((r for r in block.getRegions() if r.getName()==entry['region_name']),None)
    group=next((g for g in block.getGroups() if g.getName()==entry['group_name']),None)
    if not require_fence(region is not None and group is not None,entry['macro']+': missing region/group'):
        fences.append({'macro':entry['macro'],'region_name':entry['region_name'],
                       'group_name':entry['group_name'],'present':False});continue
    require_fence(str(region.getRegionType())==entry['odb_region_type']=='EXCLUSIVE',entry['macro']+': wrong region type')
    require_fence(str(group.getType())==entry['odb_group_type']=='PHYSICAL_CLUSTER',entry['macro']+': wrong group type')
    require_fence(group.getRegion()==region,entry['macro']+': group detached from region')
    boundaries=sorted(rect(b) for b in region.getBoundaries())
    require_fence(boundaries==[entry['bbox_dbu']],entry['macro']+': region boundary changed')
    selected={m['instance'] for m in entry['members']}
    assert len(selected)==6
    actual_group={i.getName() for i in group.getInsts()}
    require_fence(selected.issubset(actual_group),entry['macro']+': selected members missing from group')
    members=[]
    for expected_member in entry['members']:
        name=expected_member['instance'];assert name not in seen;seen.add(name)
        inst=block.findInst(name)
        if not require_fence(inst is not None,name+': selected instance removed'):
            members.append({'instance':name,'survives':False});continue
        require_fence(not inst.getMaster().isBlock(),name+': unexpected macro master')
        require_fence(inst.getGroup()==group and inst.getGroup().getRegion()==region,name+': membership changed')
        require_fence(inst.isPlaced(),name+': not placed')
        box=rect(inst.getBBox());fence=entry['bbox_dbu']
        contained=fence[0]<=box[0]<box[2]<=fence[2] and fence[1]<=box[1]<box[3]<=fence[3]
        require_fence(contained,name+': final bbox outside fence')
        output=inst.findITerm(expected_member['output_pin'])
        actual_outputs=[{'pin':t.getMTerm().getName(),'net':t.getNet().getName() if t.getNet() else None}
                        for t in inst.getITerms() if str(t.getMTerm().getIoType())=='OUTPUT']
        macro=block.findInst(entry['macro']);assert macro is not None
        sink=macro.findITerm(expected_member['macro_pin']);assert sink is not None
        output_net=output.getNet() if output is not None else None
        sink_net=sink.getNet()
        direct=output_net is not None and output_net==sink_net
        members.append({'instance':name,'master':inst.getMaster().getName(),
                        'pregpl_master':expected_member['pregpl_master'],
                        'reference_postcts_master':expected_member['reference_postcts_master'],
                        'bbox_dbu':box,'orientation':str(inst.getOrient()),
                        'placement_status':str(inst.getPlacementStatus()),
                        'group':group.getName(),'region':region.getName(),
                        'survives':True,'output_pin':expected_member['output_pin'],
                        'original_policy_net':expected_member['net'],
                        'actual_selected_output_net':output_net.getName() if output_net else None,
                        'actual_output_terminals':actual_outputs,
                        'macro':entry['macro'],'macro_pin':expected_member['macro_pin'],
                        'actual_macro_terminal_net':sink_net.getName() if sink_net else None,
                        'actual_selected_output_net_drivers':net_drivers(output_net),
                        'actual_macro_terminal_net_drivers':net_drivers(sink_net),
                        'direct_tail_preserved':direct,
                        'original_policy_net_name_preserved':output_net is not None and output_net.getName()==expected_member['net'],
                        'fully_inside_fence':contained})
    fences.append({'region_name':region.getName(),'region_type':str(region.getRegionType()),
                   'group_name':group.getName(),'group_type':str(group.getType()),
                   'bbox_dbu':entry['bbox_dbu'],'actual_boundaries_dbu':boundaries,
                   'member_count':len(members),'actual_group_member_count':len(actual_group),
                   'extra_native_group_members':sorted(actual_group-selected),'members':members})
require_fence(len(fences)==2 and len(seen)==12,'Not all twelve selected members read back exactly once')
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
report={'status':'measured','macros':result,'placement_fences':fences,
        'twelve_address_driver_members_survive_within_fences':not fence_errors,
        'placement_fence_errors':fence_errors,
        'selected_direct_tail_preservation_all':len(seen)==12 and all(m.get('direct_tail_preserved',False) for f in fences for m in f.get('members',[])),
        'actual_TT_signal_pins_match_reference':43,'TT_signal_pin_geometry_sha256':fingerprint(actual_signal_pins),
        'policy_sha256':hashlib.sha256((ROOT/'policy.json').read_bytes()).hexdigest(),
        'unchanged_special_wire_via_boundary_geometry':True,
        'grid_geometry_sha256':fingerprint(current_grid),'grid_counts':current_counts,
        'reference_grid_counts':old_counts,'boundary':'Native OpenDB macro orientation, exact footprint, transformed loaded Metal4 supply contacts and unchanged complete supply wire/via/boundary geometry. No DRC, IR drop or current capacity claim.'}
(ROOT/'metadata.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'metadata':'passed','macro_orientations':['R0','R0'],'unchanged_power_geometry':True},sort_keys=True))
