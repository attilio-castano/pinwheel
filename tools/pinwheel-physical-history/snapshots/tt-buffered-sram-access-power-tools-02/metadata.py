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
    assert str(inst.getOrient())=='MX',inst.getOrient()
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
            transformed=sorted([[x+a,y+height-d,x+c,y+height-b] for a,b,c,d in local])
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
    assert all(r[3]==bbox[3] for r in signal_geometries)
    result[inst.getName()]={'bbox_dbu':bbox,'master':master.getName(),'orientation':'MX',
                           'signal_rectangles':342,'all_signal_rectangles_touch_north_edge':True,
                           'supply_contacts':contacts}
current_grid,current_counts=grid_inventory(block);old_grid,old_counts=grid_inventory(reference)
assert current_grid==old_grid,'Supply special-wire/via/boundary geometry changed'
report={'status':'measured','macros':result,'unchanged_special_wire_via_boundary_geometry':True,
        'grid_geometry_sha256':fingerprint(current_grid),'grid_counts':current_counts,
        'reference_grid_counts':old_counts,'boundary':'Native OpenDB macro orientation, exact footprint, transformed loaded Metal4 supply contacts and unchanged complete supply wire/via/boundary geometry. No DRC, IR drop or current capacity claim.'}
(ROOT/'metadata.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'metadata':'passed','macro_orientations':['MX','MX'],'unchanged_power_geometry':True},sort_keys=True))
