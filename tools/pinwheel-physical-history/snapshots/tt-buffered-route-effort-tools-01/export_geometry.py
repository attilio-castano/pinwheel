"""Read the replay's saved routing grid and unchanged physical overlays."""
import hashlib,json
from pathlib import Path
import odb
from native_inventory import snapshot as native_snapshot
from route_checks import audit_route
ROOT=Path('/work/diagnostic')
def rect(r):return [r.xMin(),r.yMin(),r.xMax(),r.yMax()]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(name):
 db=odb.dbDatabase.create();odb.read_db(db,str(ROOT/name));return db,db.getChip().getBlock()
def inventory(block):
 return [[i.getName(),i.getMaster().getName(),rect(i.getBBox()),str(i.getOrient()),
          sorted((t.getMTerm().getName(),t.getNet().getName() if t.getNet() else None) for t in i.getITerms())]
         for i in sorted(block.getInsts(),key=lambda i:i.getName())]
def fingerprint(value):return hashlib.sha256(json.dumps(value,separators=(',',':')).encode()).hexdigest()
def located_grid_box(ix, iy, x, y, die):
 assert 0 <= ix < len(x) and 0 <= iy < len(y)
 xend=x[ix+1] if ix+1<len(x) else die[2]
 yend=y[iy+1] if iy+1<len(y) else die[3]
 box=[max(x[ix],die[0]),max(y[iy],die[1]),min(xend,die[2]),min(yend,die[3])]
 if box[2]<=box[0] or box[3]<=box[1]:return None
 return box

a,before=load('postcts.odb');db,block=load('routed.odb');before_inventory=inventory(before);after_inventory=inventory(block)
assert before_inventory==after_inventory,'Placement, cell master or terminal connectivity changed'
assert sha(ROOT/'before.v')==sha(ROOT/'after.v'),'Exported netlist changed'
full_before=native_snapshot(a,before,'before');full_after=native_snapshot(db,block,'after');audit=audit_route(full_before,full_after)
assert sha(ROOT/'postcts.odb')=='95f0fdb260de137d5b4f77669c9aaa5eb3bf56e7dc55f4c9b7d51b2b8a16556e'
(ROOT/'before-inventory.json').write_text(json.dumps(full_before,separators=(',',':'))+'\n')
(ROOT/'after-inventory.json').write_text(json.dumps(full_after,separators=(',',':'))+'\n')
import re
def block_ndr_section(path):
 text=path.read_text();match=re.search(r'^NONDEFAULTRULES\s+\d+\s*;.*?^END NONDEFAULTRULES[ \t]*$',text,re.M|re.S);assert match;return match[0]
initial_ndr=block_ndr_section(ROOT/'before.def');post_ndr=block_ndr_section(ROOT/'routed.def');assert initial_ndr==post_ndr
assert not re.search(r'\+\s+(?:VIA|USEVIA|USEVIARULE)\b',initial_ndr),'Unexpected NDR via list'
audit.update(canonical_block_NDR_DEF_sha256=hashlib.sha256(initial_ndr.encode()).hexdigest(),canonical_block_NDR_DEF_unchanged=True,block_NDR_via_lists_empty=True)
(ROOT/'routing-inventory.json').write_text(json.dumps(audit,indent=2)+'\n')
grid=block.getGCellGrid();x=list(grid.getGridX());y=list(grid.getGridY());layers={};context={};dbu=block.getDbUnitsPerMicron();die=rect(block.getDieArea())
assert all(a<b for a,b in zip(x,x[1:])) and all(a<b for a,b in zip(y,y[1:]))
for name in ['Metal2','Metal3','Metal4']:
 layer=db.getTech().findLayer(name);capacity=[[grid.getCapacity(layer,ix,iy) for iy in range(len(y))] for ix in range(len(x))];usage=[[grid.getUsage(layer,ix,iy) for iy in range(len(y))] for ix in range(len(x))]
 hotspots=[];unassigned=[];all_overflow=0;terminal_bins=0
 for ix in range(len(x)):
  for iy in range(len(y)):
   if usage[ix][iy]>capacity[ix][iy]:
    amount=usage[ix][iy]-capacity[ix][iy];all_overflow+=amount
    item={'index':[ix,iy],'capacity':capacity[ix][iy],'usage':usage[ix][iy],'overflow':amount}
    box=located_grid_box(ix,iy,x,y,die)
    terminal=ix+1==len(x) or iy+1==len(y)
    if box is None:
     unassigned.append({**item,'raw_grid_origin_dbu':[x[ix],y[iy]],'next_grid_coordinate_dbu':[x[ix+1] if ix+1<len(x) else None,y[iy+1] if iy+1<len(y) else None],'reason':'No positive rectangle remains after clipping actual grid coordinates/terminal die bounds to the actual die. Overflow is retained without an invented rectangle.'})
    else:
     hotspots.append({**item,'bbox_dbu':box,'terminal_bin_using_actual_die_edge':terminal})
     terminal_bins+=int(terminal)
 assigned=sum(h['overflow'] for h in hotspots);unlocated=sum(h['overflow'] for h in unassigned)
 assert assigned+unlocated==all_overflow
 layers[name]={'capacity':capacity,'usage':usage,'hotspots':hotspots,'unassigned_edge_hotspots':unassigned,'overflow':all_overflow,'spatial_assigned_overflow':assigned,'unassigned_edge_overflow':unlocated,'terminal_hotspot_bins_using_actual_die_edge':terminal_bins,'direction':str(layer.getDirection()),'total_saved_capacity':sum(map(sum,capacity)),'total_saved_usage':sum(map(sum,usage))}
macros={};macro_obs=[];macro_pins=[];cells=[];power_boxes=[]
for i in block.getInsts():
 master=i.getMaster();bbox=rect(i.getBBox())
 if master.isBlock():
  ox,oy=bbox[:2];macros[i.getName()]={'bbox_dbu':bbox,'master':master.getName(),'orientation':str(i.getOrient())}
  for r in master.getObstructions():
   if r.getTechLayer() and r.getTechLayer().getName() in layers:
    a,b,c,d=rect(r)
    orientation=str(i.getOrient());assert orientation in ('R0','MX'),orientation
    if orientation=='MX':b,d=master.getHeight()-d,master.getHeight()-b
    macro_obs.append({'instance':i.getName(),'layer':r.getTechLayer().getName(),'bbox_dbu':[ox+a,oy+b,ox+c,oy+d]})
  for t in i.getITerms():
   if str(t.getSigType()) in ('POWER','GROUND'):continue
   for layer,r in t.getGeometries():macro_pins.append({'instance':i.getName(),'pin':t.getMTerm().getName(),'net':t.getNet().getName() if t.getNet() else None,'layer':layer.getName(),'bbox_dbu':rect(r)})
 else:cells.append({'name':i.getName(),'master':master.getName(),'bbox_dbu':bbox,'kind':'clock_buffer' if i.getName().startswith(('clkbuf','delaybuf')) else 'repair_buffer' if i.getName().startswith(('fanout','rebuffer','hold','load','buffer','max','slew','wire')) else 'logic'})
for net_name in ['VPWR','VGND']:
 n=block.findNet(net_name)
 for sw in n.getSWires():
  for r in sw.getWires():
   layer=r.getTechLayer()
   if layer is not None:
    if layer.getName() in layers:power_boxes.append({'net':net_name,'layer':layer.getName(),'bbox_dbu':rect(r),'kind':'stripe'})
   else:
    via=r.getBlockVia() or r.getTechVia();vx,vy=r.getViaXY()
    for box in via.getBoxes():
     if box.getTechLayer() and box.getTechLayer().getName() in layers:
      a,b,c,d=rect(box);power_boxes.append({'net':net_name,'layer':box.getTechLayer().getName(),'bbox_dbu':[vx+a,vy+b,vx+c,vy+d],'kind':'via_landing'})
result={'schema':'pinwheel-buffered-tt-congestion-geometry-v1','database_sha256':sha(ROOT/'routed.odb'),'dbu_per_micron':dbu,'die_bbox_dbu':die,'grid_edge_policy':{'terminal_upper_bound':'Actualdie max is used only when clipping yields positiveextent; otherwise overflow remains spatiallyunassigned, neverdropped.','actual_grid_terminal_coordinates_dbu':[x[-1],y[-1]],'actual_die_max_dbu':[die[2],die[3]],'all_saved_units_preserved':True},'grid_x':x,'grid_y':y,'layers':layers,'macros':macros,'macro_obstructions':macro_obs,'macro_pins':macro_pins,'cells':cells,'power_boxes':power_boxes,'native_frozen_inventory_unchanged':True,'CLOCK_NDR_association_changes':audit['CLOCK_NDR_association_changes'],'inventory_unchanged':True,'inventory_sha256':fingerprint(after_inventory),'exported_netlist_unchanged':True,'netlist_sha256':sha(ROOT/'after.v'),'boundary':'Fresh saved per-layer overflow plus physical overlays; saved capacity/usage include resource reductions and are not raw routed demand.'}
(ROOT/'geometry.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
print(json.dumps({'layers':{n:{'overflow':r['overflow'],'hotspots':len(r['hotspots'])} for n,r in layers.items()},'inventory_unchanged':True,'netlist_unchanged':True},sort_keys=True))
