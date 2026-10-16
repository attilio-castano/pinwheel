"""Read the replay's saved routing grid and unchanged physical overlays."""
import hashlib,json
from pathlib import Path
import odb
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
a,before=load('postcts.odb');db,block=load('routed.odb');before_inventory=inventory(before);after_inventory=inventory(block)
assert before_inventory==after_inventory,'Placement, cell master or terminal connectivity changed'
assert sha(ROOT/'before.v')==sha(ROOT/'after.v'),'Exported netlist changed'
grid=block.getGCellGrid();x=list(grid.getGridX());y=list(grid.getGridY());layers={};context={};dbu=block.getDbUnitsPerMicron()
for name in ['Metal2','Metal3','Metal4']:
 layer=db.getTech().findLayer(name);capacity=[[grid.getCapacity(layer,ix,iy) for iy in range(len(y))] for ix in range(len(x))];usage=[[grid.getUsage(layer,ix,iy) for iy in range(len(y))] for ix in range(len(x))]
 hotspots=[]
 for ix in range(len(x)):
  for iy in range(len(y)):
   if usage[ix][iy]>capacity[ix][iy]:
    assert ix+1<len(x) and iy+1<len(y)
    hotspots.append({'index':[ix,iy],'bbox_dbu':[x[ix],y[iy],x[ix+1],y[iy+1]],'capacity':capacity[ix][iy],'usage':usage[ix][iy],'overflow':usage[ix][iy]-capacity[ix][iy]})
 layers[name]={'capacity':capacity,'usage':usage,'hotspots':hotspots,'overflow':sum(h['overflow'] for h in hotspots),'direction':str(layer.getDirection()),'total_saved_capacity':sum(map(sum,capacity)),'total_saved_usage':sum(map(sum,usage))}
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
result={'schema':'pinwheel-buffered-tt-congestion-geometry-v1','database_sha256':sha(ROOT/'routed.odb'),'dbu_per_micron':dbu,'die_bbox_dbu':rect(block.getDieArea()),'grid_x':x,'grid_y':y,'layers':layers,'macros':macros,'macro_obstructions':macro_obs,'macro_pins':macro_pins,'cells':cells,'power_boxes':power_boxes,'inventory_unchanged':True,'inventory_sha256':fingerprint(after_inventory),'exported_netlist_unchanged':True,'netlist_sha256':sha(ROOT/'after.v'),'boundary':'Fresh saved per-layer overflow plus physical overlays; saved capacity/usage include resource reductions and are not raw routed demand.'}
(ROOT/'geometry.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
print(json.dumps({'layers':{n:{'overflow':r['overflow'],'hotspots':len(r['hotspots'])} for n,r in layers.items()},'inventory_unchanged':True,'netlist_unchanged':True},sort_keys=True))
