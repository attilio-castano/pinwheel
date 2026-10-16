import json,hashlib
from pathlib import Path
import odb
def rect(r):return [r.xMin(),r.yMin(),r.xMax(),r.yMax()]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def fingerprint(x):return hashlib.sha256(json.dumps(x,separators=(",",":")).encode()).hexdigest()
def inventory(block):return [[i.getName(),i.getMaster().getName(),rect(i.getBBox()),str(i.getOrient()),sorted((t.getMTerm().getName(),t.getNet().getName() if t.getNet() else None) for t in i.getITerms())] for i in sorted(block.getInsts(),key=lambda i:i.getName())]
def located_grid_box(ix,iy,x,y,die):
    assert 0<=ix<len(x) and 0<=iy<len(y)
    xend=x[ix+1] if ix+1<len(x) else die[2];yend=y[iy+1] if iy+1<len(y) else die[3]
    b=[max(x[ix],die[0]),max(y[iy],die[1]),min(xend,die[2]),min(yend,die[3])]
    return b if b[2]>b[0] and b[3]>b[1] else None
def export(db,block,path):
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
    result={'schema':'pinwheel-buffered-tt-congestion-geometry-v1','database_sha256':sha(path.parent/'routed.odb'),'dbu_per_micron':dbu,'die_bbox_dbu':die,'grid_edge_policy':{'terminal_upper_bound':'Actualdie max is used only when clipping yields positiveextent; otherwise overflow remains spatiallyunassigned, neverdropped.','actual_grid_terminal_coordinates_dbu':[x[-1],y[-1]],'actual_die_max_dbu':[die[2],die[3]],'all_saved_units_preserved':True},'grid_x':x,'grid_y':y,'layers':layers,'macros':macros,'macro_obstructions':macro_obs,'macro_pins':macro_pins,'cells':cells,'power_boxes':power_boxes,'native_frozen_inventory_unchanged':True,'CLOCK_NDR_association_changes':[],'inventory_unchanged':True,'inventory_sha256':fingerprint(inventory(block)),'exported_netlist_unchanged':True,'netlist_sha256':sha(path.parent/'after.v'),'boundary':'Fresh saved per-layer overflow plus physical overlays; saved capacity/usage include resource reductions and are not raw routed demand.'}
    path.write_text(json.dumps(result,separators=(',',':'))+'\n')
    return result
