"""Read-only whole OpenDB snapshot and exact local movement gate."""
import hashlib,json,os
from pathlib import Path
import odb
ROOT=Path('/work/diagnostic')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def fingerprint(v):return hashlib.sha256(json.dumps(v,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def rect(v):return [v.xMin(),v.yMin(),v.xMax(),v.yMax()]
def name(v):return v.getName() if v is not None else None
def load(path):
    db=odb.dbDatabase.create();odb.read_db(db,str(path));return db,db.getChip().getBlock()
def snapshot(db,block,prefix):
    tech=db.getTech();instances={};nets={};rows=[];pins=[];power=[];macros={};blockages=[]
    for i in block.getInsts():
        master=i.getMaster();terms=sorted([t.getMTerm().getName(),name(t.getNet()),str(t.getMTerm().getIoType())] for t in i.getITerms())
        instances[i.getName()]={'master':master.getName(),'bbox_dbu':rect(i.getBBox()),'orientation':str(i.getOrient()),'placement_status':str(i.getPlacementStatus()),'width_dbu':master.getWidth(),'height_dbu':master.getHeight(),'macro':master.isBlock(),'terminals':terms,'group':name(i.getGroup()),'region':name(i.getRegion())}
        if master.isBlock():
            macros[i.getName()]={'master':master.getName(),'bbox_dbu':rect(i.getBBox()),'orientation':str(i.getOrient()),'terminals':sorted([t.getMTerm().getName(),str(t.getSigType()),name(t.getNet()),sorted([layer.getName(),rect(box)] for layer,box in t.getGeometries())] for t in i.getITerms())}
    for n in block.getNets():
        nets[n.getName()]={'sig_type':str(n.getSigType()),'ports':sorted(t.getName() for t in n.getBTerms()),'terminals':sorted([t.getInst().getName(),t.getMTerm().getName(),str(t.getMTerm().getIoType())] for t in n.getITerms()),'nondefault_rule':name(n.getNonDefaultRule())}
        for sw in n.getSWires():
            for box in sw.getWires():
                layer=box.getTechLayer()
                if layer is not None:power.append([n.getName(),'metal',layer.getName(),rect(box)])
                else:
                    via=box.getBlockVia() or box.getTechVia();assert via is not None
                    power.append([n.getName(),'via',via.getName(),list(box.getViaXY()),sorted([b.getTechLayer().getName(),rect(b)] for b in via.getBoxes() if b.getTechLayer() is not None)])
    for row in block.getRows():rows.append({'name':row.getName(),'bbox_dbu':rect(row.getBBox()),'orientation':str(row.getOrient()),'origin_dbu':list(row.getOrigin()),'site_width_dbu':row.getSite().getWidth(),'site_height_dbu':row.getSite().getHeight()})
    for term in block.getBTerms():pins.append([term.getName(),str(term.getSigType()),str(term.getIoType()),name(term.getNet()),sorted([box.getTechLayer().getName() if box.getTechLayer() else None,rect(box)] for pin in term.getBPins() for box in pin.getBoxes())])
    for b in block.getBlockages():blockages.append([rect(b.getBBox()),name(b.getInstance()),b.isSoft(),b.isPushedDown(),b.isSystemReserved(),b.getMaxDensity()])
    # Pinned write_tech_lef serializes all TECH rule definitions, including
    # same-net/via/use/mincut fields unavailable through scalar Python getters.
    tech_lef=[]
    for index,t in enumerate(db.getTechs()):
        path=ROOT/(prefix+'-tech-'+str(index)+'.lef');odb.write_tech_lef(t,str(path))
        assert path.is_file();tech_lef.append([t.getName(),sha(path)])
    rules=[];layers=list(tech.getLayers())
    for rule in block.getNonDefaultRules():
        lr=[];same=[]
        for layer in layers:
            r=rule.getLayerRule(layer)
            if r is not None:lr.append([layer.getName(),r.isBlockRule(),r.getWidth(),r.getSpacing(),r.getResistance(),r.getCapacitance(),r.getEdgeCapacitance(),r.getWireExtension()])
        for i,a in enumerate(layers):
            for b in layers[i:]:
                r=rule.findSameNetRule(a,b)
                if r is not None:same.append([r.getLayer1().getName(),r.getLayer2().getName(),r.getSpacing(),r.getAllowStackedVias()])
        rules.append([rule.getName(),rule.isBlockRule(),rule.getHardSpacing(),sorted(lr),sorted(same)])
    assert sorted(r[0] for r in rules)==['CTS_NDR_0','CTS_NDR_1']
    groups=[g.getName() for g in block.getGroups()];regions=[r.getName() for r in block.getRegions()];assert not groups and not regions
    defaults={}
    for layer_name in ('Metal1','Metal2','Metal3','Metal4','TopMetal1'):
        layer=tech.findLayer(layer_name);assert layer is not None
        defaults[layer_name]={'width_dbu':layer.getWidth(),'spacing_dbu':layer.getSpacing(),'direction':str(layer.getDirection())}
    return {'routing_layer_defaults':defaults,'instances':instances,'nets':nets,'rows':sorted(rows,key=lambda r:r['name']),'macros':macros,'pins':sorted(pins),'special_wires':sorted(power),'placement_blockages':sorted(blockages),'nondefault_rules':sorted(rules),'canonical_all_TechLEF_sha256':sorted(tech_lef),'groups':groups,'regions':regions,'die_bbox_dbu':rect(block.getDieArea()),'core_bbox_dbu':rect(block.getCoreArea()),'dbu_per_micron':block.getDbUnitsPerMicron()}
