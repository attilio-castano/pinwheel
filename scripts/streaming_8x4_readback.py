"""Bounded exact8x4 ODB/PDN readback and independent unchanged official Pincheck.

Native readback runs only in OpenROAD's embedded Python under Root's CAD lease.
Pincheck is a separate execution using an inventoried official support snapshot.
Neither result is full DRC/LVS/connectivity/timing or tapeout qualification.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

from streaming_8x4_geometry import DIE, CORE, Grid, admit, clearance, regular, require, sha, validate_power_ports

OFFICIAL = {
    'pin_check.py': '276bfb85dae4078039b15fc13fe4ae0647e10eb34d5cdb2d6edb7bc176e27d39',
    'tech_data.py': '01c72c24c0f62f0a94818b0bcd044efae43f2cc4b1b6d9e8dadcf75bffb10e6d',
    'precheck_failure.py': 'da88e75a22052948f4d8bd3abba4f6f2a608acd232ccea94df1a1b6728c45990'}


def write(path, value):
    Path(path).write_text(json.dumps(value,indent=2,allow_nan=False)+'\n')


def native(odb_path, inputs, output):
    import odb
    odb_path,inputs = regular(odb_path),Path(inputs).absolute()
    output = Path(output).absolute()
    require(not output.exists(), 'Preserve earlier8x4 readback')
    geometry = admit(inputs/'tt_block_8x4_pgvdd.def',inputs/'allocation.json')
    frozen = {str(path):sha(path) for path in (odb_path,inputs/'tt_block_8x4_pgvdd.def',inputs/'allocation.json',inputs/'pdn.tcl')}
    db = odb.read_db(odb.dbDatabase.create(),str(odb_path))
    block = db.getChip().getBlock()
    die = block.getDieArea()
    require(block.getDbUnitsPerMicron() == 1000 and [die.xMin(),die.yMin(),die.xMax(),die.yMax()] == list(DIE),
            'Actual native8x4 die differs')
    core=block.getCoreArea()
    require([core.xMin(),core.yMin(),core.xMax(),core.yMax()]==list(CORE),'Actual native8x4 core extent differs')
    expected = geometry['public_pins_dbu']
    public,ports,power = {},[],[]
    for term in block.getBTerms():
        boxes = [box for pin in term.getBPins() for box in pin.getBoxes()]
        if str(term.getSigType()) in ('POWER','GROUND'):
            for box in boxes:
                ports.append(dict(net=term.getName(),layer=box.getTechLayer().getName(),
                    bounds_dbu=[box.xMin(),box.yMin(),box.xMax(),box.yMax()]))
        else:
            name = term.getName()
            require(name in expected and name not in public and len(boxes) == 1 and
                    boxes[0].getTechLayer().getName() == 'Metal4', 'Wrong native8x4 public-pin membership/layer')
            box = boxes[0]
            actual = [box.xMin(),box.yMin(),box.xMax(),box.yMax()]
            direction = 'INPUT' if name in {'clk','ena','rst_n'} or name.startswith(('ui_in[','uio_in[')) else 'OUTPUT'
            require(actual == expected[name] and str(term.getIoType()) == direction, 'Native8x4 public pin differs: '+name)
            public[name] = actual
    require(public == expected, 'Missing native8x4 public pin')
    grid = Grid(**geometry['grid_dbu'])
    port_result = validate_power_ports(ports,grid)
    for net in block.getNets():
        if str(net.getSigType()) not in ('POWER','GROUND'): continue
        for wire in net.getSWires():
            for box in wire.getWires():
                if box.isVia() or box.getTechLayer().getName() == 'Metal4':
                    power.append(dict(net=net.getName(),kind='via_all_layers_bbox' if box.isVia() else 'Metal4_wire',
                        bounds_dbu=[box.xMin(),box.yMin(),box.xMax(),box.yMax()]))
    require(power, 'Missing native8x4 power geometry')
    minimum = min(clearance(row['bounds_dbu'],pin) for row in power for pin in expected.values())
    require(minimum >= grid.public_clearance, 'Actual8x4 power/via bounds violate public-pin clearance')
    masters = {}
    for instance in block.getInsts():
        name = instance.getMaster().getName()
        masters[name] = masters.get(name,0)+1
    require(all(sha(path) == expected_hash for path,expected_hash in frozen.items()), 'Native8x4 readback input changed')
    report = dict(schema='pinwheel.streaming-8x4-native-geometry.v1', completed=True,die_dbu=list(DIE),core_dbu=list(CORE),
        input_sha256=frozen, public_pins_dbu=public,power_ports=ports,power_geometry=power,
        power_port_result=port_result,minimum_actual_public_clearance_dbu=minimum,
        instance_count=sum(masters.values()),master_counts=masters, qualified=False,physical_acceptance=False,
        routed_connectivity_proved=False,boundary='Actual8x4 geometry and power/public-pin clearance only.')
    write(output,report)
    return report


def pincheck(gds,lef,template,allocation,top,support,output):
    import gdstk
    require(sys.version_info[:2] == (3,12) and sys.flags.optimize == 0 and gdstk.__version__ == '0.9.52',
            'Use unoptimized official Python3.12/gdstk0.9.52')
    support = Path(support).absolute()
    for name,expected in OFFICIAL.items():
        require(sha(regular(support/name)) == expected, 'Official Pincheck source changed: '+name)
    gds,lef,template = map(regular,(gds,lef,template))
    geometry=admit(template,allocation)
    frozen = {str(path):sha(path) for path in (gds,lef,template)}
    output = Path(output).absolute();require(not output.exists(), 'Preserve earlier official8x4 Pincheck')
    require(top == 'tt_um_pinwheel_streaming_ready_d2', 'Wrong certified8x4 top')
    sys.path.insert(0,str(support))
    import pin_check
    require(Path(pin_check.__file__).resolve() == (support/'pin_check.py').resolve(), 'Unexpected Pincheck import')
    pin_check.pin_check(str(gds),str(lef),str(template),top,False,'ihp-sg13cmos5l')
    require(all(sha(path) == value for path,value in frozen.items()), 'Official8x4 Pincheck input changed')
    for name,expected in OFFICIAL.items(): require(sha(support/name) == expected,'Official Pincheck source changed during run')
    result = dict(schema='pinwheel.streaming-8x4-official-pincheck.v1',official_pincheck_passed=True,
        input_sha256=frozen,official_source_sha256=OFFICIAL,support_commit='d66cf179e7bc4d296362ab7e2e3b344dc3c4f665',
        allocation_sha256=geometry['allocation_sha256'],template_sha256=geometry['template_sha256'],
        qualified=False,physical_acceptance=False,full_official_precheck_completed=False)
    write(output,result)
    return result


def gds_geometry(gds,template,allocation,output):
    import gdstk
    require(gdstk.__version__=='0.9.52','Use pinned officialgdstk0.9.52')
    gds,template,allocation=map(regular,(gds,template,allocation))
    output=Path(output).absolute();require(not output.exists(),'Preserve earlier8x4 GDS observation')
    expected=admit(template,allocation)
    frozen={str(path):sha(path) for path in (gds,template,allocation)}
    library=gdstk.read_gds(gds)
    require(library.unit==1e-6 and library.precision==1e-9,'Unexpected8x4 GDS units/precision')
    tops=[cell for cell in library.cells if cell.name=='tt_um_pinwheel_streaming_ready_d2']
    require(len(tops)==1,'Missing/duplicate8x4 top')
    top=tops[0]
    polygons=top.get_polygons(apply_repetitions=True,include_paths=True,depth=0)
    def bounds(polygon):return [*polygon.bounding_box()[0],*polygon.bounding_box()[1]]
    def near(left,right):return len(left)==len(right) and all(abs(a-b)<=1e-6 for a,b in zip(left,right))
    boundaries=[polygon for polygon in polygons if (polygon.layer,polygon.datatype)==(189,4)]
    corners=[[0.,0.],[0.,710.64],[1724.16,710.64],[1724.16,0.]]
    require(len(boundaries)==1 and near(bounds(boundaries[0]),[0.,0.,1724.16,710.64]) and
        abs(boundaries[0].area()-1724.16*710.64)<=1e-6 and len(boundaries[0].points)==4 and
        all(sum(near(point,corner) for point in boundaries[0].points)==1 for corner in corners),
        'GDS lacks exact official8x4 four-corner prBoundary189/4')
    shapes=[bounds(polygon) for polygon in polygons if (polygon.layer,polygon.datatype)==(50,2)]
    pins={}
    for name,dbu_bounds in expected['public_pins_dbu'].items():
        box=[value/1000 for value in dbu_bounds]
        center=[(box[0]+box[2])/2,(box[1]+box[3])/2]
        labels=[label for label in top.labels if label.text==name]
        require(len(labels)==1 and labels[0].layer==50 and labels[0].texttype==25 and
            near(labels[0].origin,center) and any(near(shape,box) for shape in shapes),
            'Wrong exact8x4 GDS public pin/label: '+name)
        pins[name]=dict(bounds_um=box,center_um=center)
    require(all(sha(path)==value for path,value in frozen.items()),'8x4 GDS observation inputs changed')
    result=dict(schema='pinwheel.streaming-8x4-gds-geometry.v1',exact_official_8x4_prBoundary_189_4=True,
        exact43_public_pins_and_labels=True,pins=pins,input_sha256=frozen,unit=library.unit,precision=library.precision,
        qualified=False,physical_acceptance=False,routed_connectivity_proved=False,full_official_precheck_completed=False)
    write(output,result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode',required=True)
    native_parser = sub.add_parser('native')
    for name in ('odb','inputs','output'): native_parser.add_argument('--'+name,type=Path,required=True)
    official = sub.add_parser('pincheck')
    for name in ('gds','lef','template','allocation','support','output'): official.add_argument('--'+name,type=Path,required=True)
    official.add_argument('--top',default='tt_um_pinwheel_streaming_ready_d2')
    gds_parser=sub.add_parser('gds')
    for name in ('gds','template','allocation','output'):gds_parser.add_argument('--'+name,type=Path,required=True)
    args = parser.parse_args()
    if args.mode=='native':result=native(args.odb,args.inputs,args.output)
    elif args.mode=='pincheck':result=pincheck(args.gds,args.lef,args.template,args.allocation,args.top,args.support,args.output)
    else:result=gds_geometry(args.gds,args.template,args.allocation,args.output)
    print(json.dumps(dict(schema=result['schema'],physical_acceptance=False)))


if __name__ == '__main__': main()
