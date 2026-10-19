#!/usr/bin/env python3
"""Light exact boundary, layer inventory and official 43-pin geometry readback.

This is a geometry observation of a closed diagnostic export, never the full
official nine-check precheck or evidence of routed connectivity.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

import streaming_tt_gds_diagnostic as G
from streaming_tt_intake import dependency_closure
from streaming_tt_signoff import read,regular,require,sha,unchanged,write
import streaming_tt_physical as P

TEMPLATE_SHA256='b46d9a0ee8352160e48dbc8312f092f985629061df736c7f46d58686535a76f4'


def template_pins(text):
    unit=re.search(r'UNITS DISTANCE MICRONS (\d+) ;',text);require(unit,'Missing template DBU scale')
    unit=int(unit[1]);section=re.search(r'PINS (\d+) ;(.*?)END PINS',text,re.S);require(section,'Missing template pins')
    pattern=r'^\s*- (\S+) \+ NET (\S+).*?\+ LAYER (\S+) \( (-?\d+) (-?\d+) \) \( (-?\d+) (-?\d+) \).*?\+ PLACED \( (-?\d+) (-?\d+) \) (\S+) ;'
    pins={}
    for match in re.finditer(pattern,section[2],re.M|re.S):
        name,net,layer,lx,by,rx,ty,ox,oy,direction=match.groups()
        require(name==net and name not in pins and layer=='Metal4' and direction=='N','Unsupported official pin template')
        lx,by,rx,ty,ox,oy=map(int,(lx,by,rx,ty,ox,oy))
        pins[name]=dict(bounds=[(ox+lx)/unit,(oy+by)/unit,(ox+rx)/unit,(oy+ty)/unit],
            center=[(ox+(lx+rx)/2)/unit,(oy+(by+ty)/2)/unit])
    require(len(pins)==int(section[1])==43,'Incomplete official43-pin template')
    return pins


def near(left,right,tolerance=0.000001):
    return len(left)==len(right) and all(abs(a-b)<=tolerance for a,b in zip(left,right))


def measure(top,polygons,pins):
    boundaries=[polygon for polygon in polygons if (polygon.layer,polygon.datatype)==(189,4)]
    expected=[0.,0.,1289.28,710.64]
    def bounds(polygon):return [*polygon.bounding_box()[0],*polygon.bounding_box()[1]]
    corners=[[0.,0.],[0.,710.64],[1289.28,710.64],[1289.28,0.]]
    points=boundaries[0].points.tolist() if len(boundaries)==1 else []
    exact_boundary=(len(boundaries)==1 and near(bounds(boundaries[0]),expected) and
        abs(boundaries[0].area()-(1289.28*710.64))<=0.000001 and len(points)==4 and
        all(sum(near(point,corner) for point in points)==1 for corner in corners))
    shapes=[bounds(polygon) for polygon in polygons if (polygon.layer,polygon.datatype)==(50,2)]
    rows=[]
    for name,pin in sorted(pins.items()):
        labels=[label for label in top.labels if label.text==name]
        rows.append(dict(name=name,expected=pin,label_count=len(labels),
            exact_label=len(labels)==1 and labels[0].layer==50 and labels[0].texttype==25 and near(labels[0].origin,pin['center']),
            exact_pin_rectangle=any(near(rect,pin['bounds']) for rect in shapes)))
    return dict(exact_official_6x4_prBoundary_189_4=exact_boundary,
        prBoundary_rectangles=[dict(bounds_um=bounds(polygon),area_um2=polygon.area(),vertices=polygon.points.tolist()) for polygon in boundaries],
        all43_template_labels_and_pin_rectangles=len(rows)==43 and all(row['exact_label'] and row['exact_pin_rectangle'] for row in rows),
        pins=rows,top_labels=[dict(text=label.text,layer=label.layer,texttype=label.texttype,origin=list(label.origin)) for label in top.labels],
        direct_polygon_inventory={str(pair):count for pair,count in sorted(Counter((p.layer,p.datatype) for p in polygons).items())})


def run(export_path,template,out):
    import gdstk
    require(gdstk.__version__=='0.9.52' and sys.version.startswith('3.12.'),'Use exact official precheck Python/gdstk runtime')
    export_path,template=map(regular,(export_path,template));packet=read(export_path)
    require(packet.get('schema')=='pinwheel.streaming-tt-gds-view-host.v1' and
        packet.get('status')=='views_exported' and packet.get('view_export_completed') is True and
        packet.get('candidate_flow_completed') is False and packet.get('inputs_unchanged') is True and
        packet.get('runtime_unchanged') is True and packet.get('pdk_unchanged') is True and
        packet.get('container_termination',{}).get('status')=='absent','Diagnostic GDS producer is not closed')
    source=export_path.parent
    actual={str(path.relative_to(source)):sha(path) for path in sorted(source.rglob('*')) if path.is_file() and
        not path.is_relative_to(source/'producer') and path!=export_path}
    require(actual==packet.get('artifact_sha256'),'Actual diagnostic export artifact membership/bytes changed')
    report,roots,odb,database,frozen=G.intake(packet['physical_report'],packet['physical_state'])
    views=G.validate_native(source,read(source/'request.json'),config_path=roots['/work/run']/'resolved.json')
    require(views==packet['streamout'] and sha(database)==packet['actual_database_sha256'],'GDS producer actual ODB changed')
    path=regular(source/views['views']['gds']['relative']);require(sha(path)==views['views']['gds']['sha256'] and
        sha(template)==TEMPLATE_SHA256,'Actual GDS/official6x4 template changed')
    closure=dependency_closure(P.ROOT,['scripts/streaming_tt_gds_geometry.py'])
    producer={name:hashlib.sha256(P.committed(P.ROOT/name)).hexdigest() for name in closure['files']}
    frozen.update({str(value):sha(value) for value in (export_path,path,template)})
    library=gdstk.read_gds(path);tops=[cell for cell in library.cells if cell.name=='tt_um_pinwheel_streaming_ready_d2']
    require(library.unit==1e-6 and library.precision==1e-9,'Unexpected GDS coordinate unit/precision; cannot assert micrometers')
    require(len(tops)==1,'Actual GDS top absent/ambiguous');top=tops[0]
    observed=measure(top,top.get_polygons(apply_repetitions=True,include_paths=True,depth=0),template_pins(template.read_text()))
    unchanged(frozen);require(all(sha(P.ROOT/name)==value for name,value in producer.items()),'Geometry producer changed during use')
    out=Path(out).resolve();out.parent.mkdir(parents=True,exist_ok=True);require(not out.exists(),'Preserve prior geometry observation')
    write(out,dict(schema='pinwheel.streaming-tt-gds-geometry-observation.v1',qualified=False,physical_acceptance_claim=False,
        official_nine_check_precheck_completed=False,routed_connectivity_proved=False,
        producer_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P.ROOT,text=True).strip(),
        producer_sha256=producer,producer_dependency_closure=closure,input_sha256_before=frozen,input_sha256_after=frozen,
        inputs_unchanged=True,stage=Path(packet['physical_state']).parent.name,gds_sha256=sha(path),
        gdstk_version=gdstk.__version__,python_version=sys.version,python_executable_sha256=sha(Path(sys.executable).resolve()),
        unit=library.unit,precision=library.precision,cells=len(library.cells),top_level_cells=[cell.name for cell in library.top_level()],
        top_bbox_um=[list(point) for point in top.bounding_box()],geometry=observed,
        boundary='Actual closed checkpoint GDS boundary/pin/layer observations only. Full official precheck, route/DRC/LVS/antenna/power and extracted timing remain separate.'))
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('gds-export','template','out'):parser.add_argument('--'+name,required=True,type=Path)
    args=parser.parse_args();print(run(args.gds_export,args.template,args.out),flush=True)


if __name__=='__main__':main()
