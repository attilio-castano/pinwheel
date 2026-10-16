"""Host-only exact new exporter terminal-bin tests; no OpenDB or CAD execution."""
import ast
import hashlib
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent;p=HERE/'export_geometry.py';tree=ast.parse(p.read_text());function=next(f for f in tree.body if isinstance(f,ast.FunctionDef) and f.name=='located_grid_box');namespace={};exec(compile(ast.Module(body=[function],type_ignores=[]),str(p),'exec'),namespace);locate=namespace['located_grid_box']
x=[0,7200,14400];y=[0,7200,14400];die=[0,0,16000,16000]
controls=[]
cases=[('interior nextcoords',0,0,x,y,die,[0,0,7200,7200]),('positive terminal partialbin',2,2,x,y,die,[14400,14400,16000,16000]),('lastcoordinate equalsdieedge',2,2,x,y,[0,0,14400,14400],None),('lastcoordinate beyondactualdie',2,2,x,y,[0,0,14000,14000],None),('interior clipsactualdie',1,1,x,y,[0,0,10000,10000],[7200,7200,10000,10000]),('negativeorigin clipsdie',0,0,[-100,7200],[-100,7200],die,[0,0,7200,7200])]
for label,ix,iy,gx,gy,box,expected in cases:assert locate(ix,iy,gx,gy,box)==expected,label;controls.append(label)
for ix,iy in [(3,0),(0,3),(-1,0)]:
    try:locate(ix,iy,x,y,die)
    except AssertionError:controls.append('invalid index rejected '+str((ix,iy)))
    else:raise AssertionError((ix,iy))
report={'schema':'pinwheel-buffered-tt-sram-access-grid-edge-controls-v1','status':'passed','controls_passed':len(controls),'controls':controls,'actual_exporter_function_executed':True,'exporter_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'controls_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'CAD_run':False,'boundary':'Synthetic host index/actualdie extent cases exercise exact new pureedge function; actualOpenDB grid/die coordinates will be read only in the authorized sourcebound native readback.'};(HERE/'controls.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'status':'passed','controls':len(controls)}))
