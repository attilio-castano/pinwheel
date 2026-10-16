"""Meaningful host-only frozen-plan and signal identity controls."""
import ast,hashlib,json,sys
from copy import deepcopy
from pathlib import Path
H=Path(__file__).resolve().parent;R=H.parents[2]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=json.loads((H/'plan.json').read_text());b=json.loads((R/p['source_native_inventory']).read_text())
mod=ast.parse((H/'gate.py').read_text());space={'deepcopy':deepcopy}
body=[n for n in mod.body if isinstance(n,ast.FunctionDef) and n.name in ('expected','signal_module','validate_geometry')]
exec(compile(ast.Module(body=body,type_ignores=[]),str(H/'gate.py'),'exec'),space)
a=space['expected'](b,p);space['validate_geometry'](a,p)
sys.path.insert(0,str(H/'identity'))
from physical_routed_repair import compare_repair
from physical_organization import Library
lib=Library({c:[(H/'lib'/Path(v['path']).name).read_text()] for c,v in p['liberty'].items()})
old,new=space['signal_module'](b),space['signal_module'](a)
proof=compare_repair(old,new,lib,list(p['liberty']),allow_resizing=True)
assert len(proof['added_cells'])==8 and len(proof['resized_cells'])==2
controls=['exact2resizes8additions','native_row_site_orientation_hostlegal','zero_existing_neighbor_overlaps','originalCLOCKnets_exact','all_corner_transport_contracted_identity']
assert {n:v for n,v in b['nets'].items() if v['sig_type']=='CLOCK'}=={n:v for n,v in a['nets'].items() if v['sig_type']=='CLOCK'}
def rejection(q,label):
 try:compare_repair(old,q,lib,list(p['liberty']),allow_resizing=True)
 except ValueError:controls.append(label);return
 raise AssertionError('Unsafe edit accepted: '+label)
q=deepcopy(new);name=p['added_instances'][0];q['cells'][name]['type']='sg13cmos5l_nand2_1';rejection(q,'nontransport_cell_rejected')
q=deepcopy(new);ep=p['additions'][0]['endpoint'];other=p['additions'][1]['endpoint'];q['cells'][ep]['connections']['Q']=q['cells'][other]['connections']['Q'];rejection(q,'unselected_original_Q_rewire_rejected')
q=deepcopy(new);q['cells'].pop('_30685_');rejection(q,'removed_original_register_rejected')
q=deepcopy(new);q['cells']['_18965_']['type']='sg13cmos5l_nand3_2';rejection(q,'resize_function_family_change_rejected')
q=deepcopy(new);q['cells'][name]['connections']['A']=q['cells'][name]['connections']['X'];rejection(q,'transport_cycle_rejected')
receipt={'schema':'pinwheel-buffered-tt-timing-eco-host-controls-v1','status':'passed','controls_passed':len(controls),'controls':controls,'all_corner_native_signal_model_proof':proof,'plan_sha256':sha(H/'plan.json'),'source_inventory_sha256':sha(R/p['source_native_inventory']),'source_sha256':{str(x.relative_to(R)):sha(x) for x in [H/'host_controls.py',H/'gate.py',H/'plan.json',*[z for z in sorted((H/'identity').glob('*.py'))],*[z for z in sorted((H/'lib').glob('*.lib'))]]},'boundary':'Host synthetic controls and pinned library identity; does not execute native ECO or establish timing.'}
(H/'structural-controls.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({'controls':len(controls),'receipt_sha256':sha(H/'structural-controls.json'),'proof':proof},indent=2))
