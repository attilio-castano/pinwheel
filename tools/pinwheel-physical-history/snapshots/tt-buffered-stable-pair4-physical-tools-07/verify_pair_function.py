import ast,copy,hashlib,json,re,sys,time
from pathlib import Path
H=Path(__file__).resolve().parent;ROOT=H.parents[2];sys.path.insert(0,str(H));sys.path.insert(0,str(H/'identity'))
from pair_function_gate import validate_pair_function
from physical_routed_repair import compare_repair
from physical_organization import Library
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
start=time.monotonic();source=ROOT/'build/physical/tt-buffered-stable-pair4-physical-route-03/control';inv=json.loads((source/'native-inventory.json').read_text());pair=json.loads((H/'pair-policy.json').read_text());plan=json.loads((H/'plan.json').read_text())
gate=(H/'gate.py').read_text();node=next(n for n in ast.parse(gate).body if isinstance(n,ast.FunctionDef) and n.name=='signal_module');space={};exec(ast.get_source_segment(gate,node),space);before=space['signal_module'](inv);after=copy.deepcopy(before)
actual_v=(source/'after.v').read_text();derived_v=actual_v
for name,row in pair['resizes'].items():
    assert before['cells'][name]['type']==row['before'];after['cells'][name]['type']=row['after']
    pattern=r'(?m)^(\s*)'+re.escape(row['before'])+r'(\s+'+re.escape(name)+r'\s*\()'
    derived_v,count=re.subn(pattern,lambda m:m[1]+row['after']+m[2],derived_v);assert count==1
    found=re.search(re.escape(row['before'])+r'\s+'+re.escape(name)+r'\s*\((.*?)\);',actual_v,re.S);assert found
    connections=dict(re.findall(r'\.(\w+)\s*\(\s*(\S+?)\s*\)',found[1]));expected={p:n for p,n,d in inv['instances'][name]['terminals'] if n not in ('VPWR','VGND')};assert connections==expected
assert len(before['cells'])==len(after['cells']);(H/'host-derived-after.v').write_text(derived_v)
texts={c:[(H/'lib'/Path(v['path']).name).read_text()] for c,v in plan['liberty'].items()};proof=compare_repair(before,after,Library(texts),list(texts),allow_resizing=True);expected={n:{'before':r['before'],'after':r['after']} for n,r in pair['resizes'].items()};validate_pair_function(proof,expected,len(before['cells']))
negative=[]
for label,key,value in [('adds','added_instances',['unallowed']),('count','original_cells',len(before['cells'])-1),('identity','normalized_signal_identity',False),('functioncheck','pinned_resize_functions_checked',False),('cohort','resized_cells',{}),('truth_type','normalized_signal_identity',1)]:
    bad=copy.deepcopy(proof);bad[key]=value
    try:validate_pair_function(bad,expected,len(before['cells']))
    except AssertionError:negative.append(label)
    else:raise AssertionError('Bad proof admitted: '+label)
for label,bad in [('missing', {k:v for k,v in proof.items() if k!='added_instances'}),('rewired_schema',{**proof,'added_cells':{}})]:
    try:validate_pair_function(bad,expected,len(before['cells']))
    except AssertionError:negative.append(label)
    else:raise AssertionError('Bad schema admitted: '+label)
receipt={'schema':'pinwheel-buffered-tt-pair-resize-consumer-verification-v1','status':'passed','physical_CAD_executed':False,'actual_saved_source':'03/control/after.v and native-inventory.json','after_fixture_is_derived_not_native_export':True,'native_after_export_was_not_saved_in_failed03':True,'source_signal_module_cell_count':len(before['cells']),'actual_pinned_compare_repair_three_corners':list(texts),'actual_returned_proof':proof,'strict_consumer_positive_passed':True,'negative_cases_rejected':negative,'elapsed_seconds':round(time.monotonic()-start,3),'source_sha256':{str(p):sha(p) for p in [source/'after.v',source/'native-inventory.json',H/'gate.py',H/'identity/physical_routed_repair.py',H/'pair_function_gate.py',H/'pair-policy.json',H/'verify_pair_function.py',*[H/'lib'/Path(v['path']).name for v in plan['liberty'].values()]]},'derived_after_netlist_sha256':sha(H/'host-derived-after.v')};(H/'pair-function-verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({'status':receipt['status'],'proof':proof,'negative_count':len(negative),'elapsed':receipt['elapsed_seconds']}))
