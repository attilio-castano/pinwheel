import json,hashlib,subprocess,glob
from pathlib import Path
root=Path('/work/diagnostic');binary=Path('/nix/store/c60x0zn4vxd3h2mybmg8i7q55y95i3a6-openroad-2026-02-17/bin/.openroad-wrapped')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(binary)=='6ba87b45c762ee8c9670375c204cd03d801a6da98cd6e056a1c73027aad68a7c'
def find(name):
 paths=sorted(glob.glob('/nix/store/*/bin/'+name));assert paths,name;return paths[0]
nm=find('nm');obj=find('objdump');readelf=find('readelf')
def run(args,name):
 p=subprocess.run(args,capture_output=True,text=True,timeout=30);(root/name).write_text(p.stdout+p.stderr);assert p.returncode==0,(args,p.stderr);return p.stdout
syms=run([nm,'-D','--defined-only',str(binary)],'native-dynamic-symbols.txt')
selected=[s.split()[-1] for s in syms.splitlines() if 'processWorkersBatch' in s and 'Distributed' not in s]
assert len(selected)==1,selected
body=run([obj,'-d','--disassemble='+selected[0],str(binary)],'processWorkersBatch.asm')
run([readelf,'-d',str(binary)],'native-dynamic-section.txt')
record={'status':'measured_binary_only','binary_sha256':sha(binary),'selected_symbol':selected[0],'tools':{p:sha(p) for p in [nm,obj,readelf]},'function_assembly_bytes':len(body),'OMP_tokens_present':[s for s in ['__kmpc_fork_call','GOMP_parallel','omp_get_num_threads'] if s in body],'physical_acceptance':False}
(root/'measurement.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
