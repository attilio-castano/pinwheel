import json,hashlib,os,shutil,subprocess
from pathlib import Path
from librelane.common import get_script_dir
from segments import roundtrip
R=Path('/work/diagnostic'); scripts=Path(get_script_dir()); I=json.loads((R/'inputs.json').read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for name,expected in I['native_script_sha256'].items():assert sha(scripts/name)==expected,(name,'native script changed')
entry=I['corners'][0];corner=entry['name'];libs=' '.join(str(R/name) for name in entry['libs'])
env_text=('source /work/diagnostic/baseline-env.tcl\nforeach key [array names ::env _LIB_CORNER_*] {unset ::env($key)}\nforeach key [array names ::env *SPEF*] {unset ::env($key)}\nforeach key [array names ::env *SDF*] {unset ::env($key)}\nset ::env(CURRENT_ODB) /work/diagnostic/checkpoint.odb\nset ::env(_SDC_IN) /work/diagnostic/core.sdc\nset ::env(_LIB_CORNER_0) {'+corner+' '+libs+'}\nset ::env(_PNR_EXCLUDED_CELLS) {}\nset ::env(OPENROAD_THREADS) 3\n')
(R/'corner-env.tcl').write_text(env_text)
env=dict(os.environ,SCRIPTS_DIR=str(scripts),_TCL_ENV_IN=str(R/'corner-env.tcl'),PINWHEEL_TIMING_ROOT=str(R))
with (R/'native.log').open('w') as log: result=subprocess.run(['openroad','-exit','-threads','3','-no_splash',str(R/'capture.tcl')],env=env,cwd=R,stdout=log,stderr=subprocess.STDOUT)
assert result.returncode==0,result.returncode
log=(R/'native.log').read_text();assert log.count('PINWHEEL_PINRC_READONLY_EXPORT_FINISHED')==1
assert not any(x in log for x in ['[ERROR','EST-0025','EST-0026','EST-0350'])
assert sha(R/'estimated.spef')==I['original_spef_sha256'],'Fresh uncorrected native SPEF differs from exact qualified export'
assert sha(R/'timing-before.v')==sha(R/'timing-after.v')==I['netlist_sha256']
assert sha(R/'timing-input.def')==sha(R/'timing-after.def'),'Native physical DEF changed'
assert roundtrip(R/'after_grt.segments',R/'imported.segments')==roundtrip(R/'after_grt.segments',R/'after-timing.segments')
assert sha(R/'ndr-before-import.txt')==sha(R/'ndr-after-import.txt')
(R/'measurement.json').write_text(json.dumps(dict(status='measured',readonly_native_capture_passed=True,original_spef_exactly_reproduced=True,netlist_unchanged=True,canonical_DEF_unchanged=True,all_route_segments_unchanged=True,DBNDR_unchanged=True),indent=2)+'\n')
