"""Known-public cache APIs: fresh native state per case, no routing/physical edits."""
import ctypes,hashlib,json,os,shutil,sys
from pathlib import Path
from openroad import Tech,Design
from native_inventory import snapshot
R=Path('/work/diagnostic');case=os.environ['PINWHEEL_CASE'];assert case in ['callback-first','pre-enroll-first'];tech=Tech();design=Design(tech)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def tcl(s):
 r=design.evalTclString('if {[catch {\n'+s+'\n} msg opts]} {puts stderr $msg; exit 2}; set ::pw_ok PINWHEEL_TCL_OK');assert r=='PINWHEEL_TCL_OK',r
def ptr(x):return int(x.this if hasattr(x,'this') else x)
def fn(name,argtypes,restype):
 f=getattr(ctypes.CDLL(None),name);f.argtypes=argtypes;f.restype=restype;return f
exe=Path(os.readlink('/proc/self/exe'));assert sha(exe)=='6ba87b45c762ee8c9670375c204cd03d801a6da98cd6e056a1c73027aad68a7c'
tcl('source /work/diagnostic/load.tcl\nsource $::env(SCRIPTS_DIR)/openroad/common/set_rc.tcl')
BEFORE=snapshot(design.getDb(),design.getBlock(),case+'-before')
tcl('global_route -congestion_iterations 10 -start_incremental')
router=design.getGlobalRouter();destroy=fn('_ZN3grt3Net11destroyPinsEv',[ctypes.c_void_p],None)
update=fn('_ZN3grt12GlobalRouter13updateNetPinsEPNS_3NetE',[ctypes.c_void_p,ctypes.c_void_p],None)
pred=fn('_ZN3grt12GlobalRouter19pinPositionsChangedEPNS_3NetE',[ctypes.c_void_p,ctypes.c_void_p],ctypes.c_bool)
rows=[]
for name in ['_11039_','net913','net914']:
 dbnet=design.getBlock().findNet(name);assert str(dbnet.getSigType())=='SIGNAL' and dbnet.getNonDefaultRule() is None
 native=router.getNet(dbnet)
 if case=='pre-enroll-first':destroy(ptr(native));router.addDirtyNet(dbnet)
 router.addDirtyNet(dbnet);router.addDirtyNet(dbnet) # exact addDirtyNet body invoked by swap-after and post-move callbacks
 before=bool(pred(ptr(router),ptr(native)))
 destroy(ptr(native));router.addDirtyNet(dbnet);update(ptr(router),ptr(native))
 after=bool(pred(ptr(router),ptr(native)));assert after==(case=='pre-enroll-first'),(case,name,after)
 rows.append({'net':name,'cache_order':case,'predicate_before_final_enrollment':before,'unpatched_rebuilt_pin_predicate':after,'emulated_callback_enrollments':2})
AFTER=snapshot(design.getDb(),design.getBlock(),case+'-after');assert BEFORE==AFTER,'Cache fixture changed native inventory'
result={'status':'measured','case':case,'native_binary_sha256':sha(exe),'native_binary_version':design.evalTclString('ord::openroad_version'),'physical_edit_count':0,'routing_solve_count':0,'native_init_only':True,'predicate_unpatched':True,'credit_function_unpatched':True,'native_inventory_before_after_identical':True,'rows':rows,'source_scope':'Cache-order fixture emulates exact callback addDirtyNet body only; actual resized route worklist still requires live exact3-net gate.'}
(R/(case+'-measurement.json')).write_text(json.dumps(result,indent=2)+'\n');print('PINWHEEL_CACHE_ORDER_CASE_PASSED',case,flush=True)
