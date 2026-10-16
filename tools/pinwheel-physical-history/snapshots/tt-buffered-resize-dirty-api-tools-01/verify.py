"""Public pin-history API fixture: native init only, no routing or physical edit."""
import ctypes,hashlib,json,os,shutil
from pathlib import Path
from openroad import Tech,Design
from native_inventory import snapshot
R=Path('/work/diagnostic');tech=Tech();design=Design(tech)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(x):(R/'measurement.json').write_text(json.dumps(x,indent=2)+'\n')
def tcl(s):
 r=design.evalTclString('if {[catch {\n'+s+'\n} msg opts]} {puts stderr $msg; exit 2}; set ::pw_ok PINWHEEL_TCL_OK');assert r=='PINWHEEL_TCL_OK',r
def ptr(x):return int(x.this if hasattr(x,'this') else x)
def fn(name,argtypes,restype):
 f=getattr(ctypes.CDLL(None),name);f.argtypes=argtypes;f.restype=restype;return f
exe=Path(os.readlink('/proc/self/exe'));assert sha(exe)=='6ba87b45c762ee8c9670375c204cd03d801a6da98cd6e056a1c73027aad68a7c'
tcl('source /work/diagnostic/load.tcl\nsource $::env(SCRIPTS_DIR)/openroad/common/set_rc.tcl')
BEFORE=snapshot(design.getDb(),design.getBlock(),'before')
tcl('global_route -congestion_iterations 10 -start_incremental')
router=design.getGlobalRouter();lib=ctypes.CDLL(None)
result={'status':'measured','native_binary_sha256':sha(exe),'native_binary_version':design.evalTclString('ord::openroad_version'),'physical_edit_count':0,'routing_solve_count':0,'native_init_only':True,'predicate_unpatched':True,'credit_function_unpatched':True,'allowed_signal_nets':['_11039_','net913','net914'],'rows':[],'API_available':False,'compiler_paths':{n:shutil.which(n) for n in ['clang++','g++','c++']},'native_Net_wrapper':None}
try:
 native=router.getNet(design.getBlock().findNet('net913'));result['native_Net_wrapper']={'type':str(type(native)),'dir':dir(native)}
 clear=getattr(native,'clearLastPinPositions',None)
 if callable(clear):
  clear_api='SWIG public Net::clearLastPinPositions';clear_native=lambda p:p.clearLastPinPositions()
 else:
  f=fn('_ZN3grt3Net21clearLastPinPositionsEv',[ctypes.c_void_p],None);clear_api='exported public Net::clearLastPinPositions';clear_native=lambda p:f(ptr(p))
 result['API_available']=True;result['clear_API']=clear_api
 destroy=fn('_ZN3grt3Net11destroyPinsEv',[ctypes.c_void_p],None)
 update=fn('_ZN3grt12GlobalRouter13updateNetPinsEPNS_3NetE',[ctypes.c_void_p,ctypes.c_void_p],None)
 pred=fn('_ZN3grt12GlobalRouter19pinPositionsChangedEPNS_3NetE',[ctypes.c_void_p,ctypes.c_void_p],ctypes.c_bool)
 for name in result['allowed_signal_nets']:
  dbnet=design.getBlock().findNet(name);assert str(dbnet.getSigType())=='SIGNAL' and dbnet.getNonDefaultRule() is None
  native=router.getNet(dbnet);router.addDirtyNet(dbnet) # emulate earlier swap callback with populated history
  original_predicate=bool(pred(ptr(router),ptr(native)));assert original_predicate is False
  destroy(ptr(native));router.addDirtyNet(dbnet);update(ptr(router),ptr(native))
  old_failure=bool(pred(ptr(router),ptr(native)));assert old_failure is False
  destroy(ptr(native));router.addDirtyNet(dbnet);clear_native(native);update(ptr(router),ptr(native))
  repaired=bool(pred(ptr(router),ptr(native)));assert repaired is True
  result['rows'].append({'net':name,'original_predicate':original_predicate,'destroy_reenroll_rebuild_predicate':old_failure,'clear_history_rebuild_predicate':repaired})
except AttributeError as error:
 result['API_unavailable_reason']=repr(error);result['status']='blocked_public_API_unavailable'
AFTER=snapshot(design.getDb(),design.getBlock(),'after');assert BEFORE==AFTER,'Read-only API fixture changed native inventory'
result['native_inventory_before_after_identical']=True;write(result)
assert result['API_available'],result.get('API_unavailable_reason')
assert len(result['rows'])==3
print('PINWHEEL_PUBLIC_PIN_HISTORY_RESET_VERIFIED',flush=True)
