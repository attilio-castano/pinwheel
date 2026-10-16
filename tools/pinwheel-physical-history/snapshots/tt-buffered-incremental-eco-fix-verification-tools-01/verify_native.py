import ctypes,json,sys,os,hashlib
from pathlib import Path
from openroad import Tech,Design
from runtime_guard import Patch,CREDIT,PREDICATE,DESTROY,pointer,invalidate_one,sha
from native_inventory import snapshot
R=Path("/work/diagnostic");tech=Tech();design=Design(tech)
def tcl(s):
 r=design.evalTclString('if {[catch {\n'+s+'\n} msg opts]} {puts stderr $msg; exit 2}; set ::pw_ok PINWHEEL_TCL_OK');assert r=="PINWHEEL_TCL_OK",r
tcl('source /work/diagnostic/load.tcl\nsource $::env(SCRIPTS_DIR)/openroad/common/set_rc.tcl\nread_global_route_segments /work/diagnostic/after_grt.segments')
router=design.getGlobalRouter();before=snapshot(design.getDb(),design.getBlock(),"before")
credit=Patch(CREDIT,b"\xc3");predicate=Patch(PREDICATE,b"\xb8\x01\x00\x00\x00\xc3")
credit.install();credit.function.argtypes=[ctypes.c_void_p];credit.function.restype=None;credit.function(pointer(router));credit.function(pointer(router));active=credit.receipt();credit.restore();assert not credit.active
net=design.getBlock().findNet("_03283_");assert str(net.getSigType())=="SIGNAL" and net.getNonDefaultRule() is None
try:
 receipt=invalidate_one(router,net);mode="cache_API"
except AttributeError as e:
 receipt={"method":"temporarily scoped native pinPositionsChanged override","missing_cache_API":repr(e)};mode="predicate_patch";predicate.install();assert predicate.active;predicate.restore()
after=snapshot(design.getDb(),design.getBlock(),"after");assert before==after
result={"status":"measured","native_binary_version":design.evalTclString("ord::openroad_version"),"native_binary_sha256":sha(Path(os.readlink("/proc/self/exe"))),"credit":active,"credit_original_prologue_restored":True,"predicate":predicate.receipt(),"predicate_original_prologue_restored":True,"dirty_mode":mode,"cache_invalidation":receipt,"native_inventory_before_after_identical":True,"cold_import_only_no_candidate":True,"routing_calls_executed":0,"ECO_mutations_executed":0,"FastRoute_API_type":str(type(router.fastroute())),"FastRoute_API_dir":dir(router.fastroute()),"boundary":"Native exported-function/mprotect/cache API smoke only; actual DIRTYroute/capacity/allroute/RC identity must pass live mainproducer BEFORE ECO."}
(R/"measurement.json").write_text(json.dumps(result,indent=2)+"\n");print("PINWHEEL_FIX_API_SMOKE_PASSED",flush=True)
