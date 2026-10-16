import json,os,sys,ctypes,shutil,subprocess
from pathlib import Path
from openroad import Tech,Design
R=Path("/work/diagnostic");tech=Tech();design=Design(tech);router=design.getGlobalRouter()
result={"status":"measured","router_type":str(type(router)),"router_dir":dir(router),"compiler_paths":{n:shutil.which(n) for n in ("g++","clang++","cc","nm","objdump","readelf")},"executable":os.readlink("/proc/self/exe"),"modules":{n:getattr(m,"__file__",None) for n,m in list(sys.modules.items()) if n in ("openroad","_openroad","grt","grt_py","_grt_py")}}
try:
 import grt
 result["grt_dir"]=dir(grt);result["grt_module"]=grt.__file__
except Exception as e:result["grt_error"]=repr(e)
for name in ("_ZN3grt12GlobalRouter24addResourcesForPinAccessEv","_ZN3grt12GlobalRouter12initNetlistERSt6vectorIPNS_3NetESaIS3_EE"):
 try:result.setdefault("dynamic_symbols",{})[name]=int(ctypes.cast(getattr(ctypes.CDLL(None),name),ctypes.c_void_p).value)
 except Exception as e:result.setdefault("dynamic_symbols",{})[name]=repr(e)
for path in ("/usr/include","/nix/store"):
 result.setdefault("headers",{})[path]=[]
 if path=="/usr/include":result["headers"][path]=list(map(str,Path(path).glob("**/GlobalRouter.h")))
for command in (["nm","-C",result["executable"]],["nm","-D","-C",result["executable"]]):
 if shutil.which(command[0]):
  q=subprocess.run(command,capture_output=True,text=True,timeout=10);result.setdefault("symbols",[]).append({"cmd":command,"exit":q.returncode,"matches":[l for l in q.stdout.splitlines() if any(s in l for s in ("addResourcesForPinAccess","GlobalRouter::initNetlist","GlobalRouter::fastroute","FastRouteCore::addAdjustment"))],"stderr":q.stderr[:500]})
(R/"measurement.json").write_text(json.dumps(result,indent=2)+"\n");print(json.dumps(result),flush=True)
