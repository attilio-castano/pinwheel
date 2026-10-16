"""Pinned-process workaround: suppress repeated credit BEFORE native routing."""
import atexit,ctypes,hashlib,json,os,platform
from pathlib import Path
CREDIT="_ZN3grt12GlobalRouter24addResourcesForPinAccessEv"
PREDICATE="_ZN3grt12GlobalRouter19pinPositionsChangedEPNS_3NetE"
DESTROY="_ZN3grt3Net11destroyPinsEv"
def pointer(p):return int(p.this if hasattr(p,"this") else p)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
class Patch:
 def __init__(self,symbol,replacement,expected=None):
  assert platform.machine()=="x86_64"
  self.symbol=symbol;self.function=getattr(ctypes.CDLL(None),symbol);self.address=ctypes.cast(self.function,ctypes.c_void_p).value;self.original=ctypes.string_at(self.address,32);self.replacement=replacement;self.active=False
  if expected is not None:assert self.original.hex()==expected,(symbol,self.original.hex())
  self.libc=ctypes.CDLL(None);self.libc.mprotect.argtypes=[ctypes.c_void_p,ctypes.c_size_t,ctypes.c_int];self.libc.mprotect.restype=ctypes.c_int
  # x86_64 has coherent instruction/data caches. Compiler memory writes occur
  # before synchronous native call in this sole OpenROAD process.
  assert any(int(l.split()[0].split("-")[0],16)<=self.address<int(l.split()[0].split("-")[1],16) and l.split()[1]=="r-xp" for l in Path("/proc/self/maps").read_text().splitlines())
  atexit.register(self.restore)
 def write(self,data):
  page=os.sysconf("SC_PAGE_SIZE");base=self.address//page*page;size=((self.address+len(data)-1)//page+1)*page-base
  assert self.libc.mprotect(base,size,7)==0
  ctypes.memmove(self.address,data,len(data));assert ctypes.string_at(self.address,len(data))==data
  assert self.libc.mprotect(base,size,5)==0
 def install(self):
  assert not self.active and ctypes.string_at(self.address,32)==self.original
  self.write(self.replacement);self.active=True
 def restore(self):
  if self.active:self.write(self.original);self.active=False;assert ctypes.string_at(self.address,32)==self.original
 def receipt(self):return {"symbol":self.symbol,"address":self.address,"original_prologue_hex":self.original.hex(),"replacement_hex":self.replacement.hex(),"active":self.active,"architecture":"x86_64","cache_policy":"x86_64 coherent instruction cache; synchronous same-process call; no cross-thread routing at patch installation","no_capacity_memory_or_saved_grid_writes":True}
def invalidate_one(router,net):
 # Exported public Net::destroyPins cache API. Public addDirtyNet then records
 # an empty cached pin list; native updateDirtyNets rebuilds real DB pins.
 fn=getattr(ctypes.CDLL(None),DESTROY);fn.argtypes=[ctypes.c_void_p];fn.restype=None
 native=router.getNet(net);assert native is not None
 fn(pointer(native));router.addDirtyNet(net)
 return {"method":"native public Net::destroyPins then GlobalRouter::addDirtyNet","net":net.getName(),"symbol":DESTROY,"DB_mutation":False}
