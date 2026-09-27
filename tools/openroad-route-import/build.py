"""Build only inside the pinned, offline experiment image; no default replacement."""
import hashlib,json,subprocess,sys,time
from pathlib import Path
out=Path(sys.argv[1]); support=Path(__file__).resolve().parent
src=Path('/hold/source'); native=Path('/probe/source/src/grt/src'); generated=out/'include'
generated.mkdir(exist_ok=False);(generated/'grt').mkdir()
inputs={}
for original,relative,cls in [(src/'src/grt/include/grt/GlobalRouter.h','grt/GlobalRouter.h','GlobalRouter'),(native/'fastroute/include/FastRoute.h','FastRoute.h','FastRouteCore')]:
    data=original.read_text();needle=f'class {cls}\n{{\n'
    if data.count(needle)!=1:raise ValueError('Unexpected pinned class declaration')
    (generated/relative).write_text(data.replace(needle,needle+'  friend class PinwheelRouteImport;\n'))
    inputs[str(original)]=hashlib.sha256(original.read_bytes()).hexdigest()
cc='/nix/store/h6vk77gc3300z162ywhcz8asjckrgmr3-clang-wrapper-21.1.8/bin/clang++'
sta=Path('/nix/store/dl4s2h66da8piq4wq9p0ylhc3mmn6wab-opensta-dev')
includes=[generated,src/'include',*[p for p in (src/'src').glob('*/include')],native,native/'fastroute/include']
system=[sta/'include',Path('/hold/headers/boost/include'),Path('/hold/headers/fmt/include'),Path('/hold/headers/spdlog/include'),Path('/nix/store/xrhg1bl0nlhvz4aipvack0r4ch3q85k1-tcl-8.6.16/include')]
args=[cc,'-std=c++20','-O2','-DNDEBUG','-fPIC','-shared','-Wl,-Bsymbolic','-DSPDLOG_COMPILED_LIB','-DSPDLOG_FMT_EXTERNAL','-DFMT_SHARED','-DBOOST_STACKTRACE_GNU_SOURCE_NOT_REQUIRED=1']+['-I'+str(p) for p in includes]+[a for p in system for a in ['-isystem',str(p)]]+[str(support/'extension.cc'),'-o',str(out/'libpinwheel_route_import.so')]
t=time.monotonic();result=subprocess.run(args,capture_output=True,text=True,timeout=210)
(out/'compile.log').write_text(result.stdout+result.stderr)
record=dict(status='passed' if result.returncode==0 else 'failed',argv=args,seconds=round(time.monotonic()-t,3),returncode=result.returncode,header_inputs_sha256=inputs)
if result.returncode==0:record['binary_sha256']=hashlib.sha256((out/'libpinwheel_route_import.so').read_bytes()).hexdigest()
(out/'build.json').write_text(json.dumps(record,indent=2)+'\n')
if result.returncode:raise RuntimeError((result.stdout+result.stderr)[-7000:])
print(record['status'],record['seconds'],record['binary_sha256'])
