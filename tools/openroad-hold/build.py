import hashlib,json,os,subprocess,time
from pathlib import Path
out=Path('/probe');src=out/'source';start=time.monotonic();records=[]
cc='/nix/store/h6vk77gc3300z162ywhcz8asjckrgmr3-clang-wrapper-21.1.8/bin/clang++'
sta=Path('/nix/store/dl4s2h66da8piq4wq9p0ylhc3mmn6wab-opensta-dev')
includes=[src/'include',src/'src/rsz/src',*[p for p in (src/'src').glob('*/include')],sta/'include',out/'headers/boost/include',out/'headers/fmt/include',out/'headers/spdlog/include',Path('/nix/store/xrhg1bl0nlhvz4aipvack0r4ch3q85k1-tcl-8.6.16/include')]
system_includes=includes[-5:];includes=includes[:-5]
cmd=[cc,'-std=c++20','-O3','-DNDEBUG','-fPIC','-shared','-Wl,-Bsymbolic','-DSPDLOG_COMPILED_LIB','-DSPDLOG_FMT_EXTERNAL','-DFMT_SHARED','-DBOOST_STACKTRACE_GNU_SOURCE_NOT_REQUIRED=1']+['-I'+str(p) for p in includes]+[item for p in system_includes for item in ['-isystem',str(p)]]
for name,source in [('original',src/'src/rsz/src/RepairHold.cc'),('patched',out/'RepairHold-patched.cc')]:
 folder=out/'native-02'/name;folder.mkdir(parents=True,exist_ok=False);args=cmd+[str(source),'/support/extension.cc','-o',str(folder/'libpinwheel_hold.so')]
 t=time.monotonic();r=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=300);(folder/'compile.log').write_text(r.stdout);records.append(dict(label=name,argv=args,seconds=round(time.monotonic()-t,3),returncode=r.returncode))
 (out/'build.json').write_text(json.dumps(dict(status='running' if r.returncode==0 else 'failed',commands=records),indent=2)+'\n')
 if r.returncode:raise RuntimeError(r.stdout[-3500:])
print('Built both hold implementations in',round(time.monotonic()-start,3),'seconds.')
(out/'build.json').write_text(json.dumps(dict(status='passed',seconds=round(time.monotonic()-start,3),commands=records,binaries={name:hashlib.sha256((out/'native-02'/name/'libpinwheel_hold.so').read_bytes()).hexdigest() for name in ['original','patched']}),indent=2)+'\n')
