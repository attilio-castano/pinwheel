#!/usr/bin/env python3
"""Run pinned, unchanged ACT4 RV32I bodies under an explicit unprivileged EEI.

Sail creates the reference signature; upstream's own converter/selfcheck macros
consume it. Every instruction is also compared with a Lean Semantics/CoreModel
execution. Fresh ELF images explicitly supply every ROM/RAM byte. This is not
privileged conformance, ACT4 coverage closure, or emitted-RTL validation.
"""
from __future__ import annotations
import argparse
import errno
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import shutil
import socket
import struct
import subprocess
import sys
import tarfile
import tempfile
import time
import urllib.request
import isa_reference_check as ref

ROOT=Path(__file__).resolve().parents[1]
CACHE=ROOT/'build/architecture-tests/dependencies'
MANIFEST=ROOT/'tools/architecture_tests.json'
ADAPTER=ROOT/'test/architecture_test_adapter'
LEAN=ROOT/'test/ArchitectureTestTrace.lean'
ROM_SIZE=0x400000
RAM_BASE=0x1000000
RAM_SIZE=0x100000
sha=ref.sha
write_json=ref.write_json
command=ref.command


def source_paths():
    found=set(ref.source_paths())|{Path(__file__).resolve(),MANIFEST,LEAN,ROOT/'test/architecture_test_test.py'}|set(ADAPTER.iterdir())
    todo=[LEAN]
    while todo:
        p=todo.pop()
        for module in re.findall(r'^import\s+(Pinwheel\.[\w.]+)\s*$',p.read_text(),re.M):
            q=ROOT/(module.replace('.','/')+'.lean')
            if q not in found: found.add(q);todo.append(q)
    return sorted(found)


def hashes(paths): return {str(p):sha(p) for p in sorted(paths)}
def source_hashes(): return {str(p.relative_to(ROOT)):sha(p) for p in source_paths()}


def ensure_archive(entry, fetch):
    archive = CACHE / entry["filename"]
    if archive.exists() and sha(archive) == entry["sha256"]:
        return archive
    if not fetch:
        if archive.exists():
            raise RuntimeError(f"Archive hash mismatch: {archive}")
        raise RuntimeError(f"Missing {archive}; use --fetch")
    with tempfile.TemporaryDirectory(dir=CACHE) as staging:
        pending = Path(staging) / "download"
        with urllib.request.urlopen(entry["url"], timeout=120) as response, pending.open("wb") as out:
            shutil.copyfileobj(response, out)
        if sha(pending) != entry["sha256"]:
            raise RuntimeError(f"Archive hash mismatch: {archive}")
        pending.replace(archive)
    return archive


def verify_extraction(directory, root, tar, members):
    for member in members:
        path = directory / member.name
        if not path.resolve().is_relative_to((directory / root).resolve()):
            raise RuntimeError('Escaping archive link')
        if member.issym():
            if not path.is_symlink() or os.readlink(path) != member.linkname:
                raise RuntimeError('Changed archive symlink')
        elif member.isfile() or member.islnk():
            if not path.is_file() or sha(path) != hashlib.sha256(tar.extractfile(member).read()).hexdigest():
                raise RuntimeError(f'Changed extracted file {path}')


def ensure_extraction(archive, root):
    target = CACHE / root
    with tarfile.open(archive) as tar:
        members = tar.getmembers()
        for member in members:
            parts = Path(member.name).parts
            if not parts or parts[0] != root or '..' in parts or not (
                    member.isdir() or member.isfile() or member.issym() or member.islnk()):
                raise RuntimeError('Unsafe dependency archive member')
        if not target.exists():
            with tempfile.TemporaryDirectory(dir=CACHE) as staging:
                directory = Path(staging)
                tar.extractall(directory, filter='data')
                verify_extraction(directory, root, tar, members)
                try:
                    (directory / root).rename(target)
                    return
                except OSError as error:
                    # Another process can publish the same tree before this rename.
                    if error.errno not in (errno.ENOTEMPTY, errno.EEXIST):
                        raise
        verify_extraction(CACHE, root, tar, members)


def dependencies(fetch=False):
    pin=json.loads(MANIFEST.read_text())
    CACHE.mkdir(parents=True,exist_ok=True)
    for key in ('upstream','compiler'):
        entry = pin[key]
        ensure_extraction(ensure_archive(entry, fetch), entry["root"])
    reference,binary=ref.dependencies(fetch)
    return pin,CACHE/pin['upstream']['root'],CACHE/pin['compiler']['root'],reference,binary


def elf_images(data):
    """Strict RV32 ELF PT_LOAD extraction; no section or instruction rewriting."""
    if data[:16]!=b'\x7fELF'+bytes([1,1,1,0])+bytes(8): raise ValueError('Not little-endian ELF32')
    h=struct.unpack_from('<HHIIIIIHHHHHH',data,16)
    typ,machine,version,entry,phoff,_,_,ehsize,phsize,phnum,*_=h
    if (typ,machine,version,entry,ehsize,phsize)!=(2,243,1,0,52,32) or not 1<=phnum<=32: raise ValueError('Unsupported ELF header')
    rom=bytearray(ROM_SIZE);ram=bytearray(RAM_SIZE);ranges=[]
    for k in range(phnum):
        ptype,off,va,pa,filesz,memsz,flags,align=struct.unpack_from('<IIIIIIII',data,phoff+32*k)
        if ptype!=1: continue
        if va!=pa or filesz>memsz or off+filesz>len(data) or memsz==0: raise ValueError('Invalid load segment')
        if 0<=va and va+memsz<=ROM_SIZE and flags==5: dest,rel=rom,va
        elif RAM_BASE<=va and va+memsz<=RAM_BASE+RAM_SIZE and flags==6: dest,rel=ram,va-RAM_BASE
        else: raise ValueError('ELF segment violates explicit ROM/RAM map')
        if any(max(va,a)<min(va+memsz,b) for a,b in ranges): raise ValueError('Overlapping ELF load segments')
        ranges.append((va,va+memsz));dest[rel:rel+filesz]=data[off:off+filesz]
    if not ranges or not any(a==0 for a,b in ranges): raise ValueError('Missing reset entry image')
    return bytes(rom),bytes(ram)


def complete_elf(rom,ram):
    """Supplementary ELF loads explicit zero-filled gaps; original remains first."""
    if len(rom)!=ROM_SIZE or len(ram)!=RAM_SIZE: raise ValueError('Incomplete image')
    header=b'\x7fELF'+bytes([1,1,1,0])+bytes(8)+struct.pack('<HHIIIIIHHHHHH',2,243,1,0,52,0,0,52,32,2,0,0,0)
    off=116
    headers=struct.pack('<IIIIIIII',1,off,0,0,len(rom),len(rom),5,1)+struct.pack('<IIIIIIII',1,off+len(rom),RAM_BASE,RAM_BASE,len(ram),len(ram),6,1)
    return header+headers+rom+ram


def gap_elf(original):
    """Explicitly initialize only gaps, never overlap or rewrite upstream PT_LOAD."""
    elf_images(original)
    phoff=struct.unpack_from('<I',original,28)[0];count=struct.unpack_from('<H',original,44)[0]
    ranges=[]
    for k in range(count):
        kind,_,va,_,_,size,_,_=struct.unpack_from('<IIIIIIII',original,phoff+32*k)
        if kind==1:ranges.append((va,va+size))
    gaps=[]
    for base,size,flags in ((0,ROM_SIZE,5),(RAM_BASE,RAM_SIZE,6)):
        cursor=base
        for lo,hi in sorted((lo,hi) for lo,hi in ranges if base<=lo<base+size):
            if cursor<lo:gaps.append((cursor,lo-cursor,flags))
            cursor=hi
        if cursor<base+size:gaps.append((cursor,base+size-cursor,flags))
    offset=52+32*len(gaps)
    header=b'\x7fELF'+bytes([1,1,1,0])+bytes(8)+struct.pack('<HHIIIIIHHHHHH',2,243,1,0,52,0,0,52,32,len(gaps),0,0,0)
    headers=b'';payload=b''
    for address,size,flags in gaps:
        headers+=struct.pack('<IIIIIIII',1,offset,address,address,size,size,flags,1)
        payload+=bytes(size);offset+=size
    return header+headers+payload


def symbols(text):
    result={}
    for line in text.splitlines():
        m=re.fullmatch(r'([0-9a-fA-F]{8})\s+[A-Za-z]\s+(\S+)',line)
        if m:
            key=m[2]
            if key in result: raise ValueError('Duplicate symbol')
            result[key]=int(m[1],16)
    for key in ('pinwheel_test_halt','begin_signature','end_signature','rvtest_code_begin','rvtest_code_end'):
        if key not in result: raise ValueError(f'Missing symbol {key}')
    if not 0<=result['pinwheel_test_halt']<ROM_SIZE or result['pinwheel_test_halt']%4: raise ValueError('Bad stop')
    if not RAM_BASE<=result['begin_signature']<result['end_signature']<=RAM_BASE+RAM_SIZE: raise ValueError('Bad signature')
    return result


def parse_trace(text,stop,initial,rom,ram):
    """Reject unknown/truncated/trapped traces before any value comparison."""
    if type(stop) is not int or not 0<=stop<ROM_SIZE or stop%4: raise ValueError('Bad stop')
    if len(initial)!=33 or any(type(v)is not int or not 0<=v<2**32 for v in initial) or initial!=[0]*33: raise ValueError('Bad initial registers')
    if len(rom)!=ROM_SIZE or len(ram)!=RAM_SIZE: raise ValueError('Incomplete memory')
    regs=initial[:32];memory=bytearray(ram);frames=[];reads=0
    if not text.endswith('\n\n'): raise ValueError('Incomplete trace suffix')
    for block in text.strip().split('\n\n'):
        instruction=None;fetch=[];write=None;read=None
        for line in block.splitlines():
            ins=re.fullmatch(r'\[(\d+)\] \[M\]: 0x([0-9A-Fa-f]{8}) \(0x([0-9A-Fa-f]{8})\) .+',line)
            gpr=re.fullmatch(r'x(\d+) <- 0x([0-9A-Fa-f]{8})',line)
            mem=re.fullmatch(r'mem\[([XRW]),0x([0-9A-Fa-f]+)\] (->|<-) 0x([0-9A-Fa-f]+)',line)
            if ins:
                if instruction is not None or int(ins[1])!=len(frames): raise ValueError('Repeated/reordered instruction')
                pc,word=int(ins[2],16),int(ins[3],16)
                if pc%4 or pc+4>ROM_SIZE or int.from_bytes(rom[pc:pc+4],'little')!=word: raise ValueError('Wrong fetch bytes')
                if fetch!=[(pc,word&65535),(pc+2,word>>16)]: raise ValueError('Incomplete instruction fetch')
                instruction=(pc,word)
            elif gpr:
                if instruction is None or not 1<=int(gpr[1])<=31: raise ValueError('Invalid register write')
                regs[int(gpr[1])]=int(gpr[2],16)
            elif mem:
                kind,address,direction,digits=mem.groups();address=int(address,16);value=int(digits,16)
                if len(digits) not in (2,4,8) or (kind=='W')!=(direction=='<-'): raise ValueError('Malformed memory access')
                size=len(digits)//2
                if kind=='X':
                    if instruction is not None or size!=2: raise ValueError('Malformed fetch')
                    fetch.append((address,value))
                else:
                    if instruction is None: raise ValueError('Data access before instruction')
                    if RAM_BASE<=address and address+size<=RAM_BASE+RAM_SIZE: data,offset=memory,address-RAM_BASE
                    elif 0<=address and address+size<=ROM_SIZE and kind=='R': data,offset=rom,address
                    else: raise ValueError('Out of EEI data access')
                    if address%size: raise ValueError('Misaligned data access excluded')
                    if kind=='R':
                        if int.from_bytes(data[offset:offset+size],'little')!=value: raise ValueError('Reference read disagrees with explicit image/history')
                        if read is not None:raise ValueError('Multiple loads in RV32I instruction')
                        read=[address,size,value];reads+=1
                    else:
                        if write is not None: raise ValueError('Multiple stores in RV32I instruction')
                        data[offset:offset+size]=value.to_bytes(size,'little');write=[address,size,value]
            else: raise ValueError(f'Unexpected reference trace line: {line}')
        if instruction is None: raise ValueError('Missing instruction')
        frames.append(dict(pc=instruction[0],word=instruction[1],registers=list(regs),write=write,read=read))
    if not frames or frames[0]['pc']!=0: raise ValueError('Missing reset entry')
    for k,frame in enumerate(frames): frame['next_pc']=frames[k+1]['pc'] if k+1<len(frames) else stop
    return frames,bytes(memory),reads


def validate_frame(frame):
    if type(frame)is not dict or set(frame)!={'pc','word','next_pc','registers','write','read'}: raise ValueError('Bad local frame')
    for key in ('pc','word','next_pc'):
        if type(frame[key])is not int or not 0<=frame[key]<2**32: raise ValueError('Bad scalar')
    regs=frame['registers']
    if type(regs)is not list or len(regs)!=32 or regs[0]!=0 or any(type(v)is not int or not 0<=v<2**32 for v in regs): raise ValueError('Bad registers')
    for key in ('read','write'):
        w=frame[key]
        if w is not None:
            if type(w)is not list or len(w)!=3 or any(type(v)is not int for v in w): raise ValueError('Bad memory operation')
            a,n,v=w
            if n not in (1,2,4) or a%n or not 0<=v<2**(8*n): raise ValueError('Bad memory operation size/value')
            if not (RAM_BASE<=a and a+n<=RAM_BASE+RAM_SIZE) and not (key=='read' and 0<=a and a+n<=ROM_SIZE): raise ValueError('Bad memory operation range')
    if frame['read'] is not None and frame['write'] is not None:raise ValueError('Combined RV32I load/store')


def validate_summary(summary):
    keys={'cycles','data_completions','fetches','registers','retired','stop'}
    if type(summary)is not dict or set(summary)!=keys:raise ValueError('Bad local summary')
    for key in keys-{'registers'}:
        if type(summary[key])is not int or not 0<=summary[key]<2**32:raise ValueError('Bad summary scalar')
    validate_frame(dict(pc=0,word=0,next_pc=summary['stop'],registers=summary['registers'],write=None,read=None))
    if not 0<summary['retired']==summary['fetches']<=summary['cycles'] or summary['data_completions']>summary['retired']:raise ValueError('Bad summary accounting')
    if summary['stop']>=ROM_SIZE or summary['stop']%4:raise ValueError('Bad summary stop')


def compare(local,reference):
    for frame in local+reference: validate_frame(frame)
    if len(local)!=len(reference): raise ValueError('Incomplete instruction trace')
    for k,(a,b) in enumerate(zip(local,reference)):
        if a!=b: raise RuntimeError(f'Architectural mismatch at retirement {k}: {a} != {b}')


def sail_run(binary,config,elf,full,stop,directory,records, expected_status=1):
    directory.mkdir(exist_ok=True)
    with socket.socket() as reserve: reserve.bind(('127.0.0.1',0));port=reserve.getsockname()[1]
    command([binary,'--config',config,'--trace-instr','--trace-gpr','--trace-mem','--trace-step','--trace-exception','--trace-output',directory/'sail.trace','--test-signature',directory/'sail.signature','--signature-granularity','4','--dump-memory',directory/'ram','--stop-at-pc',hex(stop),'--inst-limit','1000000',elf,full],directory.parent.parent,records)
    argv=[str(binary),'--config',str(config),'--gdb-server-port',str(port),str(elf),str(full)]
    start=time.monotonic();sock=None;rsp=None
    with (directory/'sail.log').open('w') as log:
        proc=subprocess.Popen(argv,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
        try:
            deadline=time.monotonic()+10
            while time.monotonic()<deadline:
                if proc.poll()is not None: raise RuntimeError('Sail exited before debugger')
                try: sock=socket.create_connection(('127.0.0.1',port),timeout=.1);break
                except OSError:time.sleep(.005)
            if sock is None:raise RuntimeError('Debugger timeout')
            rsp=ref.RSP(sock)
            if rsp.call('?')!='S05':raise RuntimeError('Wrong initial stop')
            rsp.ok('QStartNoAckMode');rsp.ack=False
            initial=rsp.registers()
            if initial!=[0]*33: raise RuntimeError('Unexpected reference initial architectural state')
            rsp.ok(f'Z1,{stop:x},4')
            sock.settimeout(45)
            if rsp.call('c')!='S05':raise RuntimeError('Wrong completion stop')
            final=rsp.registers()
            if final[32]!=stop or final[10]!=expected_status:raise RuntimeError(f'Upstream failure/incorrect stop {final}')
            rsp.ok('D');sock.close();sock=None
            result=proc.wait(timeout=10)
            if result!=0:raise RuntimeError('Reference process failure')
        finally:
            if rsp is not None:write_json(directory/'rsp.json',rsp.transcript)
            if sock is not None:sock.close()
            if proc.poll()is None:proc.terminate();proc.wait(timeout=5)
            records.append(dict(argv=argv,exit_code=proc.returncode,seconds=time.monotonic()-start,log=str((directory/'sail.log').relative_to(directory.parent.parent))))
    write_json(directory/'architectural-endpoints.json',dict(initial=initial,final=final))
    return initial,final


def patch_instruction(data,address,value):
    result=bytearray(data);phoff=struct.unpack_from('<I',data,28)[0];count=struct.unpack_from('<H',data,44)[0]
    hits=0
    for k in range(count):
        kind,off,va,_,size,_,flags,_=struct.unpack_from('<IIIIIIII',data,phoff+32*k)
        if kind==1 and flags==5 and va<=address and address+4<=va+size:
            struct.pack_into('<I',result,off+address-va,value);hits+=1
    if hits!=1:raise ValueError('Mutation must touch exactly one executable instruction')
    return bytes(result)


def mutation_controls(binary,config,directory,records,cc,up):
    """Actual executable mutation must change an architectural value, not only its word."""
    base=directory/'I-add-00/signature';syms=json.loads((base/'symbols.json').read_text())
    expected=[json.loads(line) for line in (base/'local.jsonl').read_text().splitlines()]
    target=None
    for k,frame in enumerate(expected):
        word=frame['word'];rhs=(word>>20)&31
        if syms['rvtest_code_begin']<=frame['pc']<syms['rvtest_code_end'] and word&0xfe00707f==0x33 and (word>>7)&31 and k and expected[k-1]['registers'][rhs] not in (0,0x80000000):
            target=(k,frame);break
    if target is None:raise RuntimeError('No active ADD mutation target')
    k,frame=target;work=directory/'mutated-add/signature';work.mkdir(parents=True)
    mutant=patch_instruction((base/'test.elf').read_bytes(),frame['pc'],frame['word']^(1<<30))
    elf=work/'test.elf';elf.write_bytes(mutant);rom,ram=elf_images(mutant);full=work/'complete-image.elf';full.write_bytes(gap_elf(mutant))
    initial,final=sail_run(binary,config,elf,full,syms['pinwheel_test_halt'],work,records)
    actual,contents,_=parse_trace((work/'sail.trace').read_text(),syms['pinwheel_test_halt'],initial,rom,ram)
    if actual[-1]['registers']!=final[:32] or contents!=(work/f'ram.0x{RAM_BASE:x}.bin').read_bytes():raise RuntimeError('Malformed mutant endpoints')
    if len(actual)<=k or actual[k]['pc']!=frame['pc'] or actual[k]['registers']==frame['registers']:raise RuntimeError('No concrete mutation value witness')
    try:compare(expected,actual)
    except RuntimeError:pass
    else:raise RuntimeError('Actual instruction fault not detected')
    witness=dict(name='upstream-add-changed-to-sub',retirement=k,pc=frame['pc'],original_word=frame['word'],mutated_word=actual[k]['word'],expected_registers=frame['registers'],actual_registers=actual[k]['registers'])
    write_json(work/'witness.json',witness)
    # A wrong expected signature must reach the upstream fail path, not merely
    # differ in a host comparator. Only generated reference data is corrupted.
    work=directory/'mutated-signature/selfcheck';work.mkdir(parents=True)
    lines=(base/'sail.results').read_text().splitlines()
    values=[i for i,line in enumerate(lines) if re.fullmatch(r'.word 0x[0-9a-f]{8}',line)]
    at=values[1];before=int(lines[at].split('0x')[1],16);lines[at]=f'.word 0x{before^1:08x}'
    wrong=work/'wrong.results';wrong.write_text('\n'.join(lines)+'\n')
    elf=work/'test.elf'
    command([cc,'-v','-march=rv32i','-mabi=ilp32','-nostdlib','-nostartfiles','-static','-Wl,--no-relax','-I'+str(ADAPTER),'-I'+str(up/'tests/env'),'-DTEST_FLEN=32','-DTEST_FILE="I-add-00"','-DRVTEST_SELFCHECK',f'-DSIGNATURE_FILE="{wrong}"','-T'+str(ADAPTER/'link.ld'),up/'tests/rv32i/I/I-add-00.S',ADAPTER/'halt.S','-o',elf],directory,records)
    symtext=command([cc.parent/'riscv-none-elf-nm','-n',elf],directory,records);(work/'symbols.txt').write_text(symtext);syms=symbols(symtext)
    rom,ram=elf_images(elf.read_bytes());full=work/'complete-image.elf';full.write_bytes(gap_elf(elf.read_bytes()))
    initial,final=sail_run(binary,config,elf,full,syms['pinwheel_test_halt'],work,records,expected_status=3)
    bad,contents,_=parse_trace((work/'sail.trace').read_text(),syms['pinwheel_test_halt'],initial,rom,ram)
    if bad[-1]['registers']!=final[:32] or contents!=(work/f'ram.0x{RAM_BASE:x}.bin').read_bytes():raise RuntimeError('Malformed failed-signature endpoints')
    signature_fault=dict(name='upstream-selfcheck-wrong-expected-result',expected_signature_word=before,mutated_signature_word=before^1,actual_passfail_register=final[10],expected_passfail_register=1,retirements=len(bad))
    write_json(work/'witness.json',signature_fault)
    return [witness,signature_fault]


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--tag',required=True);ap.add_argument('--fetch',action='store_true');ap.add_argument('--limit',type=int);args=ap.parse_args()
    if not re.fullmatch(r'[A-Za-z0-9_-]+',args.tag) or (args.limit is not None and args.limit<1):raise ValueError('Bad tag/limit')
    directory=ROOT/'build/architecture-tests'/args.tag;directory.mkdir(parents=True,exist_ok=False)
    sources=source_hashes();records=[];report=dict(status='running',sources=sources,commands=records,tests=[])
    removed=[k for k in os.environ if k in {'GCC_EXEC_PREFIX','COMPILER_PATH','LIBRARY_PATH','CPATH','C_INCLUDE_PATH','CPLUS_INCLUDE_PATH','OBJC_INCLUDE_PATH','LD_LIBRARY_PATH'} or k.startswith('DYLD_')]
    for k in removed:os.environ.pop(k)
    report['cleared_tool_override_variables']=sorted(removed)
    try:
        pin,up,tc,reference,binary=dependencies(args.fetch)
        write_json(directory/'pin.json',pin);report.update(pin=pin,reference=reference,exclusions=pin['exclusions'])
        cc=tc/'bin/riscv-none-elf-gcc';nm=tc/'bin/riscv-none-elf-nm'
        report['host']=dict(platform=platform.platform(),python=sys.version)
        report['compiler_version']=command([cc,'--version'],directory,records)
        report['compiler_subtools']=command([cc,'-print-search-dirs'],directory,records)
        report['sail_build_info']=command([binary,'--build-info'],directory,records)
        report['native_linkage']=command(['/usr/bin/otool','-L',binary,cc,tc/'libexec/gcc/riscv-none-elf/15.2.0/cc1',tc/'riscv-none-elf/bin/as',tc/'riscv-none-elf/bin/ld'],directory,records)
        report['runtime_boundary']='Pinned release binaries and complete bundled compiler files; macOS dyld-cache system libraries recorded by linkage/host identity, not OS qualification.'
        template=command([binary,'--rv32','--print-default-config'],directory,records);(directory/'default-rv32.json').write_text(template)
        config=ref.configuration(template);config['memory']['regions'][0]['size']['value']=hex(ROM_SIZE);config['memory']['regions'][1]['base']['value']=hex(RAM_BASE);config['memory']['regions'][1]['size']['value']=hex(RAM_SIZE);config['memory']['dtb_address']['value']='0x0'
        write_json(directory/'config.json',config);command([binary,'--config',directory/'config.json','--validate-config'],directory,records)
        report['isa_string']=command([binary,'--config',directory/'config.json','--print-isa-string'],directory,records).strip()
        command(['lake','build','Pinwheel.Hardware.Processor.CoreModel','Pinwheel.Hardware.Processor.AddressMap'],directory,records)
        lean=Path(command(['lake','env','which','lean'],directory,records).strip()).resolve()
        lake=Path(command(['lake','env','which','lake'],directory,records).strip()).resolve()
        tools={binary,lean,lake,Path(shutil.which('lake')).resolve(),Path(sys.executable).resolve(),Path('/usr/bin/otool')}
        tools.update(p for p in tc.rglob('*') if p.is_file())
        tools.update((lean.parent.parent/'lib/lean').glob('*.dylib'))
        report['tools']=hashes(tools)
        command([sys.executable,ROOT/'test/architecture_test_test.py'],directory,records)
        report['direct_lean_dependencies']=command(['lake','env','lean','--deps',LEAN],directory,records).splitlines()
        builds=[]
        for p in source_paths():
            if p.suffix=='.lean' and 'Pinwheel' in p.parts:
                base=ROOT/'.lake/build/lib/lean'/p.relative_to(ROOT).with_suffix('')
                builds.extend(q for ext in ('.olean','.olean.private','.olean.server','.ir') if (q:=Path(str(base)+ext)).exists())
        report['project_build_inputs']=hashes(builds)
        report['lean_distribution_inputs']=hashes(p for p in (lean.parent.parent/'lib/lean').rglob('*') if p.is_file() and p.name.endswith(('.olean','.olean.private','.olean.server','.ir')))
        tests=sorted((up/pin['suite']).glob('*.S'))
        if len(tests)!=pin['expected_test_files']:raise RuntimeError('Changed suite inventory')
        report['upstream_inventory']={str(p.relative_to(up)):sha(p) for p in tests}
        report['upstream_headers']=hashes((up/'tests/env').glob('*.h'))
        report['full_selected_suite']=args.limit is None
        if args.limit is not None:tests=tests[:args.limit]
        spec=importlib.util.spec_from_file_location('upstream_sig_modify',up/'framework/src/act/sig_modify.py');sig=importlib.util.module_from_spec(spec);spec.loader.exec_module(sig)
        report['upstream_signature_converter']=dict(path=str(spec.origin),sha256=sha(spec.origin))
        for test in tests:
            case=directory/test.stem;case.mkdir();result=dict(test=str(test.relative_to(up)),source_sha256=sha(test),modes=[])
            for mode in ('signature','selfcheck'):
                work=case/mode;work.mkdir();elf=work/'test.elf'
                argv=[cc,'-v','-march=rv32i','-mabi=ilp32','-nostdlib','-nostartfiles','-static','-Wl,--no-relax','-I'+str(ADAPTER),'-I'+str(up/'tests/env'),'-DTEST_FLEN=32',f'-DTEST_FILE="{test.stem}"','-T'+str(ADAPTER/'link.ld')]
                if mode=='selfcheck':argv += ['-DRVTEST_SELFCHECK',f'-DSIGNATURE_FILE="{case}/signature/sail.results"']
                command(argv+[test,ADAPTER/'halt.S','-o',elf],directory,records)
                symtext=command([nm,'-n',elf],directory,records);(work/'symbols.txt').write_text(symtext);syms=symbols(symtext);write_json(work/'symbols.json',syms)
                rom,ram=elf_images(elf.read_bytes());(work/'rom.bin').write_bytes(rom);(work/'initial-ram.bin').write_bytes(ram);(work/'complete-image.elf').write_bytes(gap_elf(elf.read_bytes()))
                initial,final=sail_run(binary,directory/'config.json',elf,work/'complete-image.elf',syms['pinwheel_test_halt'],work,records)
                frames,reference_ram,reads=parse_trace((work/'sail.trace').read_text(),syms['pinwheel_test_halt'],initial,rom,ram)
                if frames[-1]['registers']!=final[:32] or (work/f'ram.0x{RAM_BASE:x}.bin').read_bytes()!=reference_ram:raise RuntimeError('Trace and independent endpoint dump disagree')
                signature=(work/'sail.signature').read_text().splitlines();a=syms['begin_signature']-RAM_BASE;b=syms['end_signature']-RAM_BASE
                if any(not re.fullmatch('[0-9a-f]{8}',x) for x in signature) or b-a!=4*len(signature):raise RuntimeError('Malformed/incomplete signature')
                if b''.join(int(v,16).to_bytes(4,'little') for v in signature)!=reference_ram[a:b]:raise RuntimeError('Signature differs from RAM')
                if mode=='signature':sig.process_signature_file(work/'sail.signature',32)
                job=dict(rom=str(work/'rom.bin'),ram=str(work/'initial-ram.bin'),trace=str(work/'local.jsonl'),final_ram=str(work/'local-ram.bin'),stop=syms['pinwheel_test_halt'],limit=1000000)
                (work/'jobs.jsonl').write_text(json.dumps(job)+'\n')
                command(['lake','env','lean','-DwarningAsError=true','--run',LEAN,work/'jobs.jsonl',work/'local-result.jsonl'],directory,records,timeout=240)
                local=[json.loads(l) for l in (work/'local.jsonl').read_text().splitlines()];compare(local,frames)
                if (work/'local-ram.bin').read_bytes()!=reference_ram:raise RuntimeError('Final RAM mismatch')
                summary=json.loads((work/'local-result.jsonl').read_text());validate_summary(summary)
                if summary['retired']!=len(frames) or summary['registers']!=final[:32] or summary['stop']!=syms['pinwheel_test_halt'] or summary['data_completions']!=reads+sum(f['write']is not None for f in frames):raise RuntimeError('Final summary mismatch')
                write_json(work/'comparison.json',dict(status='passed',**summary,reference_reads=reads,reference_writes=sum(f['write']is not None for f in frames),signature_words=len(signature)))
                result['modes'].append(dict(mode=mode,**summary,reference_reads=reads,signature_words=len(signature)))
            report['tests'].append(result);print(f"PASS {test.name}: signature + upstream selfcheck + semantic/controller traces",flush=True)
        report['actual_program_mutations']=mutation_controls(binary,directory/'config.json',directory,records,cc,up)
        report['comparison']='All instruction PC/word/nextPC,32 integer registers, every accepted read address/size/value (including x0 loads), every committed store and full final RAM; upstream signature and upstream selfcheck. Actual GDB initial/final registers, full memory dump and trace are cross-checked.'
        report['adapter']='Unchanged upstream test/header bodies. Empty documented no-CSR boot override; pass/fail a0=1/3 at explicit stop. Full image gaps explicitly loaded as zero. ROM4MiB at0;RAM1MiB at0x01000000. No MMIO; serialized FENCE. Controller request/response stalls and completion-edge stores.'
        if source_hashes()!=sources:raise RuntimeError('Source changed during campaign')
        for group in ('tools','project_build_inputs','lean_distribution_inputs'):
            for path,digest in report[group].items():
                if sha(path)!=digest:raise RuntimeError(f'{group} changed: {path}')
        dependencies(False)
        report['status']='passed'
    except Exception as error:
        report['status']='failed';report['error']=f'{type(error).__name__}: {error}';raise
    finally:
        report['artifacts']={str(p.relative_to(directory)):sha(p) for p in sorted(directory.rglob('*')) if p.is_file() and p.name!='report.json'}
        write_json(directory/'report.json',report)
    print(f"PASS {len(report['tests'])} upstream ACT4 files; {directory/'report.json'}")

if __name__=='__main__':main()
