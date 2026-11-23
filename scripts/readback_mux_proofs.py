"""Add ordinary-kernel mux algebra before expensive generic proof search.

Every generated theorem header is preserved byte for byte. The branch is only
successful if all goals close, so it neither narrows raw state nor drops guards.
"""
from pathlib import Path
import re

IMPORT = 'import Pinwheel.Hardware.Readback.Mux\n'
MARKER = '  all_goals first\n'
BRANCH = ('  | (simp only [ite_self, Pinwheel.Hardware.Readback.Mux.orSelect,\n'
          '       Pinwheel.Hardware.Readback.Mux.notSelect, BitVec.and_assoc]\n'
          '     done)\n'
          '  | (normalize_mux_guards; done)\n')
HEADER = re.compile(r'theorem local_[0-9]+ [^\n]* :\n[ \t]+[^\n]+ := by\n\Z')


def declarations(text):
    lines,offsets=text.splitlines(keepends=True),[0]
    for line in lines:offsets.append(offsets[-1]+len(line))
    result=[];names=set();k=0
    while k<len(lines):
        if not re.match(r'theorem local_[0-9]+(?:\s|$)',lines[k]):k+=1;continue
        if k+1>=len(lines):raise ValueError('Truncated local theorem')
        header=lines[k]+lines[k+1]
        if not HEADER.fullmatch(header):raise ValueError('Ambiguous ordinary theorem header')
        name=lines[k].split()[1]
        if name in names:raise ValueError('Duplicate local theorem')
        names.add(name);end=k+2
        while end<len(lines) and (not lines[end].strip() or lines[end][0] in ' \t'):end+=1
        if end==len(lines) or not lines[end].startswith(('theorem ','run_cmd ','end ')):
            raise ValueError('Missing or changed top-level proof boundary')
        result.append((offsets[k],offsets[k+2],offsets[end],header));k=end
    return result


def add_mux_algebra(directory: Path, modules: list[str]) -> int:
    total=0
    for module in modules:
        if not re.fullmatch(r'LocalProofs[0-9]*',module):continue
        path=directory/(module+'.lean');original=path.read_text();updated=original
        decls=declarations(original);edits=[]
        for start,body_start,end,header in decls:
            body=original[body_start:end]
            if MARKER not in body:continue
            if body.count(MARKER)!=1 or BRANCH in body:raise ValueError('Already modified or ambiguous proof search')
            edits.append((start,end,header+body.replace(MARKER,MARKER+BRANCH,1)));total+=1
        for start,end,value in reversed(edits):updated=updated[:start]+value+updated[end:]
        if [d[3] for d in declarations(updated)]!=[d[3] for d in decls]:raise AssertionError('Changed theorem statements')
        if edits:updated=IMPORT+updated
        path.write_text(updated)
    return total
