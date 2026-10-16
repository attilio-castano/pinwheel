"""Strict raw native segment parser; no route reconstruction or missing-net inference."""
import hashlib,json,re
from pathlib import Path

def parse_segments(path):
    text=Path(path).read_text();nets={};name=None;opened=False
    for raw in text.splitlines():
        line=raw.strip()
        if not line:continue
        if name is None:
            assert line not in ('(',')') and len(line.split())==1,('Invalid net name',line)
            assert line not in nets,('Duplicate net',line)
            name=line;nets[name]=[];opened=False
        elif not opened:
            assert line=='(',('Expected opening',line);opened=True
        elif line==')':
            assert nets[name],('Empty exported route',name);name=None;opened=False
        else:
            row=line.split();assert len(row)==6,('Invalid segment',line)
            for index in (0,1,3,4):assert re.fullmatch(r'-?\d+',row[index]),('Invalid coordinate',line)
            for index in (2,5):assert re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',row[index]),('Invalid layer',line)
            layers={'Metal1':1,'Metal2':2,'Metal3':3,'Metal4':4,'TopMetal1':5}
            assert row[2] in layers and row[5] in layers,('Layer outside pinned technology',line)
            if row[2]==row[5]:assert row[0]==row[3] or row[1]==row[4],('Diagonal wire segment',line)
            else:assert row[0]==row[3] and row[1]==row[4],('NonzeroXY via segment',line)
            nets[name].append([int(row[0]),int(row[1]),row[2],int(row[3]),int(row[4]),row[5]])
    assert name is None and nets,('Truncated or absent routes',name)
    canonical={name:sorted(rows,key=lambda row:tuple(str(v) for v in row)) for name,rows in sorted(nets.items())}
    digest=hashlib.sha256(json.dumps(canonical,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    return dict(net_count=len(nets),segment_count=sum(map(len,nets.values())),canonical_sha256=digest,nets=canonical)

def roundtrip(source,other):
    a,b=parse_segments(source),parse_segments(other)
    assert a==b,'Segment netset/multiset/coordinates/layers changed during import or timing'
    return {k:v for k,v in a.items() if k!='nets'}
