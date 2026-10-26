# New campaign-owned source snapshot, reviewed from retained local evidence.
# Derivation input SHA256: d377b793278c295b9ea84778cb0f63642e1ece87b27de1edd102d07d7fa65838
# No archived module is imported or executed; only this new source is used.
"""Owned TYP-only finite geometry translation; no solver is launched here."""
from collections import Counter,defaultdict
from decimal import Decimal
from fractions import Fraction as F
from itertools import product
import hashlib
import json
import re
import struct


def need(value,message):
    if not value:raise ValueError(message)


def dot(a,b):return sum(x*y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def f32(value):return struct.unpack('!f',struct.pack('!f',float(value)))[0]
def quantize(value):return F.from_float(f32(value))
def um(value):return quantize(Decimal(str(value))/Decimal(1000000))
def token(value):return format(float(value),'.17g')


def parse_itf(text):
    lines=[line.strip() for line in text.splitlines() if line.strip() and not line.lstrip().startswith('$')]
    need(lines.pop(0)=='TECHNOLOGY = sg13cmos5l','Unexpected ITF technology')
    rows={}
    for line in lines:
        m=re.fullmatch(r'(DIELECTRIC|CONDUCTOR|VIA)\s+(\w+)\s*\{([^{}]+)\}',line)
        need(m is not None,'Unsupported ITF syntax');kind,name,body=m.groups();fields={}
        for item in body.split():
            pair=item.split('=');need(len(pair)==2 and pair[0] not in fields,'Duplicate/malformed ITF field')
            fields[pair[0]]=pair[1]
        need(name not in rows,'Duplicate ITF layer')
        if kind=='DIELECTRIC':need(set(fields)=={'THICKNESS','ER'},'Unexpected dielectric fields')
        elif kind=='CONDUCTOR':need(set(fields) in ({'THICKNESS','WMIN','SMIN','RPSQ'},{'THICKNESS','WMIN','SMIN','RPSQ','LAYER_TYPE'}),'Unexpected conductor fields')
        else:need(set(fields)=={'FROM','TO','AREA','RPV'},'Unexpected via fields')
        for key,value in fields.items():
            if key not in ('LAYER_TYPE','FROM','TO'):
                number=Decimal(value);need(number.is_finite() and number>0,'Nonpositive/nonfinite ITF value')
        rows[name]=dict(kind=kind,**fields)
    return rows


def stack(rows):
    # Explicit retained routing-height convention: metal embeds in its following
    # dielectric, so conductor thickness is not added again to dielectric height.
    names=['fox','nitride','dummyOx','ox1','ox2','ox3','ox4','oxTopMetal1','nitTop']
    y=Decimal(0);slabs=[];metals={};before={'ox1':'Metal1','ox2':'Metal2','ox3':'Metal3','ox4':'Metal4','oxTopMetal1':'TopMetal1'}
    for name in names:
        row=rows[name];need(row['kind']=='DIELECTRIC','Wrong dielectric kind')
        if name in before:
            metal=before[name];m=rows[metal];need(m['kind']=='CONDUCTOR','Wrong routing conductor kind')
            metals[metal]=dict(bottom_um=str(y),top_um=str(y+Decimal(m['THICKNESS'])),**m)
        top=y+Decimal(row['THICKNESS']);slabs.append(dict(name=name,lo_um=str(y),hi_um=str(top),er=row['ER']));y=top
    need(rows['air']['ER']=='1.0','Unexpected external air assumption')
    return dict(slabs=slabs,metals=metals,top_um=str(y),outside_er='1.0',below_zero_er='4.1',
        convention='fox+nitride+dummyOx below M1; oxN includes lower metal. Active/poly/trench are excluded from routing height; finite below-zero er4.1 is a pilot truncation assumption.')


def boxes(case,run):
    length=Decimal(run['wire_length_um']);ext=Decimal(run['lateral_and_longitudinal_ground_extension_um'])
    result=[]
    for wire in case['wires']:
        result.append(dict(name=wire['name'],bounds=tuple(map(um,[wire['x0_um'],wire['x1_um'],wire['y0_um'],wire['y1_um'],'0',length]))))
    x0=min(Decimal(w['x0_um']) for w in case['wires'])-ext;x1=max(Decimal(w['x1_um']) for w in case['wires'])+ext
    result.insert(0,dict(name='GND_SUB',bounds=tuple(map(um,[x0,x1,'-0.4','0',-ext,length+ext]))))
    if case['extra_ground_plane']=='Metal3':result.insert(1,dict(name='GND_M3',bounds=tuple(map(um,[x0,x1,case['ground_M3_bottom_um'],case['ground_M3_top_um'],-ext,length+ext]))))
    if run['phase']=='name_permutation':result=[next(b for b in result if b['name']==name) for name in run['expected_names']]
    need([b['name'] for b in result]==run['expected_names'],'Planned conductor order differs')
    for b in result:
        v=b['bounds'];need(all(v[2*a]<v[2*a+1] for a in range(3)),'Degenerate box')
    for i,a in enumerate(result):
        for b in result[i+1:]:
            need(not all(max(a['bounds'][2*k],b['bounds'][2*k])<min(a['bounds'][2*k+1],b['bounds'][2*k+1]) for k in range(3)),'Overlapping conductors')
    return result


def quad(axis,plane,ranges,sign):
    other=[a for a in range(3) if a!=axis];vertices=[]
    for u,v in [(0,0),(1,0),(1,1),(0,1)]:
        p=[None]*3;p[axis]=plane;p[other[0]]=ranges[0][u];p[other[1]]=ranges[1][v];vertices.append(tuple(p))
    if sign!=(1 if axis!=1 else -1):vertices.reverse()
    return vertices


def uniform(bs):
    faces=[]
    for b in bs:
        for axis in range(3):
            other=[a for a in range(3) if a!=axis];ranges=[b['bounds'][2*a:2*a+2] for a in other]
            for side,sign in [(0,-1),(1,1)]:faces.append(dict(kind='C',name=b['name'],er='4.1',vertices=quad(axis,b['bounds'][2*axis+side],ranges,sign)))
    return faces


def layered(bs,case,run,model):
    ext=um(run['lateral_and_longitudinal_ground_extension_um']);ground=next(b['bounds'] for b in bs if b['name']=='GND_SUB')
    bounds=tuple(map(quantize,(ground[0]-ext,ground[1]+ext,ground[2]-ext,um(model['top_um']),ground[4]-ext,ground[5]+ext)))
    slabs=[(um(s['lo_um']),um(s['hi_um']),s['er']) for s in model['slabs']]
    def label(p):
        for b in bs:
            if all(b['bounds'][2*a]<p[a]<b['bounds'][2*a+1] for a in range(3)):return ('C',b['name'])
        if not all(bounds[2*a]<p[a]<bounds[2*a+1] for a in range(3)):return ('D','1.0')
        if p[1]<0:return ('D',model['below_zero_er'])
        for lo,hi,er in slabs:
            if lo<p[1]<hi:return ('D',er)
        raise ValueError('Point on a material boundary')
    cuts=[]
    for axis in range(3):
        values={bounds[2*axis],bounds[2*axis+1]}
        for b in bs:values.update(b['bounds'][2*axis:2*axis+2])
        if axis==1:
            for lo,hi,er in slabs:values.update((lo,hi))
        cuts.append(sorted(values))
    cells={}
    for index in product(*(range(len(c)-1) for c in cuts)):
        cells[index]=label(tuple((cuts[a][index[a]]+cuts[a][index[a]+1])/2 for a in range(3)))
    groups=defaultdict(set)
    for axis in range(3):
        other=[a for a in range(3) if a!=axis]
        for plane in range(len(cuts[axis])):
            for u,v in product(range(len(cuts[other[0]])-1),range(len(cuts[other[1]])-1)):
                left=[0]*3;left[axis]=plane-1;left[other[0]]=u;left[other[1]]=v;right=left.copy();right[axis]+=1
                a=cells.get(tuple(left),('D','1.0'));b=cells.get(tuple(right),('D','1.0'))
                if a==b:continue
                need(not(a[0]=='C' and b[0]=='C'),'Touching distinct conductors')
                if a[0]=='C':key=('C',a[1],b[1],axis,plane,1)
                elif b[0]=='C':key=('C',b[1],a[1],axis,plane,-1)
                else:key=('D',a[1],b[1],axis,plane,1)
                groups[key].add((u,v))
    expected_tiles={key:set(mask) for key,mask in groups.items()}
    faces=[];covered=defaultdict(set);unit_faces=sum(map(len,groups.values()))
    for key,mask in sorted(groups.items()):
        kind,first,second,axis,plane,sign=key;other=[a for a in range(3) if a!=axis]
        while mask:
            u,v=min(mask);u1=u+1
            while (u1,v) in mask:u1+=1
            v1=v+1
            while all((x,v1) in mask for x in range(u,u1)):v1+=1
            for x,y in product(range(u,u1),range(v,v1)):mask.remove((x,y))
            # A separate coverage witness checks the merged emission against all
            # material-adjacency grid tiles, including the ground-interface hole.
            for tile in product(range(u,u1),range(v,v1)):
                need(tile not in covered[key],'Overlapping merged boundary tile');covered[key].add(tile)
            ranges=[(cuts[other[0]][u],cuts[other[0]][u1]),(cuts[other[1]][v],cuts[other[1]][v1])]
            vertices=quad(axis,cuts[axis][plane],ranges,sign)
            if kind=='C':face=dict(kind=kind,name=first,er=second,vertices=vertices)
            else:
                center=tuple(sum(p[a] for p in vertices)/4 for a in range(3));ref=list(center)
                distances=[abs(cuts[axis][i]-cuts[axis][plane]) for i in [plane-1,plane+1] if 0<=i<len(cuts[axis])]
                ref[axis]+=min(distances)/4
                face=dict(kind='D',in_er=first,out_er=second,reference=tuple(map(quantize,ref)),vertices=vertices)
                need(label(face['reference'])==('D',second),'Wrong dielectric reference side')
            faces.append(face)
    need(dict(covered)==expected_tiles,'Incomplete material partition boundary')
    return faces,dict(finite_prism_bounds_m=[str(v) for v in bounds],outside_er='1.0',below_zero_er='4.1',grid_cells=len(cells),unmerged_boundary_tiles=unit_faces,
        every_material_adjacency_tile_covered_once=True,closed_finite_partition=True,
        boundary_policy='Ground extension E; dielectric x/z boundary one further E beyond ground and bottom one E below substrate box. Top at nitTop/air. Explicit finite air exterior; boundary phase enlarges E20 to E40.')


def certify(bs,faces):
    records={};seen=set()
    for face in faces:
        v=face['vertices'];need(len(v)==4 and len(set(v))==4,'Degenerate quadrilateral')
        n=cross(sub(v[1],v[0]),sub(v[2],v[0]));need(dot(n,n)>0 and dot(n,sub(v[3],v[0]))==0,'Nonplanar/degenerate face')
        shape=tuple(sorted(v));need(shape not in seen,'Duplicate/coincident interface');seen.add(shape)
        if face['kind']=='D':
            need(F(Decimal(face['out_er']))>0 and F(Decimal(face['in_er']))>0 and face['out_er']!=face['in_er'],'Invalid dielectric material')
            need(dot(n,sub(face['reference'],v[0]))>0,'Dielectric reference on wrong side')
    for b in bs:
        fs=[f for f in faces if f['kind']=='C' and f['name']==b['name']];edges=Counter();vertices=set();volume=F(0)
        center=tuple((b['bounds'][2*a]+b['bounds'][2*a+1])/2 for a in range(3))
        for face in fs:
            v=face['vertices'];n=cross(sub(v[1],v[0]),sub(v[2],v[0]));need(dot(n,sub(v[0],center))>0,'Inward conductor face')
            for a,c in zip(v,v[1:]+v[:1]):edges[(a,c)]+=1;vertices.add(a)
            for i,j,k in [(0,1,2),(0,2,3)]:volume+=dot(v[i],cross(v[j],v[k]))/6
        need(edges and all(count==1 and edges[(c,a)]==1 for (a,c),count in edges.items()),'Conductor mesh is not closed/oppositely oriented')
        need(len(vertices)-len(edges)//2+len(fs)==2,'Conductor Euler characteristic')
        expected=F(1)
        for a in range(3):expected*=b['bounds'][2*a+1]-b['bounds'][2*a]
        need(volume==expected,'Conductor enclosed volume differs from independent box dimensions')
        records[b['name']]=dict(faces=len(fs),vertices=len(vertices),edges=len(edges)//2,euler=2,volume_m3=str(volume),bounds_m=[str(x) for x in b['bounds']],surface_er=sorted({f['er'] for f in fs}))
    need(set(f['name'] for f in faces if f['kind']=='C')==set(records),'Unexpected conductor')
    return dict(conductors=records,dielectric_faces=sum(f['kind']=='D' for f in faces),all_faces=len(faces),exact_rational_geometry=True,
        numeric_input='Coordinates explicitly round to upstream sscanf binary32, serialized with17 digits; um converted to SI meters once before float32.')


def emit(bs,faces):
    files={};lines=['* Owned finite TYP pilot; coordinates SI meters; epsilon relative']
    for b in bs:
        groups=defaultdict(list)
        for face in faces:
            if face['kind']=='C' and face['name']==b['name']:groups[face['er']].append(face)
        items=sorted(groups.items())
        for i,(er,fs) in enumerate(items):
            name=f'c_{b["name"]}_{i}.qui';files[name]='* conductor '+b['name']+'\n'+''.join('Q '+b['name']+' '+' '.join(token(x) for v in f['vertices'] for x in v)+'\n' for f in fs)
            lines.append(f'C {name} {er} 0 0 0'+(' +' if i<len(items)-1 else ''))
    for i,f in enumerate(face for face in faces if face['kind']=='D'):
        name=f'd_{i:03}.qui';files[name]='* dielectric reference is on outperm side\nQ IF '+' '.join(token(x) for v in f['vertices'] for x in v)+'\n'
        lines.append(f'D {name} {f["out_er"]} {f["in_er"]} 0 0 0 '+' '.join(token(x) for x in f['reference']))
    files['geometry.lst']='\n'.join(lines)+'\n'
    return files


S20 = 1048576
COORDINATE_UNIT_M = '0.00000095367431640625'


def normalize_s20(files):
    """Exact power-of-two coordinate rescale, including dielectric references.

    Physical vertices already represent source-parser binary32 SI coordinates.
    Rescaling by 2**20 is checked exactly, rather than re-rounding requested
    physical dimensions under a different coordinate convention.
    """
    result = {}; witness = []
    for name, text in files.items():
        lines = []
        for line_number, line in enumerate(text.splitlines(), 1):
            fields = line.split()
            if fields and fields[0] == 'Q':
                need(len(fields) == 14, 'Unsupported quadrilateral normalization')
                indices = range(2, 14)
            elif fields and fields[0] == 'D':
                need(len(fields) == 10 and fields[4:7] == ['0', '0', '0'], 'Unexpected dielectric offset/reference grammar')
                indices = range(7, 10)
            else:
                lines.append(line.replace('coordinates SI meters', 'raw coordinates=2**20 * SI metres'))
                continue
            original, scaled = [], []
            for index in indices:
                physical = F.from_float(float(fields[index]))
                need(quantize(physical) == physical, 'SI coordinate is not exact parser binary32')
                raw = physical * S20
                need(quantize(raw) == raw and raw / S20 == physical, 'S20 coordinate is not exact/reversible binary32')
                fields[index] = token(raw)
                need(F.from_float(f32(float(fields[index]))) / S20 == physical, 'Serialized S20 coordinate readback differs')
                original.append(str(physical)); scaled.append(str(raw))
            witness.append(dict(file=name, line=line_number, SI_m=original, emitted_coordinate=scaled,
                                source_parser_binary32_roundtrip_exact=True))
            lines.append(' '.join(fields))
        result[name] = '\n'.join(lines) + '\n'
    unit_map = dict(schema='pinwheel.streaming-8x4-layered-S20-unit-map.v1', S=S20,
                    coordinate_unit_m=COORDINATE_UNIT_M, physical_units='m',
                    capacitance_physical_F_equals_raw_times_coordinate_unit_m=True,
                    exact_binary32_coordinate_scaling=True, all_coordinate_and_reference_witnesses=witness,
                    SI_files_sha256={n:hashlib.sha256(t.encode()).hexdigest() for n,t in files.items()},
                    emitted_files_sha256={n:hashlib.sha256(t.encode()).hexdigest() for n,t in result.items()})
    need(witness and all(n in unit_map['emitted_files_sha256'] for n in files), 'Empty/incomplete scaling witness')
    return result, unit_map


def from_plan(case, length_um, extension_um):
    """Construct only the predeclared actual-ITF M1 finite 3D interfaces.

    SI coordinates undergo the solver input's binary32 quantization once. The
    interface geometry is a bounded pilot; outer-domain error remains measured.
    """
    need(length_um in ('10', '20', '30') and extension_um in ('20', '30'),
         'Undeclared layered finite geometry')
    need(extension_um != '30' or length_um in ('20', '30'), 'Undeclared extension/length combination')
    wires = []
    for row in case['rectangles']:
        x0, x1, y0, y1 = row['bounds_um']
        wires.append(dict(name=row['name'], x0_um=x0, x1_um=x1, y0_um=y0, y1_um=y1))
    geometry_case = dict(wires=wires, extra_ground_plane=None)
    run = dict(wire_length_um=length_um, lateral_and_longitudinal_ground_extension_um=extension_um,
               expected_names=['GND_SUB']+[r['name'] for r in case['rectangles']], phase='layered')
    layers = case['epsilon_layers']
    need(layers[-1][2] == '1' and layers[-1][1] == '1000', 'Unexpected external air slab')
    model = dict(slabs=[dict(lo_um=a, hi_um=b, er=er) for a,b,er in layers[:-1]],
                 top_um=layers[-1][0], below_zero_er='4.1')
    bs = boxes(geometry_case,run)
    faces, boundary = layered(bs,geometry_case,run,model)
    certificate = certify(bs,faces)
    certificate['boundary'] = boundary
    certificate['coordinate_unit_m'] = COORDINATE_UNIT_M
    certificate['numeric_input'] = 'Physical SI coordinates quantized to parser binary32 once, then exact 2**20 numerical rescaling; physical C equals raw C / 2**20 once.'
    certificate['case'] = case['name']
    certificate['wire_length_um'] = length_um
    certificate['ground_extension_um'] = extension_um
    certificate['model_qualified'] = False
    files, unit_map = normalize_s20(emit(bs,faces))
    files['unit-map.json'] = json.dumps(unit_map, indent=2) + '\n'
    certificate['unit_map_sha256'] = hashlib.sha256(files['unit-map.json'].encode()).hexdigest()
    return files, certificate
