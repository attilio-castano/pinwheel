"""Strict observed native-pattern grammar and full-stack role/coordinate witness.

Adapted only after the Root-owned 310-case native census. Native names/roles
are explicit records, never inferred from a FasterCap prefix or row position.
"""
from decimal import Decimal as D
import hashlib
import json
from pathlib import Path
import re

import streaming_8x4_model24_contract as K
import streaming_8x4_model24_geometry as A

G,P=A.G,A.P
NUM=r'[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?'
SETS={'1v2','3v2'}
FAMILIES={'Over1','Over3','Under1','Under3','OverUnder1','OverUnder3','UnderDiag1','UnderDiag3'}
REPRESENTATIVES=[
 '3v2/MODEL24_TYP/UnderDiag3/M4duM5/W0.2_W1.64/S0.21_S0_L10/wires',
 '3v2/MODEL24_TYP/UnderDiag3/M4duM5/W0.2_W1.64/S0.42_S6.56_L10/wires']


def number(text):
    P.need(re.fullmatch(NUM,text) is not None,'Invalid native decimal');value=D(text)
    P.need(value.is_finite() and abs(value)<D('1e6'),'Unbounded native decimal');return value


def parse(text,relative_path):
    path=Path(relative_path);parts=path.parts
    P.need(not path.is_absolute() and '..' not in parts and len(parts)==7 and parts[0] in SETS
        and parts[1]=='MODEL24_TYP' and parts[2] in FAMILIES and parts[-1]=='wires',
        'Only exact observed native pattern path grammar admitted')
    lines=[line.strip() for line in text.splitlines() if line.strip() and not line.lstrip().startswith('#')]
    expected='PATTERN '+'/'.join(parts[1:-1]);P.need(lines and lines[0]==expected,'Native PATTERN/path binding differs')
    grounds=[];wires=[];dielectrics=[];bbox=sim=None
    wire_pattern=re.compile(r'WIRE (\d+) (M\d+_w\d+) LL\s+('+NUM+r')\s+('+NUM+r') LR\s+('+NUM+r')\s+('+NUM+r') UR\s+('+NUM+r')\s+('+NUM+r') UL\s+('+NUM+r')\s+('+NUM+r')\s+LENGTH\s+('+NUM+r')\s+VOLTAGE\s+([01])')
    for line in lines[1:]:
        m=re.fullmatch(r'GROUND_PLANE (\d+) (M\d+_w\d+)\s+HEIGHT\s+('+NUM+r')\s+('+NUM+r')\s+THICKNESS\s+('+NUM+r')',line)
        if m:
            index,name,lo,hi,thickness=m.groups();a,b,t=map(number,(lo,hi,thickness))
            P.need(b>a and b-a==t,'Native ground-plane thickness mismatch')
            grounds.append(dict(index=int(index),name=name,local_bottom_um=str(a),local_top_um=str(b),thickness_um=str(t)));continue
        m=re.fullmatch(r'DIELECTRIC (\w+)\s+HEIGHT\s+('+NUM+r')\s+('+NUM+r')\s+EPSILON\s+('+NUM+r')',line)
        if m:
            name,lo,hi,er=m.groups();a,b,e=map(number,(lo,hi,er));P.need(b>a and e>0,'Invalid native dielectric')
            dielectrics.append(dict(name=name,local_bottom_um=str(a),local_top_um=str(b),er=str(e)));continue
        m=wire_pattern.fullmatch(line)
        if m:
            index,name,*rest=m.groups();values=list(map(number,rest[:-1]));x0,y0,x1,y00,x11,y1,x00,y11,length=values
            P.need(x0==x00 and x1==x11 and y0==y00 and y1==y11 and x1>x0 and y1>y0 and length>0,
                'Native nonrectangular/degenerate wire')
            wires.append(dict(index=int(index),name=name,local_bounds_um=list(map(str,[x0,x1,y0,y1])),
                nominal_length_um=str(length),voltage=int(rest[-1])));continue
        m=re.fullmatch(r'WINDOW_BBOX\s+LL\s+('+NUM+r')\s+('+NUM+r')\s+UR\s+('+NUM+r')\s+('+NUM+r')\s+LENGTH\s+('+NUM+r')',line)
        if m:
            P.need(bbox is None,'Duplicate native WINDOW_BBOX');v=list(map(number,m.groups()))
            P.need(v[2]>v[0] and v[3]>v[1] and v[4]>0,'Invalid native window');bbox=list(map(str,v));continue
        m=re.fullmatch(r'SIM_WIN_EXT\s+LL\s+('+NUM+r')\s+('+NUM+r')\s+UR\s+('+NUM+r')\s+('+NUM+r')\s+LENGTH\s+('+NUM+r')\s+('+NUM+r')',line)
        if m:
            P.need(sim is None,'Duplicate native SIM_WIN_EXT');sim=list(map(str,map(number,m.groups())));continue
        raise ValueError('Unsupported/unobserved native pattern record: '+line[:100])
    P.need(grounds and wires and dielectrics and bbox is not None and sim is not None,
        'Incomplete native pattern record membership')
    span=number(bbox[2])-number(bbox[0])
    P.need(list(map(number,sim))==[-span,D(0),span,D(0),D(0),number(bbox[4])],
        'Native simulation-window transform differs from observed bbox convention')
    P.need(len({r['name'] for r in grounds+wires})==len(grounds)+len(wires)
        and len({r['index'] for r in wires})==len(wires)
        and len({r['name'] for r in dielectrics})==len(dielectrics)
        and all(r['nominal_length_um']==bbox[-1] for r in wires)
        and sum(r['voltage']==1 for r in wires)==1,'Native role/name/index/length/target identity differs')
    primary=1 if parts[0]=='1v2' else 3;family=parts[2]
    P.need(family.endswith(str(primary)),'Native pattern set/family multiplicity differs')
    target=next(w for w in wires if w['voltage']==1);target_met=int(re.fullmatch(r'M(\d+)_w\d+',target['name'])[1])
    target_wires=[w for w in wires if int(re.fullmatch(r'M(\d+)_w\d+',w['name'])[1])==target_met]
    P.need(len(target_wires)==primary and target['index']==(1 if primary==1 else 2),
        'Native selected target/middle-wire identity differs')
    if family.startswith('UnderDiag'):
        m=re.fullmatch(r'M(\d+)duM(\d+)',parts[3]);P.need(m is not None,'Native diagonal metal path differs')
        a,b=map(int,m.groups());wanted_grounds=[0];other=[w for w in wires if w not in target_wires]
        P.need(len(other)==2 and all(w['name'].startswith('M'+str(b)+'_') for w in other),'Native diagonal role membership differs')
    elif family.startswith('OverUnder'):
        m=re.fullmatch(r'M(\d+)oM(\d+)uM(\d+)',parts[3]);P.need(m is not None,'Native over/under metal path differs')
        a,b,c=map(int,m.groups());wanted_grounds=[b,c];P.need(len(wires)==primary,'Unexpected context wire')
    elif family.startswith('Over'):
        m=re.fullmatch(r'M(\d+)oM(\d+)',parts[3]);P.need(m is not None,'Native over metal path differs')
        a,b=map(int,m.groups());wanted_grounds=[b];P.need(len(wires)==primary,'Unexpected context wire')
    else:
        m=re.fullmatch(r'M(\d+)uM(\d+)',parts[3]);P.need(m is not None,'Native under metal path differs')
        a,b=map(int,m.groups());wanted_grounds=[0,b];P.need(len(wires)==primary,'Unexpected context wire')
    P.need(a==target_met and [int(re.fullmatch(r'M(\d+)_w\d+',g['name'])[1]) for g in grounds]==wanted_grounds,
        'Native declared metal path/ground roles differ')
    width_match=re.fullmatch(r'W('+NUM+r')_W('+NUM+r')',parts[4]);space_match=re.fullmatch(r'S('+NUM+r')_S('+NUM+r')_L('+NUM+r')',parts[5])
    P.need(width_match is not None and space_match is not None,'Native width/spacing/length path differs')
    width,other_width=map(number,width_match.groups());spacing,other_spacing,length_factor=map(number,space_match.groups())
    P.need(width>0 and other_width>0 and spacing>0 and other_spacing>=0 and length_factor>0
        and all(number(w['local_bounds_um'][1])-number(w['local_bounds_um'][0])==width for w in target_wires)
        and all(number(w['nominal_length_um'])==width*length_factor for w in wires),
        'Native path width/length differs from actual wire rectangles')
    ordered=sorted(target_wires,key=lambda w:w['index'])
    P.need(all(number(right['local_bounds_um'][0])-number(left['local_bounds_um'][1])==spacing
        for left,right in zip(ordered,ordered[1:])),'Native primary-wire spacing differs from path')
    if family.startswith('UnderDiag'):
        other=sorted([w for w in wires if w not in target_wires],key=lambda w:w['index'])
        P.need(all(number(w['local_bounds_um'][1])-number(w['local_bounds_um'][0])==other_width for w in other)
            and number(other[0]['local_bounds_um'][0])-number(target['local_bounds_um'][0])==other_spacing,
            'Native diagonal width/offset differs from path')
    return dict(path=relative_path,pattern='/'.join(parts[1:-1]),set=parts[0],family=parts[2],
        grounds=grounds,wires=wires,dielectrics=dielectrics,window_bbox=bbox,sim_window=sim,
        raw_sha256=hashlib.sha256(text.encode()).hexdigest())


def normalize(text,path,itf_text):
    row=parse(text,path);stack=G.stack(G.parse_itf(itf_text));metals=['Metal1','Metal2','Metal3','Metal4','TopMetal1']
    offsets=[];records=[]
    for kind,items in [('ground',row['grounds']),('wire',row['wires'])]:
        for item in items:
            match=re.fullmatch(r'M(\d+)_w(\d+)',item['name']);metal=int(match[1])
            P.need(0<=metal<=5 and (kind=='ground' or metal>0),'Invalid native routing metal')
            if kind=='ground':local_lo,local_hi=map(D,[item['local_bottom_um'],item['local_top_um']])
            else:local_lo,local_hi=map(D,item['local_bounds_um'][2:])
            if metal==0:
                P.need(kind=='ground' and local_hi==0,'Only observed substrate ground M0 at local0 supported')
                offset=D(0);global_lo,global_hi=local_lo,local_hi
            else:
                selected=stack['metals'][metals[metal-1]];global_lo,global_hi=map(D,[selected['bottom_um'],selected['top_um']])
                P.need(global_hi-global_lo==local_hi-local_lo,'Native conductor thickness differs from source ITF')
                offset=global_lo-local_lo;P.need(global_hi-local_hi==offset,'Native metal coordinate shift is inconsistent')
            offsets.append(offset);records.append(dict(kind=kind,native=item,metal=metal,global_bottom_um=str(global_lo),global_top_um=str(global_hi)))
    P.need(len(set(offsets))==1,'Native roles imply conflicting physical stack offsets')
    offset=offsets[0]
    # Check every actually printed dielectric interval against the full ITF
    # material partition; equal-er native subslabs need not share ITF labels.
    for dielectric in row['dielectrics']:
        lo,hi=D(dielectric['local_bottom_um'])+offset,D(dielectric['local_top_um'])+offset;er=D(dielectric['er'])
        cuts={lo,hi}
        for slab in stack['slabs']:
            cuts.update(x for x in (D(slab['lo_um']),D(slab['hi_um'])) if lo<x<hi)
        for a,b in zip(sorted(cuts),sorted(cuts)[1:]):
            middle=(a+b)/2;matches=[s for s in stack['slabs'] if D(s['lo_um'])<middle<D(s['hi_um'])]
            expected=D(matches[0]['er']) if matches else D('1') if middle>=D(stack['top_um']) else None
            P.need(expected is not None and expected==er,'Native dielectric/coordinate interval differs from ITF')
    return dict(native=row,full_stack=stack,physical_records=records,local_to_global_y_offset_um=str(offset),
        every_conductor_and_printed_dielectric_checked=True,source_material_sha256=hashlib.sha256(itf_text.encode()).hexdigest(),
        coordinate_transform_is_translation_only=True,model_qualified=False)


def build(text,path,itf_text,length_um='20',extension_um='20'):
    P.need(length_um in ('10','20','30') and extension_um in ('20','30'),'Fixed observed representative length/extension required')
    row=normalize(text,path,itf_text);length,ext=D(length_um),D(extension_um);native=row['native'];bs=[];roles=[]
    x0,x1=D(native['window_bbox'][0])-ext,D(native['window_bbox'][2])+ext
    for record in row['physical_records']:
        item=record['native'];kind=record['kind'];ordinal=len(bs)+1
        name=('GROUND_' if kind=='ground' else 'WIRE_')+str(ordinal)+'_'+item['name'].upper()
        if kind=='ground':values=[x0,x1,D(record['global_bottom_um']),D(record['global_top_um']),-ext,length+ext]
        else:values=[D(item['local_bounds_um'][0]),D(item['local_bounds_um'][1]),D(record['global_bottom_um']),D(record['global_top_um']),D(0),length]
        bs.append(dict(name=name,bounds=tuple(map(G.um,values))))
        roles.append(dict(ordinal=ordinal,name=name,role='ground' if kind=='ground' else 'signal',matrix_name='g'+str(ordinal)+'_'+name,
            origin=kind+' native '+item['name']+' index'+str(item['index'])+(' voltage'+str(item['voltage']) if kind=='wire' else '')))
    K.role_names(roles);anchor=next(r['name'] for r in roles if r['role']=='ground')
    operator_boxes=[dict(b,name='GND_SUB' if b['name']==anchor else b['name']) for b in bs]
    run=dict(lateral_and_longitudinal_ground_extension_um=extension_um)
    faces,boundary=G.layered(operator_boxes,{},run,row['full_stack'])
    for face in faces:
        if face['kind']=='C' and face['name']=='GND_SUB':face['name']=anchor
    certificate=G.certify(bs,faces);certificate.update(boundary=boundary,physical_anchor_ground=anchor,
        internal_anchor_rename_is_bijective_and_not_a_new_substrate=True,
        local_to_global_y_offset_um=row['local_to_global_y_offset_um'],wire_length_um=length_um,
        ground_extension_um=extension_um,coordinate_unit_m=G.COORDINATE_UNIT_M,model_qualified=False)
    files,unit_map=G.normalize_s20(G.emit(bs,faces));files['unit-map.json']=json.dumps(unit_map,indent=2)+'\n'
    return dict(normalization=row,ordered_conductor_roles=roles,files=files,certificate=certificate,
        geometry_operator_sha256=P.sha(G.__file__),same_frozen_operator_with_explicit_bijective_anchor_name=True,
        no_native_conductor_omitted_or_added=True,model_qualified=False)
