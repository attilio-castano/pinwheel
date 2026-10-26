"""Fixed90-case ideal end-face R reference; no fitted endpoint subtraction.

Each of three source LEF corners uses this same30-net geometry. Explicit zero
route extensions make the conductor rectangle length equal the declared L.
Positive-area ideal BPin contacts touch the complete two end faces from outside.
This declared uniform-sheet reference is not contact/spreading/via qualification.
"""
from decimal import Decimal as D
import re

import streaming_8x4_rc_r_length_geometry as LEF
import streaming_8x4_rc_consumer as C
import streaming_8x4_rc_protocol as P

need=P.need
METALS=('Metal1','Metal2','Metal3','Metal4','TopMetal1')
WIDTHS=dict(zip(METALS,('.16','.20','.20','.20','1.64')))
DIRECTIONS=dict(zip(METALS,('HORIZONTAL','VERTICAL','HORIZONTAL','VERTICAL','HORIZONTAL')))
CORNERS=('ITF_MIN','ITF_TYP','ITF_MAX')
LENGTHS=(50,100,150)
TOP='model24_r_endface'
DBU=1000
DIE=(0,0,1200000,1000000)


def cases():
    result=[]
    for metal in METALS:
        for multiple in (1,2):
            width=int(D(WIDTHS[metal])*multiple*DBU)
            for length in LENGTHS:
                i=len(result);x=10000+(i%6)*200000;y=10000+(i//6)*200000
                start=[x,y];end=[x+length*DBU,y] if DIRECTIONS[metal]=='HORIZONTAL' else [x,y+length*DBU]
                if DIRECTIONS[metal]=='HORIZONTAL':
                    contacts=[[-100,-width//2,0,width//2],[0,-width//2,100,width//2]]
                    box=[x,y-width//2,end[0],y+width//2]
                else:
                    contacts=[[-width//2,-100,width//2,0],[-width//2,0,width//2,100]]
                    box=[x-width//2,y,x+width//2,end[1]]
                result.append(dict(index=i,name=metal+'_W'+str(multiple)+'_L'+str(length),layer=metal,
                    multiple=multiple,width_dbu=width,length_um=length,start=start,end=end,
                    zero_extensions=[0,0],body_dbu=box,contact_boxes=contacts,
                    ndr='WIDE' if multiple==2 else None,
                    native_shape_length_minus_width_dbu=length*DBU-width))
    need(len(result)==30 and len({r['name'] for r in result})==30,'Fixed30-net geometry differs')
    return result


def fixture():
    lines=['VERSION 5.8 ;','DIVIDERCHAR "/" ;','BUSBITCHARS "[]" ;','DESIGN '+TOP+' ;',
        'UNITS DISTANCE MICRONS 1000 ;','DIEAREA ( 0 0 ) ( 1200000 1000000 ) ;',
        'NONDEFAULTRULES 1 ;','- WIDE']
    for metal in METALS:
        w=int(D(WIDTHS[metal])*2*DBU);lines.append(' + LAYER '+metal+' WIDTH '+str(w)+' SPACING '+str(w))
    lines+=[' ;','END NONDEFAULTRULES','COMPONENTS 0 ;','END COMPONENTS','PINS 60 ;']
    for row in cases():
        for i,(suffix,direction,point) in enumerate((('A','INPUT',row['start']),('B','OUTPUT',row['end']))):
            box=row['contact_boxes'][i]
            lines += ['- '+row['name']+'_'+suffix+' + NET '+row['name']+' + DIRECTION '+direction+' + USE SIGNAL',
                ' + PORT + LAYER '+row['layer']+' ( '+str(box[0])+' '+str(box[1])+' ) ( '+str(box[2])+' '+str(box[3])+' )',
                ' + FIXED ( '+str(point[0])+' '+str(point[1])+' ) N ;']
    lines+=['END PINS','NETS 30 ;']
    for row in cases():
        a,b=row['start'],row['end'];ndr=' + NONDEFAULTRULE WIDE' if row['ndr'] else ''
        lines += ['- '+row['name']+' ( PIN '+row['name']+'_A ) ( PIN '+row['name']+'_B ) + USE SIGNAL'+ndr,
            ' + ROUTED '+row['layer']+' ( '+str(a[0])+' '+str(a[1])+' 0 ) ( '+str(b[0])+' '+str(b[1])+' 0 ) ;']
    return '\n'.join(lines+['END NETS','END DESIGN'])+'\n'


def section(text,name,count):
    matches=list(re.finditer(r'^'+name+r'\s+(\d+)\s*;\s*\n(.*?)^END '+name+r'\s*$',text,re.M|re.S))
    need(len(matches)==1 and int(matches[0][1])==count,'Missing/extra fixed '+name)
    rows=list(re.finditer(r'^\s*-\s+(\S+)\s+(.*?);',matches[0][2],re.M|re.S))
    need(len(rows)==count and len({r[1] for r in rows})==count,'Duplicate/missing '+name+' entries')
    need(not re.sub(r'^\s*-\s+\S+\s+.*?;','',matches[0][2],flags=re.M|re.S).strip(), 'Unparsed '+name+' data')
    return matches[0],{r[1]:r[2] for r in rows}


def geometry(text):
    need(type(text) is str and text.isascii() and '\r' not in text,'Only complete ASCII LF fixture DEF supported')
    expected=cases();nets_match,nets=section(text,'NETS',30);pins_match,pins=section(text,'PINS',60)
    ndr_match,ndrs=section(text,'NONDEFAULTRULES',1)
    need(set(ndrs)=={'WIDE'},'Unknown NDR')
    ndr_rows=re.findall(r'\+\s+LAYER\s+(\w+)\s+WIDTH\s+(\d+)\s+SPACING\s+(\d+)',ndrs['WIDE'])
    need(ndr_rows==[(m,str(int(D(WIDTHS[m])*2*DBU)),str(int(D(WIDTHS[m])*2*DBU))) for m in METALS],
        'Complete five-layer wide NDR differs')
    need(not re.sub(r'\+\s+LAYER\s+\w+\s+WIDTH\s+\d+\s+SPACING\s+\d+','',ndrs['WIDE']).strip(),'Extra NDR field')
    remaining=text
    for match in sorted((nets_match,pins_match,ndr_match),key=lambda m:m.start(),reverse=True):remaining=remaining[:match.start()]+remaining[match.end():]
    wanted=('VERSION 5.8 ; DIVIDERCHAR "/" ; BUSBITCHARS "[]" ; DESIGN '+TOP+' ; UNITS DISTANCE MICRONS 1000 ; '
        'DIEAREA ( 0 0 ) ( 1200000 1000000 ) ; COMPONENTS 0 ; END COMPONENTS END DESIGN')
    need(remaining.split()==wanted.split(),'Header/die/units/components/extra section differs')
    need(set(nets)=={r['name'] for r in expected} and set(pins)=={r['name']+'_'+s for r in expected for s in ('A','B')},
        'Fixed net/port membership differs')
    for row in expected:
        body=nets[row['name']];points=re.findall(r'\(\s+([*\d-]+)\s+([*\d-]+)\s+(-?\d+)\s+\)',body)
        need(len(points)==2 and all(p[2]=='0' for p in points),'Both actual route extensions must be explicit zero')
        decoded=[]
        for fields in points:
            decoded.append([decoded[-1][i] if v=='*' and decoded else int(v) for i,v in enumerate(fields[:2])])
        need(decoded==[row['start'],row['end']],'Actual route centerline differs')
        normalized=re.sub(r'\(\s+[*\d-]+\s+[*\d-]+\s+-?\d+\s+\)','',body)
        ports=re.findall(r'\(\s+PIN\s+(\S+)\s+\)',normalized)
        need(set(ports)=={row['name']+'_A',row['name']+'_B'} and len(ports)==2,'Actual net endpoint membership differs')
        normalized=re.sub(r'\(\s+PIN\s+\S+\s+\)','',normalized)
        tokens=normalized.split();wanted=['+','USE','SIGNAL']+(['+','NONDEFAULTRULE','WIDE'] if row['ndr'] else [])+['+','ROUTED',row['layer']]
        need(tokens==wanted,'Actual route layer/NDR/extra segment/via differs')
        for i,(suffix,direction,point) in enumerate((('A','INPUT',row['start']),('B','OUTPUT',row['end']))):
            # DEF writers may recenter BPin local rectangles. Compare the exact
            # physical rectangle after the N-oriented placement transform.
            pin=pins[row['name']+'_'+suffix]
            pattern=(r'\s*\+\s+NET\s+(\S+)\s+\+\s+DIRECTION\s+(INPUT|OUTPUT)\s+\+\s+USE\s+SIGNAL\s+'
                r'\+\s+PORT\s+\+\s+LAYER\s+(\S+)\s+\(\s*(-?\d+)\s+(-?\d+)\s*\)\s*\(\s*(-?\d+)\s+(-?\d+)\s*\)\s+'
                r'\+\s+FIXED\s+\(\s*(-?\d+)\s+(-?\d+)\s*\)\s+N\s*')
            match=re.fullmatch(pattern,pin);need(match is not None,'Unsupported end-face contact syntax/orientation')
            net,actual_direction,layer=match.group(1,2,3);x0,y0,x1,y1,px,py=map(int,match.group(4,5,6,7,8,9))
            actual=[x0+px,y0+py,x1+px,y1+py];box=row['contact_boxes'][i]
            wanted=[box[0]+point[0],box[1]+point[1],box[2]+point[0],box[3]+point[1]]
            need((net,actual_direction,layer)==(row['name'],direction,row['layer']) and actual==wanted,
                'Full-width end-face global contact/layer/connectivity differs')
    return dict(nets=30,ports=60,components=0,routed_vias=0,segments=30,explicit_zero_extensions=60,
        complete_geometry_checked=True,ideal_full_end_face_contacts=True,rows=expected)


def resistance(sheets):
    need(set(sheets)==set(METALS),'Every source sheet resistance required')
    return {r['name']:D(sheets[r['layer']])*D(r['length_um'])*DBU/D(r['width_dbu']) for r in cases()}
