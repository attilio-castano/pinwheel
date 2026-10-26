"""Fixed 45-net actual-via-family arithmetic geometry; no physical fit.

Generated definitions remain block dbVias. Their exact boxes are derived from
the pinned dbVia.cpp create_via_boxes integer algorithm, not from R data.
"""
from decimal import Decimal as D
import re
import streaming_8x4_model24_route_def as R
import streaming_8x4_model24_r_endpoint_geometry as OLD

need=R.need
METALS=OLD.METALS
DEFAULT=dict(zip(METALS,(160,200,200,200,1640)))
PG=dict(zip(METALS,(440,1000,2100,2100,1640)))
NAMED=('Via1_XY','Via1_YY','Via2_YX','Via3_XY')
GENERATED=('via1_2_1000_440_1_2_410_410','via2_3_1000_2100_4_2_480_480','via3_4_2100_2100_4_4_480_480')
FAMILIES=NAMED+GENERATED
LENGTHS=(50,100,150)
TOP='model24_actual_via_arithmetic'
DIE=(0,0,1600000,1800000)


def definitions(census):
    used=census['census']['via_usage'];need(set(used)==set(FAMILIES),'Exact actual seven-family census required')
    result={n:used[n]['definition'] for n in FAMILIES}
    need([result[n]['cut_count'] for n in FAMILIES]==[1,1,1,1,2,8,16],'Actual cut-family membership differs')
    need(all(used[n]['orientations']=={'N':used[n]['placements']} for n in FAMILIES),'Only actual N-oriented family scope admitted')
    return result


def boxes(definition):
    if definition['kind']=='technology_via':return definition['rectangles_dbu']
    p=definition['parameters'];need(set(p)=={'VIARULE','CUTSIZE','LAYERS','CUTSPACING','ENCLOSURE','ROWCOL'},'Unadmitted generated-via parameter')
    sx,sy=p['CUTSIZE'];dx,dy=p['CUTSPACING'];rows,cols=p['ROWCOL'];bx,by,tx,ty=p['ENCLOSURE']
    need(all(type(v)is int and v>0 for v in (sx,sy,rows,cols)),'Invalid generated cut dimensions')
    xmax=cols*sx+(cols-1)*dx;ymax=rows*sy+(rows-1)*dy;cx=xmax//2;cy=ymax//2
    cuts=[[j*(sx+dx)-cx,i*(sy+dy)-cy,j*(sx+dx)+sx-cx,i*(sy+dy)+sy-cy]for i in range(rows)for j in range(cols)]
    lo,cut,hi=p['LAYERS'];need(len(cuts)==definition['cut_count'],'Generated cut count differs')
    return {lo:[[-cx-bx,-cy-by,xmax-cx+bx,ymax-cy+by]],cut:cuts,hi:[[-cx-tx,-cy-ty,xmax-cx+tx,ymax-cy+ty]]}


def cases(defs):
    result=[]
    families=[(n,defs[n]['layers'][0],defs[n]['layers'][2],n in GENERATED) for n in FAMILIES]
    for name,lo,hi,pg in families:
        for length in LENGTHS:
            i=len(result);x=20000+(i%6)*250000;y=20000+(i//6)*200000;delta=length*1000
            middle=[x+delta,y]if OLD.DIRECTIONS[lo]=='HORIZONTAL'else[x,y+delta]
            end=[middle[0]+delta,middle[1]]if OLD.DIRECTIONS[hi]=='HORIZONTAL'else[middle[0],middle[1]+delta]
            result.append(dict(name='V'+str(FAMILIES.index(name))+'_L'+str(length),family=name,pg=pg,
                layers=[lo,hi],widths=[(PG if pg else DEFAULT)[lo],(PG if pg else DEFAULT)[hi]],
                points=[[x,y],middle,middle,end],length_um=length,cut_count=defs[name]['cut_count']))
    for metal in METALS[:4]:
        for pg in (False,True):
            for length in LENGTHS:
                i=len(result);x=20000+(i%6)*250000;y=20000+(i//6)*200000;delta=length*1000
                end=[x+delta,y]if OLD.DIRECTIONS[metal]=='HORIZONTAL'else[x,y+delta]
                result.append(dict(name=metal+('_PG'if pg else '_D')+'_L'+str(length),family=None,pg=pg,
                    layers=[metal],widths=[(PG if pg else DEFAULT)[metal]],points=[[x,y],end],length_um=length))
    need(len(result)==45 and len({r['name']for r in result})==45,'Exact45-net universe differs')
    return result


def ports(row):
    result=[]
    for i,(suffix,direction,point)in enumerate((('A','INPUT',row['points'][0]),('B','OUTPUT',row['points'][-1]))):
        layer=row['layers'][0 if i==0 else -1];w=row['widths'][0 if i==0 else -1]
        box=([-100,-w//2,0,w//2]if i==0 else[0,-w//2,100,w//2])if OLD.DIRECTIONS[layer]=='HORIZONTAL'else([-w//2,-100,w//2,0]if i==0 else[-w//2,0,w//2,100])
        result.append(dict(name=row['name']+'_'+suffix,net=row['name'],direction=direction,layer=layer,point=point,
            local=box,global_box=[box[j]+point[j%2]for j in range(4)]))
    return result


def fixture(defs):
    lines=['VERSION 5.8 ;','DIVIDERCHAR "/" ;','BUSBITCHARS "[]" ;','DESIGN '+TOP+' ;',
        'UNITS DISTANCE MICRONS 1000 ;','DIEAREA ( 0 0 ) ( 1600000 1800000 ) ;','VIAS 3 ;']
    for name in GENERATED:
        p=defs[name]['parameters'];lines+=['- '+name+' + VIARULE '+p['VIARULE']]
        for field in ('CUTSIZE','LAYERS','CUTSPACING','ENCLOSURE','ROWCOL'):lines.append(' + '+field+' '+' '.join(map(str,p[field])))
        lines.append(' ;')
    lines+=['END VIAS','NONDEFAULTRULES 1 ;','- ACTUAL_PG']
    for m in METALS:lines.append(' + LAYER '+m+' WIDTH '+str(PG[m])+' SPACING '+str(PG[m]))
    lines+=[' ;','END NONDEFAULTRULES','COMPONENTS 0 ;','END COMPONENTS','PINS 90 ;']
    for row in cases(defs):
        for p in ports(row):
            a=p['local'];x,y=p['point'];lines+=['- '+p['name']+' + NET '+p['net']+' + DIRECTION '+p['direction']+' + USE SIGNAL',
                f' + PORT + LAYER {p["layer"]} ( {a[0]} {a[1]} ) ( {a[2]} {a[3]} )',f' + FIXED ( {x} {y} ) N ;']
    lines+=['END PINS','NETS 45 ;']
    for row in cases(defs):
        n=row['name'];route=' + ROUTED '+row['layers'][0]
        for i,p in enumerate(row['points']):
            route+=' ( '+str(p[0])+' '+str(p[1])+' 0 )'
            if row['family']and i==1:route+=' '+row['family']
        lines+=['- '+n+' ( PIN '+n+'_A ) ( PIN '+n+'_B ) + USE SIGNAL'+(' + NONDEFAULTRULE ACTUAL_PG'if row['pg']else''),route+' ;']
    return '\n'.join(lines+['END NETS','END DESIGN'])+'\n'


class Capture(R.Census):
    def __init__(self,*args):super().__init__(*args);self.by_net={}
    def emit(self,event):self.by_net.setdefault(event['net'],[]).append(event);super().emit(event)


def routes(text,tech):
    technology=R.tech(tech,1000);defs=R.generated_vias(text,technology);rules=R.nondefault_rules(text,technology,set(technology['vias'])|set(defs))
    acc=Capture(technology,defs,rules);regular=R.parse_nets(text,'NETS',acc);special=R.parse_nets(text,'SPECIALNETS',acc)
    need(not special,'SPECIALNETS is outside the diagnostic');return acc.by_net,defs,rules


def geometry(text,tech,defs):
    need(text.isascii()and '\r'not in text,'Complete ASCII LF geometry required')
    OLD.section(text,'COMPONENTS',0)
    reference=fixture(defs);actual=routes(text,tech);expected=routes(reference,tech)
    need(actual==expected,'Complete routed primitive/extension/via/cut/NDR geometry differs')
    _,pins=OLD.section(text,'PINS',90);need(set(pins)=={p['name']for row in cases(defs)for p in ports(row)},'Complete global contact membership differs')
    pattern=(r'\s*\+\s+NET\s+(\S+)\s+\+\s+DIRECTION\s+(INPUT|OUTPUT)\s+\+\s+USE\s+SIGNAL\s+'
        r'\+\s+PORT\s+\+\s+LAYER\s+(\S+)\s+\(\s*(-?\d+)\s+(-?\d+)\s*\)\s*\(\s*(-?\d+)\s+(-?\d+)\s*\)\s+'
        r'\+\s+FIXED\s+\(\s*(-?\d+)\s+(-?\d+)\s*\)\s+N\s*')
    for row in cases(defs):
        for p in ports(row):
            m=re.fullmatch(pattern,pins[p['name']]);need(m is not None,'Unknown contact syntax/transform')
            net,direction,layer=m.group(1,2,3);a,b,c,d,x,y=map(int,m.group(4,5,6,7,8,9))
            need((net,direction,layer)==(p['net'],p['direction'],p['layer'])and[a+x,b+y,c+x,d+y]==p['global_box'],'Full end-face global contact differs')
    def outside(value):
        for section in ('VIAS','NONDEFAULTRULES','PINS','NETS','COMPONENTS'):
            need(len(re.findall(r'^'+section+r'\s+\d+\s*;',value,re.M))==1,'Missing/duplicate complete section')
            value=re.sub(r'^'+section+r'\s+\d+\s*;.*?^END '+section+r'\s*$', '',value,flags=re.M|re.S)
        return list(R.lex(value))
    need(outside(text)==outside(reference),'Unparsed/changed header, die or physical section')
    return dict(nets=45,ports=90,components=0,wire_controls=24,via_chains=21,generated_definitions=3,
        complete_geometry_checked=True,all_route_extensions_zero=True,post_via_explicit_zero_point_required=True)
