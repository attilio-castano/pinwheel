"""Strict HOST routing-only DEF/tech-LEF census; never an RC envelope.

Every token in NETS/SPECIALNETS/VIAS/NONDEFAULTRULES is consumed. Geometry
outside those sections is explicitly outside this coarse routing census.
"""
from collections import Counter,defaultdict
from decimal import Decimal as D
import hashlib
import json
import re
from typing import NamedTuple

MAX_BYTES=128*1024*1024
NUMBER=r'[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?'
ORIENT={'N','S','E','W','FN','FS','FE','FW'}
SHAPES={'RING','STRIPE','FOLLOWPIN','IOWIRE','COREWIRE','BLOCKWIRE','FILLWIRE','PADRING','BLOCKRING','DRCFILL','BLOCKAGE'}
PATTERN=re.compile(r'\s+|\#[^\n]*|"(?:\\.|[^"\\])*"|[()+;]|(?:\\[\s\S]|[^\s()+;\#\\"])+')


def need(value,message):
    if not value:raise ValueError(message)


def canonical(value):return json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode()
def digest(value):return hashlib.sha256(canonical(value)).hexdigest()


class Token(NamedTuple):
    value:str
    kind:str


def lex(text):
    offset=0
    for match in PATTERN.finditer(text):
        need(match.start()==offset,'Unparsed DEF lexical byte near '+repr(text[offset:offset+30]));offset=match.end();raw=match[0]
        if raw.isspace() or raw.startswith('#'):continue
        kind='symbol' if raw in '()+;-' else 'string' if raw.startswith('"') else 'atom'
        if kind=='atom':
            need('\\\n' not in raw and '\\\r' not in raw,'Escaped newline in DEF identifier unsupported')
            raw=re.sub(r'\\(.)',r'\1',raw)
        yield Token(raw,kind)
    need(offset==len(text),'Unparsed final DEF lexical bytes')


class Cursor:
    def __init__(self,tokens):self.tokens=tokens;self.i=0
    def done(self):return self.i==len(self.tokens)
    def peek(self,n=0):return self.tokens[self.i+n].value if self.i+n<len(self.tokens) else None
    def is_(self,value,n=0):
        if self.i+n>=len(self.tokens):return False
        token=self.tokens[self.i+n];return token.value==value and token.kind==('symbol' if value in ('+','(',')',';','-') else 'atom')
    def pop(self):
        need(not self.done(),'Truncated routing syntax');t=self.tokens[self.i];self.i+=1;return t.value
    def expect(self,value):need(self.is_(value),'Expected '+value+' near '+str(self.peek()));self.i+=1
    def atom(self):
        need(not self.done() and self.tokens[self.i].kind=='atom','Expected routing identifier');return self.pop()
    def integer(self,minimum=None):
        text=self.atom();need(re.fullmatch(r'[+-]?\d+',text) is not None,'Expected integral DEF distance/count')
        value=int(text);need(abs(value)<2**53 and (minimum is None or value>=minimum),'Unbounded/negative DEF distance/count');return value
    def number(self):
        text=self.atom();need(re.fullmatch(NUMBER,text) is not None,'Expected numeric routing metadata');value=D(text);need(value.is_finite(),'Nonfinite routing metadata');return str(value)


def section(text,name):
    flags=re.M|re.I;tail=r'[ \t]*(?:\#[^\r\n]*)?$'
    starts=list(re.finditer(r'^[ \t]*'+name+r'[ \t]+(\d+)[ \t]*;'+tail,text,flags))
    ends=list(re.finditer(r'^[ \t]*END[ \t]+'+name+tail,text,flags))
    candidates=list(re.finditer(r'^[ \t]*'+name+r'(?:[ \t;]|$)',text,flags))
    end_candidates=list(re.finditer(r'^[ \t]*END[ \t]+'+name+r'(?:[ \t;]|$)',text,flags))
    need(len(candidates)==len(starts) and len(end_candidates)==len(ends),'Unparsed DEF section header: '+name)
    need(len(starts)==len(ends) and len(starts)<=1,'Duplicate/missing DEF section boundary: '+name)
    if not starts:return 0,''
    need(starts[0].end()<=ends[0].start(),'Reversed DEF section: '+name)
    return int(starts[0][1]),text[starts[0].end():ends[0].start()]


def entries(text,name):
    count,body=section(text,name);row=[];actual=0
    for token in lex(body):
        if token.kind=='symbol' and token.value==';':
            need(row and row[0]==Token('-','symbol') and len(row)>=2,'Unparsed '+name+' record prefix')
            actual+=1;yield Cursor(row[1:]);row=[]
        else:row.append(token)
    need(not row and actual==count,'Incomplete/declared '+name+' record count differs')


def units(text):
    need(type(text) is str and text.isascii() and '\x00' not in text and len(text.encode())<=MAX_BYTES,'Unsupported/oversized DEF bytes')
    found=re.findall(r'^[ \t]*UNITS[ \t]+DISTANCE[ \t]+MICRONS[ \t]+(\d+)[ \t]*;[ \t]*(?:\#[^\r\n]*)?$',text,re.M|re.I)
    candidates=re.findall(r'^[ \t]*UNITS(?:[ \t;]|$)',text,re.M|re.I)
    need(len(found)==len(candidates)==1 and 1<=int(found[0])<=1000000,'Missing/unsupported exact DEF units');return int(found[0])


def design_name(text):
    """A unique lexical DESIGN header, never a comment/property substring."""
    rows=re.findall(r'^[ \t]*DESIGN[ \t]+(.+?)[ \t]*;[ \t]*(?:\#[^\r\n]*)?$',text,re.M|re.I)
    candidates=re.findall(r'^[ \t]*DESIGN(?:[ \t;]|$)',text,re.M|re.I)
    need(len(rows)==len(candidates)==1,'Missing/duplicate exact DEF DESIGN header')
    c=Cursor(list(lex(rows[0])));name=c.atom();need(c.done(),'Unparsed DEF DESIGN header')
    end_rows=re.findall(r'^[ \t]*END[ \t]+DESIGN[ \t]*(?:\#[^\r\n]*)?$',text,re.M|re.I)
    end_candidates=re.findall(r'^[ \t]*END[ \t]+DESIGN(?:[ \t;]|$)',text,re.M|re.I)
    need(len(end_rows)==len(end_candidates)==1,'Missing/duplicate END DESIGN')
    return name


def scaled(value,dbu):
    result=D(value)*dbu;need(result.is_finite() and result==result.to_integral_value(),'Tech geometry not integral in actual DEF units');return int(result)


def lef_blocks(text,kind):
    pattern=r'^'+kind+r'\s+(\S+)([^\n]*)\n(.*?)^\s*END\s+\1\s*$'
    return [(m[1],m[2].strip(),m[3]) for m in re.finditer(pattern,text,re.M|re.S|re.I)]


def tech(text,dbu):
    need(type(text) is str and text.isascii() and '\x00' not in text and len(text.encode())<=16*1024*1024,'Unsupported/oversized technology LEF')
    clean='\n'.join(line.split('#',1)[0] for line in text.splitlines());layers={};routing=[]
    for name,_,body in lef_blocks(clean,'LAYER'):
        types=re.findall(r'\bTYPE\s+(\w+)\s*;',body,re.I);need(len(types)==1 and name not in layers,'Duplicate/ambiguous tech layer')
        row=dict(type=types[0].upper())
        if row['type']=='ROUTING':
            widths=re.findall(r'^\s*WIDTH\s+('+NUMBER+r')\s*;\s*$',body,re.M|re.I);directions=re.findall(r'\bDIRECTION\s+(\w+)\s*;',body,re.I)
            need(len(widths)==len(directions)==1,'Missing unique tech routing width/direction')
            for field in ('HEIGHT','THICKNESS'):
                values=re.findall(r'^\s*'+field+r'\s+('+NUMBER+r')\s*;\s*$',body,re.M|re.I)
                need(len(values)<=1,'Duplicate tech layer physical metadata')
                row[field+'_um']=str(D(values[0])) if values else None
            row.update(width_dbu=scaled(widths[0],dbu),direction=directions[0].upper(),routing_level=len(routing)+1);need(row['width_dbu']>0,'Nonpositive tech routing width');routing.append(name)
        layers[name]=row
    need(routing and layers,'No complete tech routing layers');vias={};rules={}
    for kind,destination in [('VIA',vias),('VIARULE',rules)]:
        for name,header,body in lef_blocks(clean,kind):
            need(name not in destination,'Duplicate tech via/rule')
            need(header.upper() in (('','DEFAULT') if kind=='VIA' else ('GENERATE','GENERATE DEFAULT')),'Unsupported tech via/rule header')
            groups=list(re.finditer(r'\bLAYER\s+(\w+)\s*;(.*?)(?=\bLAYER\s+\w+\s*;|\Z)',body,re.S|re.I))
            cut=[];metals=[];rectangles={}
            prefix=body[:groups[0].start()] if groups else body
            prefix=re.sub(r'\bRESISTANCE\s+'+NUMBER+r'\s*;','',prefix,flags=re.I);need(not prefix.strip(),'Unparsed tech via/rule prefix')
            for group in groups:
                layer,material=group[1],group[2];need(layer in layers,'Unknown tech via/rule material layer')
                rect=[]
                for found in re.finditer(r'\bRECT\s+('+NUMBER+r')\s+('+NUMBER+r')\s+('+NUMBER+r')\s+('+NUMBER+r')\s*;',material,re.I):
                    box=list(map(lambda s:scaled(s,dbu),found.groups()));need(box[2]>box[0] and box[3]>box[1],'Nonpositive tech via rectangle');rect.append(box)
                need(not re.search(r'\bPOLYGON\b',material,re.I),'Polygonal tech via/rule unsupported')
                recognized=r'\bRECT\s+'+NUMBER+r'\s+'+NUMBER+r'\s+'+NUMBER+r'\s+'+NUMBER+r'\s*;'
                residual=re.sub(recognized,'',material,flags=re.I)
                if kind=='VIARULE':
                    for statement in (r'ENCLOSURE\s+'+NUMBER+r'\s+'+NUMBER, r'SPACING\s+'+NUMBER+r'\s+BY\s+'+NUMBER, r'RESISTANCE\s+'+NUMBER, r'WIDTH\s+'+NUMBER+r'\s+TO\s+'+NUMBER, r'DIRECTION\s+(?:HORIZONTAL|VERTICAL)'):
                        residual=re.sub(r'\b'+statement+r'\s*;','',residual,flags=re.I)
                need(not residual.strip(),'Unparsed tech via/rule physical geometry: '+name)
                rectangles.setdefault(layer,[]).extend(rect)
                if layers[layer]['type']=='CUT':cut.append(layer)
                elif layers[layer]['type']=='ROUTING':metals.append(layer)
                else:raise ValueError('Nonrouting tech via layer unsupported')
            need(len(set(cut))==1 and len(set(metals))==2,'Tech via/rule must identify two routing/one cut layer: '+name+' '+str((cut,metals)))
            metals=sorted(set(metals),key=lambda n:layers[n]['routing_level']);cut=list(set(cut));need(layers[metals[1]]['routing_level']==layers[metals[0]]['routing_level']+1,'Nonadjacent tech via/rule stack unsupported')
            need(rectangles[cut[0]],'Missing exact tech via cuts')
            if kind=='VIA':need(all(rectangles[m] for m in metals),'Missing tech via metal rectangles')
            destination[name]=dict(kind='technology_via' if kind=='VIA' else 'technology_generate_rule',layers=[metals[0],cut[0],metals[1]],
                cut_count=len(rectangles[cut[0]]),rectangles_dbu=rectangles,source_header=header)
    return dict(layers=layers,routing_layers=routing,vias=vias,via_rules=rules,dbu_per_um=dbu,
        scope='routing widths and explicit via/cut definitions; not full LEF/DRC or physical R/C qualification')


def rect(c,count=4):
    c.expect('(');values=[c.integer() for _ in range(count)];c.expect(')');return values


def generated_vias(text,technology):
    result={}
    for c in entries(text,'VIAS'):
        name=c.atom();need(name not in result and name not in technology['vias'],'Duplicate/aliased DEF via name');fields={};rects=[]
        while not c.done():
            c.expect('+');key=c.atom();need(key not in fields or key=='RECT','Duplicate DEF via field')
            if key in ('VIARULE','PATTERNNAME'):fields[key]=c.atom()
            elif key in ('CUTSIZE','CUTSPACING','ORIGIN'):fields[key]=[c.integer() for _ in range(2)]
            elif key in ('ENCLOSURE','OFFSET'):fields[key]=[c.integer() for _ in range(4)]
            elif key=='ROWCOL':fields[key]=[c.integer(1),c.integer(1)]
            elif key=='LAYERS':fields[key]=[c.atom() for _ in range(3)]
            elif key=='RECT':
                layer=c.atom();a,b=rect(c,2),rect(c,2);need(layer in technology['layers'] and b[0]>a[0] and b[1]>a[1],'Unknown/nonpositive explicit DEF via rectangle');rects.append(dict(layer=layer,box=a+b))
            else:raise ValueError('Unparsed DEF via physical field: '+key)
        if 'VIARULE' in fields:
            need(not rects and {'VIARULE','CUTSIZE','CUTSPACING','ENCLOSURE','LAYERS'}<=set(fields),'Incomplete generated DEF via rule geometry')
            rule=technology['via_rules'].get(fields['VIARULE']);need(rule and fields['LAYERS']==rule['layers'],'Generated via/rule layer stack differs')
            need(all(v>0 for v in fields['CUTSIZE']) and all(v>=0 for v in fields['CUTSPACING']+fields['ENCLOSURE']),'Invalid generated via size/spacing/enclosure')
            rows,cols=fields.get('ROWCOL',[1,1]);need(rows*cols<=1000000,'Unbounded generated via cut array')
            cut=rule['rectangles_dbu'][rule['layers'][1]];need(len(cut)==1 and fields['CUTSIZE']==[cut[0][2]-cut[0][0],cut[0][3]-cut[0][1]],'Generated via cut size differs from selected rule')
            result[name]=dict(kind='generated_DEF_via',layers=fields['LAYERS'],cut_count=rows*cols,parameters=fields,
                cut_positions_not_expanded=True,metal_enclosure_spacing_accuracy_not_qualified=True)
        else:
            need(rects and set(fields)<={'PATTERNNAME'},'Explicit DEF via has unsupported/generated fields');cuts={r['layer'] for r in rects if technology['layers'][r['layer']]['type']=='CUT'};metals={r['layer'] for r in rects if technology['layers'][r['layer']]['type']=='ROUTING'}
            need(len(cuts)==1 and len(metals)==2 and len(cuts|metals)==len({r['layer'] for r in rects}),'Unsupported explicit DEF via stack');metals=sorted(metals,key=lambda m:technology['layers'][m]['routing_level'])
            need(technology['layers'][metals[1]]['routing_level']==technology['layers'][metals[0]]['routing_level']+1,'Nonadjacent explicit DEF via unsupported')
            result[name]=dict(kind='explicit_DEF_via',layers=[metals[0],next(iter(cuts)),metals[1]],cut_count=sum(r['layer'] in cuts for r in rects),rectangles_dbu=rects,parameters=fields)
    return result


def nondefault_rules(text,technology,via_names):
    result={}
    for c in entries(text,'NONDEFAULTRULES'):
        name=c.atom();need(name not in result,'Duplicate DEF NDR');layers={};other=[]
        while not c.done():
            c.expect('+');key=c.atom()
            if key=='LAYER':
                layer=c.atom();need(layer in technology['routing_layers'] and layer not in layers,'Unknown/duplicate NDR layer');fields={}
                while not c.done() and not c.is_('+'):
                    field=c.atom();need(field in ('WIDTH','SPACING','WIREEXTENSION','DIAGWIDTH') and field not in fields,'Unparsed/duplicate physical NDR field');fields[field]=c.integer(0)
                need(fields.get('WIDTH',0)>0,'Missing positive NDR width');layers[layer]=fields
            elif key=='HARDSPACING':other.append([key])
            elif key=='VIA':
                via=c.atom();need(via in via_names,'Unresolved NDR via');other.append([key,via])
            elif key=='VIARULE':
                rule=c.atom();need(rule in technology['via_rules'],'Unresolved NDR via rule');other.append([key,rule])
            elif key=='MINCUTS':
                layer=c.atom();need(technology['layers'].get(layer,{}).get('type')=='CUT','Unresolved NDR cut layer');other.append([key,layer,c.integer(1)])
            else:raise ValueError('Unparsed NDR physical syntax: '+key)
        need(layers,'NDR has no resolved layer widths');result[name]=dict(layers=layers,other=other)
    return result


class Census:
    def __init__(self,technology,definitions,rules):
        self.tech=technology;self.vias=dict(technology['vias'],**definitions);self.rules=rules
        self.hash=hashlib.sha256();self.events=0;self.layers={};self.used_vias={};self.sections={};self.used_ndr=set();self.via_layer_incidence=defaultdict(Counter);self.cut_layer_incidence=defaultdict(Counter)
    def emit(self,event):
        self.hash.update(canonical(event)+b'\n');self.events+=1;need(self.events<=5000000,'Unbounded routed primitive count')
        layer=event.get('layer');kind=event['kind'];scope=event['scope']
        if kind in ('segment','relative_RECT','absolute_RECT'):
            need(layer in self.tech['routing_layers'],'Unresolved routed material layer')
            row=self.layers.setdefault(layer,dict(segment_count=0,centerline_length_dbu=0,widths_dbu=Counter(),widths_by_scope={},rect_patch_count=0,rect_dimensions_dbu=Counter(),scope_counts=Counter(),mask_counts=Counter()))
            row['scope_counts'][scope]+=1
            if kind=='segment':
                row['segment_count']+=1;row['centerline_length_dbu']+=event['length_dbu'];row['widths_dbu'][str(event['width_dbu'])]+=1;row['widths_by_scope'].setdefault(scope,Counter())[str(event['width_dbu'])]+=1
            else:
                box=event['box'];row['rect_patch_count']+=1;row['rect_dimensions_dbu'][str(box[2]-box[0])+'x'+str(box[3]-box[1])]+=1
            if event.get('mask') is not None:row['mask_counts'][str(event['mask'])]+=1
        elif kind=='via':
            name=event['name'];definition=self.vias[name];row=self.used_vias.setdefault(name,dict(placements=0,cut_occurrences=0,scope_counts=Counter(),orientations=Counter(),mask_counts=Counter(),definition=definition))
            row['placements']+=1;row['cut_occurrences']+=definition['cut_count'];
            self.via_layer_incidence[definition['layers'][0]][scope]+=1;self.via_layer_incidence[definition['layers'][2]][scope]+=1
            self.cut_layer_incidence[definition['layers'][1]][scope]+=definition['cut_count']
            row['scope_counts'][scope]+=1;row['orientations'][event['orientation']]+=1
            if event.get('mask') is not None:row['mask_counts'][str(event['mask'])]+=1
    def width(self,layer,ndr):
        need(layer in self.tech['routing_layers'],'Unresolved routing layer: '+layer)
        if ndr is None:return self.tech['layers'][layer]['width_dbu'],'technology_default'
        need(ndr in self.rules and layer in self.rules[ndr]['layers'],'Unresolved/incomplete used NDR layer width');self.used_ndr.add(ndr)
        return self.rules[ndr]['layers'][layer]['WIDTH'],'NDR:'+ndr


def route(c,acc,scope,net,net_ndr,wire_type):
    shield=c.atom() if wire_type=='SHIELD' else None;paths=0;shapes=0
    while True:
        layer=c.atom();need(layer in acc.tech['routing_layers'],'Unresolved path layer');special=scope=='SPECIALNETS'
        width=c.integer(0) if special else None;effective=net_ndr
        if not special and c.is_('TAPER'):c.pop();effective=None
        elif not special and c.is_('TAPERRULE'):c.pop();effective=c.atom()
        if not special:width,width_source=acc.width(layer,effective)
        else:width_source='explicit_special_width'
        shape=None
        if c.is_('+') and c.is_('SHAPE',1):
            need(special,'SHAPE field on regular routing unsupported');c.pop();c.pop();shape=c.atom();need(shape in SHAPES,'Unresolved special shape class')
        paths+=1;point=None;extension=None;mask=None;items=0
        acc.emit(dict(kind='path',scope=scope,net=net,layer=layer,width_dbu=width,width_source=width_source,wire_type=wire_type,shield=shield,shape=shape))
        while not c.done() and not c.is_('+') and not c.is_('NEW'):
            if c.is_('MASK'):
                c.pop();mask=c.integer(0);need(mask<=999,'Unbounded route/via mask');continue
            if c.is_('('):
                c.pop();fields=[]
                while not c.is_(')'):fields.append(c.atom());need(len(fields)<=3,'Unsupported routed point shape')
                c.pop();need(len(fields) in (2,3) and (not special or len(fields)==2),'Unsupported special point extension/coordinate')
                xy=[]
                for axis,token in enumerate(fields[:2]):
                    if token=='*':need(point is not None,'Unbound first routed coordinate wildcard');xy.append(point[axis])
                    else:need(re.fullmatch(r'[+-]?\d+',token) is not None,'Nonintegral routed coordinate');xy.append(int(token))
                need(all(abs(v)<2**53 for v in xy),'Unbounded routed point')
                ext=None
                if len(fields)==3:
                    need(re.fullmatch(r'\d+',fields[2]) is not None,'Negative/nonintegral route extension');ext=int(fields[2]);need(ext<2**53,'Unbounded route extension')
                if point is not None and point!=xy:
                    need(point[0]==xy[0] or point[1]==xy[1],'Nonorthogonal route requires a separately admitted geometry parser')
                    need(width>0,'Positive-length special wire has zero width')
                    acc.emit(dict(kind='segment',scope=scope,net=net,layer=layer,width_dbu=width,width_source=width_source,
                        start=point,end=xy,length_dbu=abs(point[0]-xy[0])+abs(point[1]-xy[1]),start_extension_dbu=extension,end_extension_dbu=ext,mask=mask,wire_type=wire_type,shape=shape))
                    shapes+=1
                acc.emit(dict(kind='point',scope=scope,net=net,layer=layer,xy=xy,explicit_extension_dbu=ext,mask=mask));point=xy;extension=ext;mask=None;items+=1;continue
            if c.is_('RECT'):
                c.pop();need(not special and point is not None,'Relative RECT lacks regular path point');rect_mask=None
                if c.is_('MASK'):c.pop();rect_mask=c.integer(0)
                box=rect(c);box=[box[i]+point[i%2] for i in range(4)];need(box[2]>box[0] and box[3]>box[1],'Nonpositive relative route RECT')
                acc.emit(dict(kind='relative_RECT',scope=scope,net=net,layer=layer,box=box,mask=rect_mask));shapes+=1;items+=1;continue
            name=c.atom();need(name in acc.vias,'Unparsed route token or unresolved via: '+name);need(point is not None,'Routed via has no placement coordinate')
            definition=acc.vias[name];bottom,_,top=definition['layers'];need(layer in (bottom,top),'Via does not touch active routing layer')
            orientation=c.pop() if c.peek() in ORIENT else 'N';other=top if layer==bottom else bottom
            acc.emit(dict(kind='via',scope=scope,net=net,name=name,xy=point,orientation=orientation,mask=mask,from_layer=layer,to_layer=other))
            layer=other
            if not special:width,width_source=acc.width(layer,effective)
            mask=None;items+=1;shapes+=1
        need(items>0 and mask is None,'Empty route path/dangling mask')
        if c.is_('NEW'):c.pop();continue
        break
    return paths,shapes


def parse_nets(text,name,acc):
    names=set();net_hash=hashlib.sha256();counts=Counter();unrouted=[]
    for c in entries(text,name):
        net=c.atom();need(net not in names,'Duplicate decoded DEF net name');names.add(net);endpoints=[]
        while c.is_('('):
            c.pop();instance,pin=c.atom(),c.atom();extra=[]
            if c.is_('+'):c.pop();c.expect('SYNTHESIZED');extra=['SYNTHESIZED']
            c.expect(')');endpoints.append([instance,pin,*extra])
        need(len({tuple(v) for v in endpoints})==len(endpoints),'Duplicate exact endpoint in routed net')
        attrs={};ndr=None;paths=0;shapes=0
        while not c.done():
            c.expect('+');key=c.atom()
            if key in ('ROUTED','FIXED','COVER','SHIELD'):
                p,s=route(c,acc,name,net,ndr,key);paths+=p;shapes+=s;continue
            if key=='RECT':
                need(name=='SPECIALNETS','Absolute RECT only admitted for special net');layer=c.atom();mask=None
                if c.is_('MASK'):c.pop();mask=c.integer(0)
                a,b=rect(c,2),rect(c,2);need(b[0]>a[0] and b[1]>a[1],'Nonpositive special absolute RECT')
                acc.emit(dict(kind='absolute_RECT',scope=name,net=net,layer=layer,box=a+b,mask=mask));shapes+=1;continue
            need(key not in attrs or key=='PROPERTY','Duplicate nonroute net attribute')
            if key=='NONDEFAULTRULE':
                need(paths==0,'Late net NDR after routing is ambiguous');ndr=c.atom();need(ndr in acc.rules,'Unresolved net NDR');attrs[key]=ndr
            elif key in ('USE','SOURCE','ORIGINAL','PATTERN'):attrs[key]=c.atom()
            elif key=='WEIGHT':attrs[key]=c.integer(0)
            elif key in ('ESTCAP','FREQUENCY','XTALK'):attrs[key]=c.number()
            elif key=='FIXEDBUMP':attrs[key]=True
            elif key=='PROPERTY':
                values=[]
                while not c.done() and not c.is_('+'):values.append(c.pop())
                need(values and len(values)%2==0,'Malformed net property pairs');attrs.setdefault(key,[]).extend(values)
            else:raise ValueError('Unparsed '+name+' physical/attribute syntax: '+key)
        use=attrs.get('USE','UNSPECIFIED');need(use in ('UNSPECIFIED','SIGNAL','CLOCK','POWER','GROUND','ANALOG','RESET','SCAN','TIEOFF'),'Unresolved net use class')
        counts['nets']+=1;counts['endpoints']+=len(endpoints);counts['paths']+=paths;counts['physical_shapes']+=shapes;counts['use:'+use]+=1
        if not shapes:
            counts['nets_without_route_material']+=1
            if len(endpoints)>1:unrouted.append(net)
        net_hash.update(canonical(dict(name=net,endpoints=endpoints,attributes=attrs,paths=paths,physical_shapes=shapes))+b'\n')
    acc.sections[name]=dict(counts=dict(counts),complete_net_endpoint_attribute_sha256=net_hash.hexdigest(),
        multi_endpoint_nets_without_route_material=unrouted,net_names_sha256=digest(sorted(names)))
    return names


def parse(text,tech_text):
    dbu=units(text);technology=tech(tech_text,dbu);definitions=generated_vias(text,technology)
    for definition in definitions.values():need(definition['kind']!='generated_DEF_via' or 'PATTERNNAME' not in definition['parameters'],
        'Generated via PATTERNNAME cut occupancy is not admitted')
    for kind in ('FILLS','SLOTS'):
        count,body=section(text,kind);need(count==0 and not list(lex(body)),'Uncounted conducting '+kind+' requires separate parser coverage')
    rules=nondefault_rules(text,technology,set(technology['vias'])|set(definitions));acc=Census(technology,definitions,rules)
    regular=parse_nets(text,'NETS',acc);special=parse_nets(text,'SPECIALNETS',acc)
    need(regular or special,'No complete routed net sections')
    for layer,row in acc.layers.items():row['centerline_length_um']=str(D(row['centerline_length_dbu'])/dbu)
    return dict(schema='pinwheel.model24-route-material-census.v1',DEF_dbu_per_um=dbu,
        technology_routing_layers=technology['routing_layers'],routing_sections=acc.sections,
        layer_usage=acc.layers,via_metal_layer_incidence=dict(acc.via_layer_incidence),cut_layer_occurrences=dict(acc.cut_layer_incidence),
        used_routing_layers_including_via_metals=sorted(set(acc.layers)|set(acc.via_layer_incidence)),
        technology_layer_metadata=technology['layers'],via_usage=acc.used_vias,defined_DEF_vias=definitions,defined_NDRs=rules,
        used_NDRs=sorted(acc.used_ndr),net_names_shared_between_regular_and_special=sorted(regular&special),
        routing_primitive_events=acc.events,routing_primitive_sha256=acc.hash.hexdigest(),
        routed_geometry_syntax_complete=True,all_used_via_cut_counts_resolved=True,
        scope='complete parsed routed primitives and via/cut/width/length inventory only',
        centerline_lengths_exclude_RECT_patch_area_and_endpoint_extension_geometry=True,
        generated_cut_parameters_retained_without_expanding_positions=True,
        cell_internal_and_port_material_context_complete=False,spacing_context_coverage_complete=False,
        field_solver_reference_coverage_complete=False,physical_corner_applicability_complete=False,
        qualified_model_envelope=False,model_qualified=False,qualified_timing=False)
