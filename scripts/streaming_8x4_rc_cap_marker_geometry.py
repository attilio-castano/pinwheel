"""Exact single-case/six-net marker C geometry; no field solve or Native."""
from decimal import Decimal as D
import re
import streaming_8x4_rc_consumer_cap as C

need=C.need
METALS=['Metal1','Metal2','Metal3','Metal4','TopMetal1']
WIDTHS=dict(zip(METALS,[160,200,200,200,1640]))
HEIGHTS=dict(zip(METALS,[['1.04','1.46'],['2.00','2.49'],['3.03','3.52'],['4.06','4.55'],['5.40','7.40']]))
JOBS=['retained','marker']
CASES=[dict(name='TYP-Metal1-Metal2-centered',prefix='Metal1_Metal2_pair',reference_case_id='TYP-Metal1-Metal2-centered',layers=['Metal1','Metal2'])]

def physical_cases(reference32,reference25):
    result=[]
    for case in CASES:
        source=reference25 if case['layers']==['Metal1'] else reference32
        selected=[r for r in source['cases'] if r['name']==case['reference_case_id']]
        need(len(selected)==1,'Exact marker C physical case membership differs')
        row=selected[0];expected=[]
        for index,metal in enumerate(case['layers']):
            half=D(WIDTHS[metal])/2000
            expected.append(dict(name='W'+str(index+1),bounds_um=[str(-half),str(half),*HEIGHTS[metal]]))
        need([r['name'] for r in row['rectangles']]==[r['name'] for r in expected]
            and [[D(x) for x in r['bounds_um']] for r in row['rectangles']]==[[D(x) for x in r['bounds_um']] for r in expected],
            'Supplementary C exact default width/center/vertical cross-section differs')
        if result:need(row['epsilon_layers']==result[0]['epsilon_layers'],'Full TYP reference material stack differs')
        result.append(dict(name=case['name'],reference_case_id=case['reference_case_id'],layers=case['layers'],
            rectangles=row['rectangles'],epsilon_layers=row['epsilon_layers']))
    need(len(result)==1,'Complete marker C physical universe required')
    return result


def definition(job):
    need(job in JOBS,'Undeclared marker C job')
    separation=512;padding=32;rows=[];partners={}
    for ci,case in enumerate(CASES):
        for li,length in enumerate((50,100,150)):
            center=(padding+(ci*3+li)*separation)*1000;nets=[]
            for wi,layer in enumerate(case['layers']):
                net=case['prefix']+'_L'+str(length)+'_W'+str(wi+1);nets.append(net)
                rows.append(dict(net=net,case=case['name'],layer=layer,conductor='W'+str(wi+1),width_DBU=WIDTHS[layer],
                    length_um=length,start_DBU=[padding*1000,center],end_DBU=[(padding+length)*1000,center]))
            for net in nets:partners[net]=None if len(nets)==1 else next(n for n in nets if n!=net)
    need(len(rows)==6 and len(partners)==6,'Complete39-net universe required')
    return dict(job=job,separation_um=separation,padding_um=padding,rows=rows,partners=partners,
        diearea_DBU=[0,0,(150+2*padding)*1000,(2*separation+2*padding)*1000])


def fixture(job):
    pins=[];nets=[]
    for row in job['rows']:
        net=row['net'];layer=row['layer'];half=row['width_DBU']//2
        for suffix,point,direction in (('A',row['start_DBU'],'INPUT'),('B',row['end_DBU'],'OUTPUT')):
            pins.append(f'- {net}_{suffix} + NET {net} + DIRECTION {direction} + USE SIGNAL\n'
                f' + PORT + LAYER {layer} ( -{half} -{half} ) ( {half} {half} ) + FIXED ( {point[0]} {point[1]} ) N ;')
        a,b=row['start_DBU'],row['end_DBU']
        nets.append(f'- {net} ( PIN {net}_A ) ( PIN {net}_B )\n'
            f' + ROUTED {layer} ( {a[0]} {a[1]} ) ( {b[0]} {b[1]} ) ;')
    _,_,xmax,ymax=job['diearea_DBU']
    return ('VERSION 5.8 ;\nDIVIDERCHAR "/" ;\nBUSBITCHARS "[]" ;\nDESIGN rc_cap_marker ;\n'
        'UNITS DISTANCE MICRONS 1000 ;\n'+f'DIEAREA ( 0 0 ) ( {xmax} {ymax} ) ;\n'
        'COMPONENTS 0 ;\nEND COMPONENTS\nPINS 12 ;\n'+'\n'.join(pins)+'\nEND PINS\nNETS 6 ;\n'
        +'\n'.join(nets)+'\nEND NETS\nEND DESIGN\n')


def validate(text,job):
    need(type(text) is str and text.isascii() and '\r' not in text,'Only ASCII LF marker DEF supported')
    remainder=text
    sections={}
    for section,count in [('PINS',12),('NETS',6)]:
        blocks=list(re.finditer(r'^\s*'+section+r'\s+(\d+)\s*;(.*?)^\s*END '+section+r'\s*$',remainder,re.M|re.S))
        need(len(blocks)==1 and int(blocks[0][1])==count,'Exact marker section census differs')
        m=blocks[0];sections[section]=m[2];remainder=remainder[:m.start()]+remainder[m.end():]
    area='DIEAREA ( 0 0 ) ( '+str(job['diearea_DBU'][2])+' '+str(job['diearea_DBU'][3])+' ) ;'
    target='VERSION 5.8 ; DIVIDERCHAR "/" ; BUSBITCHARS "[]" ; DESIGN rc_cap_marker ; UNITS DISTANCE MICRONS 1000 ; '+area+' COMPONENTS 0 ; END COMPONENTS END DESIGN'
    need(remainder.split()==target.split(),'Supplementary outline/units/cell/NDR/extra-section authority differs')
    wanted={r['net']:r for r in job['rows']};actual={};cursor=0
    pattern=re.compile(r'\s*- (\w+)\s+(.*?)\s*;',re.S)
    for match in pattern.finditer(sections['NETS']):
        need(not sections['NETS'][cursor:match.start()].strip(),'Unsupported marker net syntax');cursor=match.end()
        name,body=match.groups();need(name in wanted and name not in actual,'Duplicate/foreign marker net')
        row=wanted[name];ports=re.findall(r'\(\s*PIN\s+(\w+)\s*\)',body)
        need(len(ports)==2 and set(ports)=={name+'_A',name+'_B'},'Actual marker net-port binding differs')
        paths=re.split(r'\+\s+ROUTED\s+',body);need(len(paths)==2,'Exactly one marker route required')
        prefix=re.sub(r'\(\s*PIN\s+\w+\s*\)','',paths[0])
        need(len(re.findall(r'\+\s+USE\b',prefix))<=1,'Duplicate marker net USE')
        prefix=re.sub(r'\+\s+USE\s+SIGNAL\b','',prefix);need(not prefix.strip(),'NDR/unknown marker net attributes')
        route=re.fullmatch(r'(\w+)\s+((?:\(\s*(?:-?\d+|\*)\s+(?:-?\d+|\*)\s*\)\s*){2})',paths[1].strip())
        need(route is not None and route[1]==row['layer'],'Actual marker route layer/via/count differs')
        points=[]
        for point in re.findall(r'\(\s*(-?\d+|\*)\s+(-?\d+|\*)\s*\)',route[2]):
            need(points or '*' not in point,'Unbound marker route wildcard')
            points.append([points[-1][i] if v=='*' else int(v) for i,v in enumerate(point)])
        need(points==[row['start_DBU'],row['end_DBU']] and WIDTHS[route[1]]==row['width_DBU'],
            'Actual marker endpoints/default effective width differs')
        actual[name]=dict(layer=route[1],points_DBU=points,width_DBU=WIDTHS[route[1]])
    need(len(actual)==6 and not sections['NETS'][cursor:].strip(),'Incomplete marker route census')
    ports={};cursor=0
    pattern=re.compile(r'\s*- (\w+) \+ NET (\w+) \+ DIRECTION (INPUT|OUTPUT) \+ USE SIGNAL\s+\+ PORT\s+\+ LAYER (\w+)\s+\(\s*(-?\d+)\s+(-?\d+)\s*\)\s+\(\s*(-?\d+)\s+(-?\d+)\s*\)\s+\+ FIXED\s+\(\s*(-?\d+)\s+(-?\d+)\s*\) N\s*;')
    for match in pattern.finditer(sections['PINS']):
        need(not sections['PINS'][cursor:match.start()].strip(),'Unsupported marker port syntax');cursor=match.end()
        name,net,direction,layer,*coordinates=match.groups();need(net in wanted and name not in ports,'Duplicate/foreign marker port')
        row=wanted[net];end='start_DBU' if name==net+'_A' else 'end_DBU' if name==net+'_B' else None;half=row['width_DBU']//2
        need(end and layer==row['layer'] and direction==('INPUT' if end=='start_DBU' else 'OUTPUT')
            and list(map(int,coordinates))==[-half,-half,half,half,*row[end]],'Actual marker pin layer/shape/placement differs')
        ports[name]=dict(net=net,layer=layer,point_DBU=row[end])
    need(len(ports)==12 and not sections['PINS'][cursor:].strip(),'Incomplete marker port census')
    return dict(routes=actual,ports=ports,actual6nets12ports=True,zero_cells_ITerms_vias=True,no_NDR=True)
