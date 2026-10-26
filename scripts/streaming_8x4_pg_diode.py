"""Finite PG-aware diode placement planner and live Tcl bridge.

The Python helper never loads or writes an ODB. It consumes read-only live
snapshots and emits site/orientation moves; only the owning OpenROAD Tcl
process applies them. A placement/access certificate is not routing signoff.
"""
import argparse
from bisect import bisect_left
from collections import Counter, defaultdict
from copy import deepcopy
from decimal import Decimal
import hashlib
import heapq
import json
from pathlib import Path
import re
import signal
import sys
import time

SCHEMA = 'pinwheel.streaming-8x4-pg-diode.v1'
TOP = 'tt_um_pinwheel_streaming_ready_d2'
MASTER = 'sg13cmos5l_antennanp'
TECH_SHA = '3edd5a1ad31e8307be537d0d1b85c3258fefeb21aac04aaa476e4f72de4cffd5'
CORE = (2880, 3780, 1721280, 706860)
POLICIES = {'A': dict(radius_sites=16, adjacent_rows=0),
    'B': dict(search='all-legal-core-row-sites',metric='Manhattan-bbox-lower-left-DBU',
        order=['distance','absolute-row-displacement','row-y','site-x'],
        minimum_x=2880,maximum_x=1719840,site_pitch=480,rows=186)}
BLOCKED_RULE = dict(source_commit='dcf36133a369abc8f3c5e5738cd4d82e4903c0e0',
    source_manifest_sha256='a1006bd413d06facf149b583a0bad640769e92ec686f137ce72691d9a3f31350',
    special_nets_only=True,ignore_vias=True,ignore_wire_shape='DRCFILL',routing_levels=[2,3],
    ignore_horizontal_and_square=True,used_layer_includes_pin_layer_plus_one=True,
    whole_cell_row_site_raster=True,core_dbu=list(CORE),site_pitch_dbu=480,row_height_dbu=3780)


def need(ok, message):
    if not ok: raise ValueError(message)


def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, value):
    path = Path(path); need(not path.exists(), 'Preserve previous PG-diode artifact: ' + str(path))
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + '\n')


def dbu(value):
    value = Decimal(value) * 1000
    need(value.is_finite() and value == value.to_integral_value(), 'Nonintegral/nonfinite DBU')
    return int(value)


def bounds(value):
    need(len(value) == 4 and all(type(v) is int for v in value) and value[0] < value[2] and value[1] < value[3],
        'Invalid physical rectangle')
    return tuple(value)


def intersect(a, b): return max(a[0], b[0]) < min(a[2], b[2]) and max(a[1], b[1]) < min(a[3], b[3])
def contains(a, b): return a[0] <= b[0] and a[1] <= b[1] and b[2] <= a[2] and b[3] <= a[3]
def clearance(a, b): return max(a[0]-b[2], b[0]-a[2], a[1]-b[3], b[1]-a[3])
def translate(rect, x, y): return (rect[0]+x, rect[1]+y, rect[2]+x, rect[3]+y)


def transform(rect, x, y, orient, width=1440, height=3780):
    need(orient in ('R0', 'MX', 'MY', 'R180'), 'Unsupported diode orientation')
    l, d, r, u = rect
    if orient in ('MY', 'R180'): l, r = width-r, width-l
    if orient in ('MX', 'R180'): d, u = height-u, height-d
    return (x+l, y+d, x+r, y+u)


def read_snapshot(path):
    insts = {}; terms = {}; nets = {}; ports = {}; public = []; pg = []; blockages = []; top = []
    versions=[];special=[];special_nets=[];net_flags=0
    for line in Path(path).read_text().splitlines():
        row = line.split('\t'); kind = row[0]
        if kind == 'SNAPSHOT': need(row==['SNAPSHOT','2'],'Unsupported live snapshot version');versions.append(2)
        elif kind == 'TOP': need(len(row) == 2, 'Bad top'); top.append(row[1])
        elif kind == 'INST':
            need(len(row) == 9 and row[1] not in insts, 'Duplicate/bad instance')
            insts[row[1]] = dict(master=row[2], box=bounds(tuple(map(int,row[3:7]))),
                orient=row[7], status=row[8])
        elif kind == 'ITERM':
            need(len(row) == 6 and tuple(row[1:3]) not in terms, 'Duplicate/bad ITerm')
            terms[tuple(row[1:3])] = tuple(row[3:])
        elif kind == 'NET':
            need(len(row) in (5,6) and row[1] not in nets, 'Duplicate/bad net')
            nets[row[1]] = (row[2], int(row[3]), int(row[4]))
            if len(row)==6:
                need(row[5] in ('0','1'),'Bad special-net flag');net_flags+=1
                if row[5]=='1':special_nets.append(row[1])
        elif kind == 'BTERM':
            need(len(row) == 5 and row[1] not in ports, 'Duplicate/bad port'); ports[row[1]] = tuple(row[2:])
        elif kind == 'BPIN':
            need(len(row) == 8, 'Bad public shape'); public.append(tuple(row[1:]))
        elif kind == 'PG':
            need(len(row) == 8, 'Bad PG shape'); pg.append((row[1],row[2],bounds(tuple(map(int,row[3:7]))),row[7]))
        elif kind == 'SPECIAL':
            need(len(row)==8,'Bad special routing shape');special.append((row[1],row[2],bounds(tuple(map(int,row[3:7]))),row[7]))
        elif kind == 'BLOCKAGE':
            need(len(row) == 6, 'Bad placement blockage'); blockages.append((bounds(tuple(map(int,row[1:5]))), row[5]))
        else: raise ValueError('Unsupported snapshot record: ' + kind)
    need(top == [TOP] and insts and terms and nets and ports and pg,
        'Incomplete/wrong-top snapshot')
    ic = Counter(); bc = Counter()
    for (inst,pin), (direction,kind,net) in terms.items():
        need(inst in insts and pin and direction in ('INPUT','OUTPUT','INOUT'), 'Unresolved ITerm')
        if net: need(net in nets, 'Unknown connected net'); ic[net] += bool(net)
    for _, (_,kind,net) in ports.items(): need(net in nets, 'Unknown port net'); bc[net] += 1
    need(all((ic[n],bc[n]) == r[1:] for n,r in nets.items()), 'Incomplete net endpoint census')
    need({r[0] for r in pg} <= {n for n,r in nets.items() if r[0] in ('POWER','GROUND')}, 'PG owner/type mismatch')
    if versions:
        need(versions==[2] and net_flags==len(nets) and set(special_nets)<=set(nets),'Incomplete live special-net census')
        need(all(r[0] in special_nets for r in special),'Non-special obstruction owner')
        need(Counter(r[:3] for r in pg if r[3]=='0')==Counter(r[:3] for r in special if nets[r[0]][0] in ('POWER','GROUND')),
            'Incomplete same-layer PG special-shape census')
    else:
        need(not special and not net_flags,'Versionless partial special census')
    return dict(instances=insts, terminals=terms, nets=nets, ports=ports, public=sorted(public), pg=sorted(pg), blockages=sorted(blockages),
        special=sorted(special) if versions else None,special_nets=sorted(special_nets) if versions else None)


def legacy_host_specials(snapshot, def_text):
    """Explicit HOST-only supplement for the two closed pre-v2 PG snapshots.

    Every positive-width special segment must match the old full PG census.
    Native main never uses this adapter: its source-bound live capture is v2.
    """
    need(snapshot['special'] is None,'Not a legacy snapshot')
    section=re.search(r'^SPECIALNETS (\d+) ;\n(.*?)^END SPECIALNETS',def_text,re.M|re.S)
    need(section is not None,'Missing legacy special section');rows=[];names=[]
    for net in re.finditer(r'^\s*- (\S+)\s+(.*?);',section[2],re.M|re.S):
        name=net[1];names.append(name)
        need(name in snapshot['nets'] and snapshot['nets'][name][0] in ('POWER','GROUND'),'Legacy non-PG special net unsupported')
        for clause in re.finditer(r'(?:ROUTED|NEW) (\S+) (\d+) \+ SHAPE (\S+) \( (-?\d+) (-?\d+) \)([^\n]*)',net[2]):
            layer,width,kind,x,y,tail=clause.groups();width,x,y=int(width),int(x),int(y)
            if not width:continue
            endpoint=re.fullmatch(r' \( (-?\d+) (-?\d+) \)\s*',tail)
            need(endpoint is not None and width%2==0 and kind in ('STRIPE','FOLLOWPIN'),'Unsupported legacy special segment')
            x2,y2=map(int,endpoint.groups());need(x==x2 or y==y2,'Nonorthogonal legacy special shape')
            box=(x-width//2,min(y,y2),x+width//2,max(y,y2)) if x==x2 else (min(x,x2),y-width//2,max(x,x2),y+width//2)
            rows.append((name,layer,bounds(box),kind))
    need(len(names)==len(set(names))==int(section[1]) and
        Counter(r[:3] for r in rows)==Counter(r[:3] for r in snapshot['pg'] if r[3]=='0'),
        'Legacy DEF/snapshot full non-via special membership differs')
    result=deepcopy(snapshot);result.update(special=sorted(rows),special_nets=sorted(names));return result


def geometry(def_path):
    return geometry_text(Path(def_path).read_text())


def geometry_text(text):
    need(re.findall(r'^UNITS DISTANCE MICRONS (\d+)\s*;',text,re.M) == ['1000'], 'Wrong DEF units')
    need(re.findall(r'^DIEAREA \( (\d+) (\d+) \) \( (\d+) (\d+) \) ;$',text,re.M) == [('0','0','1724160','710640')], 'Wrong die')
    rows = re.findall(r'^ROW ROW_(\d+) CoreSite (\d+) (\d+) (N|FS) DO (\d+) BY 1 STEP (\d+) 0 ;$',text,re.M)
    need(len(rows) == 186 and all((int(n),int(x),int(y),o,int(c),int(p)) ==
        (i,2880,3780+i*3780,'N' if i%2 == 0 else 'FS',3580,480) for i,(n,x,y,o,c,p) in enumerate(rows)), 'Official rows differ')
    tracks = {}
    for axis,start,count,pitch,layer in re.findall(r'^TRACKS (X|Y) (\d+) DO (\d+) STEP (\d+) LAYER (\S+) ;$',text,re.M):
        need((layer,axis) not in tracks, 'Duplicate track grid'); tracks[layer,axis] = (int(start),int(count),int(pitch))
    need(('Metal2','X') in tracks and ('Metal1','Y') in tracks, 'Missing landing track grids')
    return dict(rows=[dict(y=int(r[2]),orient=r[3]) for r in rows], tracks=tracks)


def profile(tech_path, cell_path, request):
    need(sha(tech_path) == request['tech_sha256'] == TECH_SHA and sha(cell_path) == request['cell_sha256'], 'LEF input changed')
    return profile_text(Path(tech_path).read_text(),Path(cell_path).read_text())


def profile_text(tech, cells):
    macro = re.search(r'^MACRO '+MASTER+r'\n(.*?)^END '+MASTER,cells,re.M|re.S)
    need(macro is not None and re.search(r'SIZE 1\.44 BY 3\.78\s*;',macro[1]) and re.search(r'ORIGIN 0 0\s*;',macro[1]), 'Diode macro differs')
    pin = re.search(r'^  PIN A\n(.*?)^  END A',macro[1],re.M|re.S)
    need(pin is not None and re.findall(r'^\s*LAYER\s+(\S+)\s*;',pin[1],re.M) == ['Metal1'], 'Unsupported A pin')
    rects = [bounds(tuple(dbu(x) for x in row)) for row in re.findall(r'RECT\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s*;',pin[1])]
    need(len(rects) == 3, 'A geometry incomplete')
    via = re.search(r'^Via\s+Via1_YY\s+DEFAULT\s*\n(.*?)^\s*END Via1_YY\s*$',tech,re.M|re.S|re.I)
    need(via is not None, 'Pinned Via1_YY absent'); enclosures = {}
    for name in ('Metal1','Metal2'):
        segment = re.search(r'LAYER\s+'+name+r'\s*;\s*(.*?)(?=\s*LAYER|$)',via[1],re.I|re.S)
        rs = re.findall(r'RECT\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s*;',segment[1],re.I) if segment else []
        need(len(rs) == 1, 'Unsupported Via1 enclosure'); enclosures[name] = bounds(tuple(dbu(x) for x in rs[0]))
    spacing = {}
    for name in ('Metal1','Metal2'):
        layer = re.search(r'^LAYER '+name+r'\n(.*?)^END '+name,tech,re.M|re.S)
        need(layer is not None, 'Missing routing layer')
        table = re.search(r'SPACINGTABLE\s+PARALLELRUNLENGTH\s+(.*?);',layer[1],re.S)
        need(table is not None, 'Missing width/PRL spacing table')
        values = []
        for row in re.findall(r'WIDTH\s+(.*?)(?=\s*WIDTH|$)',table[1],re.S):
            nums = row.split(); need(len(nums) >= 2, 'Invalid spacing table'); values += [dbu(v) for v in nums[1:]]
        need(values, 'Vacuous spacing envelope'); spacing[name] = max(values)
    need(spacing['Metal2'] == 600, 'Pinned complete Metal2 spacing envelope differs')
    # Pinned network.cxx adds both the actual pin layer and its upper via-access
    # layer. This macro has only M1 pin geometry, including both PG pins.
    need(set(re.findall(r'^\s*LAYER\s+(Metal\d+)\s*;',macro[1],re.M))=={'Metal1'},'Antenna master used layers changed')
    return dict(pin_rectangles=rects, via=enclosures, spacing=spacing, via_name='Via1_YY',dpl_used_layers=[1,2],
        width=1440,height=3780,escape_width=200)


def targets(before, current, explicit=None):
    need(set(before['instances']) <= set(current['instances']), 'Canonical antenna repair removed an existing instance')
    need(all(current['instances'][n]['master'] == r['master'] for n,r in before['instances'].items()),
        'Canonical antenna repair changed an existing master')
    if explicit is None:
        # dbInst names are unique within the live block. dbObject::getId is a
        # C++ base API not included by the pinned Tcl SWIG interface.
        names = set(current['instances']) - set(before['instances'])
    else: names = list(explicit)
    need(len(names) == len(set(names)), 'Duplicate target instance')
    for name in names:
        need(name in current['instances'] and current['instances'][name]['master'] == MASTER, 'Target is not canonical diode')
        need(current['instances'][name]['status'] == 'PLACED', 'Canonical diode is not movable PLACED')
        signal = [(pin,t) for (inst,pin),t in current['terminals'].items() if inst == name and t[1] not in ('POWER','GROUND')]
        need(len(signal) == 1 and signal[0][0] == 'A' and signal[0][1][0] == 'INPUT' and signal[0][1][2] in current['nets'], 'Diode A connectivity differs')
    return sorted(names,key=lambda n:(current['instances'][n]['box'][1],current['instances'][n]['box'][0],n))


def grid_values(lo, hi, track):
    start,count,pitch = track; first=max(0,(lo-start+pitch-1)//pitch); last=min(count-1,(hi-start)//pitch)
    return [start+k*pitch for k in range(first,last+1)]


def access(x,y,orient, model, geo, pg):
    body=(x,y,x+1440,y+3780); pins=[transform(r,x,y,orient) for r in model['pin_rectangles']]
    m2 = [box for _,layer,box,_ in pg if layer in ('Metal2','*')]
    m1 = [box for _,layer,box,_ in pg if layer in ('Metal1','*')]
    # Keep every possible A-pin landing safely clear of M2 PG, rather than only
    # avoiding one measured via center. The larger default-via/spacing envelope
    # is conservative; actual routing remains an independent acceptance gate.
    extent=max(abs(v) for v in model['via']['Metal2'])
    if any(clearance(pin,box) < model['spacing']['Metal2']+extent for pin in pins for box in m2): return None
    for pin in pins:
        for px in grid_values(pin[0],pin[2],geo['tracks']['Metal2','X']):
            for py in grid_values(pin[1],pin[3],geo['tracks']['Metal1','Y']):
                v1=translate(model['via']['Metal1'],px,py);v2=translate(model['via']['Metal2'],px,py)
                if not contains(body,v1) or not intersect(v1,pin):continue
                if any(clearance(v1,b)<model['spacing']['Metal1'] for b in m1):continue
                if any(clearance(v2,b)<model['spacing']['Metal2'] for b in m2):continue
                length=2*geo['tracks']['Metal2','X'][2]
                for direction in (-1,1):
                    end=py+direction*length;escape=(px-100,min(py,end)-100,px+100,max(py,end)+100)
                    if contains(CORE,escape) and all(clearance(escape,b)>=model['spacing']['Metal2'] for b in m2):
                        return dict(via=model['via_name'],point_dbu=[px,py],Metal1=v1,Metal2=v2,
                            escape_dbu=escape,spacing_envelope=model['spacing'],all_A_pin_M2_PG_envelope_clear=True)
    return None


def search_sites(box, geo, policy):
    """Lazy exact candidate order; B holds one next-x entry per official row."""
    need(policy in POLICIES,'Undeclared placement policy')
    old_row=(box[1]-3780)//3780
    if policy=='A':
        # Preserve the original policy-A candidate order byte for byte.
        for dx in [0]+[sign*k for k in range(1,17) for sign in (-1,1)]:
            yield old_row,box[0]+dx*480,box[1]
        return
    first,last,pitch=CORE[0],CORE[2]-1440,480
    count=(last-first)//pitch+1
    def xs():
        center=max(0,min(count-1,(box[0]-first)//pitch))
        yield first+center*pitch
        for delta in range(1,max(center+1,count-center)):
            for index in (center-delta,center+delta):
                if 0<=index<count:yield first+index*pitch
    heap=[];generators=[]
    for k,row in enumerate(geo['rows']):
        generator=xs();generators.append(generator);x=next(generator);y=row['y'];dy=abs(y-box[1])
        heapq.heappush(heap,(abs(x-box[0])+dy,dy,y,x,k))
    while heap:
        _,dy,y,x,k=heapq.heappop(heap)
        yield k,x,y
        x=next(generators[k],None)
        if x is not None:heapq.heappush(heap,(abs(x-box[0])+dy,dy,y,x,k))


def blocked_regions(special, model):
    need(special is not None,'Complete source-bound live special routing census required')
    result=[]
    for net,layer,box,kind in special:
        if layer not in ('Metal2','Metal3') or int(layer[5:]) not in model['dpl_used_layers'] or kind=='DRCFILL':continue
        if box[3]-box[1]<=box[2]-box[0]:continue
        # Exact uniform official-grid specialization of Grid::gridCovering:
        # core-relative floor start, ceil end, clipped to legal core pixels.
        l=max(0,(box[0]-CORE[0])//480);r=min(3580,(box[2]-CORE[0]+479)//480)
        d=max(0,(box[1]-CORE[1])//3780);u=min(186,(box[3]-CORE[1]+3779)//3780)
        if l<r and d<u:result.append((net,layer,(CORE[0]+l*480,CORE[1]+d*3780,CORE[0]+r*480,CORE[1]+u*3780)))
    return result


def plan(current, names, geo, model, policy, deadline=None):
    need(policy in POLICIES, 'Undeclared placement policy')
    blocked=blocked_regions(current['special'],model)
    occupied=defaultdict(list); target_set=set(names)
    for name,row in current['instances'].items():
        if name in target_set:continue
        box=row['box']
        for k,site in enumerate(geo['rows']):
            if box[1]<site['y']+3780 and site['y']<box[3]:occupied[k].append((box[0],box[2],name))
    for k in occupied: occupied[k].sort()
    moves=[]
    def legal(box,row_index):
        if not contains(CORE,box):return False
        if any(intersect(box,region) for _,_,region in blocked):return False
        for block,soft in current['blockages']:
            if soft=='0' and intersect(box,block):return False
        for l,r,_ in occupied[row_index]:
            if l < box[2] and box[0] < r:return False
            if box[0]-r == 480 or l-box[2] == 480:return False
        return True
    for name in names:
        if deadline is not None:need(time.monotonic()<=deadline, 'Bounded HOST planner time expired')
        old=current['instances'][name];box=old['box'];need(box[2]-box[0]==1440 and box[3]-box[1]==3780,'Target dimensions differ')
        old_row=(box[1]-3780)//3780;need(0<=old_row<186 and geo['rows'][old_row]['y']==box[1] and (box[0]-2880)%480==0,'Target off original row/site')
        found=None
        for k,x,y in search_sites(box,geo,policy):
            if policy=='B' and deadline is not None:need(time.monotonic()<=deadline,'Bounded HOST planner time expired')
            mirrored=old['orient'] in ('MY','R180')
            orient=('MY' if mirrored else 'R0') if geo['rows'][k]['orient']=='N' else ('R180' if mirrored else 'MX')
            newbox=(x,y,x+1440,y+3780)
            if not legal(newbox,k):continue
            certificate=access(x,y,orient,model,geo,current['pg'])
            if certificate is not None:found=dict(instance=name,master=MASTER,before=old,
                x=x,y=y,orient=orient,box=newbox,certificate=certificate,native_blocked_layer_raster_clear=True);break
        need(found is not None,'No finite PG-safe legal site for '+name+' under policy '+policy)
        moves.append(found);occupied[(found['y']-3780)//3780].append((found['x'],found['x']+1440,name))
    return moves


def unchanged(baseline, after, moves):
    wanted={m['instance']:m for m in moves}
    need(set(after['instances'])==set(baseline['instances']), 'Hook added/deleted an instance')
    for key in ('terminals','nets','ports','public','pg','blockages','special','special_nets'):
        need(after[key]==baseline[key], 'Hook changed connectivity/interface/fixed geometry: '+key)
    for name,row in baseline['instances'].items():
        actual=after['instances'][name]
        if name not in wanted:need(actual==row,'Hook moved/changed existing instance: '+name)
        else:
            move=wanted[name];need(actual==dict(row,box=tuple(move['box']),orient=move['orient']), 'Applied target differs: '+name)


def make_request(tech_lef, cell_lef, policy='A', *, native_tech_lef=None, native_cell_lef=None):
    need(policy in POLICIES,'Undeclared policy')
    return dict(schema=SCHEMA,top=TOP,policy=policy,tech_lef=str(native_tech_lef or tech_lef),cell_lef=str(native_cell_lef or cell_lef),
        policy_definition=deepcopy(POLICIES[policy]),
        native_placement_legality=deepcopy(BLOCKED_RULE),snapshot_version=2,
        tech_sha256=sha(tech_lef),cell_sha256=sha(cell_lef),planner_seconds=60,
        source_sha256=sha(__file__),qualified=False,physical_acceptance=False)


def validate_request(request, policy):
    need(request['schema']==SCHEMA and request['source_sha256']==sha(__file__) and request['planner_seconds']==60 and
        request['top']==TOP and request['policy']==policy and request['policy_definition']==POLICIES[policy] and
        request['native_placement_legality']==BLOCKED_RULE and request['snapshot_version']==2 and
        request['qualified'] is False and request['physical_acceptance'] is False,'Request/source/budget/policy differs')


def main():
    # A pure helper can fail independently of the owning CAD process. Bound
    # its complete parse/plan/verify lifetime, not only the search loop.
    def expired(*_): raise TimeoutError('PG-diode helper exceeded its fixed 60-second budget')
    signal.signal(signal.SIGALRM, expired);signal.alarm(60)
    p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='mode',required=True)
    for mode in ('plan','verify'):
        q=sub.add_parser(mode)
        for n in ('request','before','current','def','output'):q.add_argument('--'+n,dest='def_path' if n=='def' else n,type=Path,required=True)
        q.add_argument('--policy',choices=tuple(POLICIES),required=True)
        q.add_argument('--explicit',type=Path);q.add_argument('--moves',type=Path,required=True)
        if mode=='verify':q.add_argument('--plan',type=Path,required=True)
    a=p.parse_args();request=json.loads(a.request.read_text());validate_request(request,a.policy)
    baseline=read_snapshot(a.before);current=read_snapshot(a.current);geo=geometry(a.def_path)
    need(baseline['special'] is not None and current['special'] is not None,'Native capture must include complete v2 special shapes')
    model=profile(request['tech_lef'],request['cell_lef'],request)
    if a.mode=='plan':
        explicit=a.explicit.read_text().splitlines() if a.explicit else None
        names=targets(baseline,current,explicit);moves=plan(current,names,geo,model,request['policy'],time.monotonic()+60)
        row=dict(schema=SCHEMA,policy=request['policy'],policy_definition=POLICIES[a.policy],native_placement_legality=BLOCKED_RULE,targets=names,moves=moves,
            input_sha256={str(f):sha(f) for f in [a.request,a.before,a.current,a.def_path,Path(request['tech_lef']),Path(request['cell_lef'])]},
            source_sha256=sha(__file__),qualified=False,physical_acceptance=False,
            access_scope='One explicit default-via/M2 escape witness plus conservative full A-pin PG envelope; actual DRT remains required')
        write(a.output,row);need(not a.moves.exists(),'Preserve old move response')
        a.moves.write_text(''.join('\t'.join(map(str,[m['instance'],m['x'],m['y'],m['orient']]))+'\n' for m in moves))
    else:
        row=json.loads(a.plan.read_text());need(row['schema']==SCHEMA and row['source_sha256']==sha(__file__) and
            row['policy']==a.policy and row['policy_definition']==POLICIES[a.policy] and
            row['native_placement_legality']==BLOCKED_RULE,'Plan/source/policy/legality changed')
        need(all(sha(f)==h for f,h in row['input_sha256'].items()),'Planning input changed')
        unchanged(baseline,current,row['moves'])
        for m in row['moves']:
            need(access(m['x'],m['y'],m['orient'],model,geo,current['pg']) is not None,'Access lost after live application')
            need(not any(intersect(tuple(m['box']),r) for _,_,r in blocked_regions(current['special'],model)),
                'Native blocked-layer legality lost after application')
        write(a.output,dict(schema=SCHEMA,verified=True,targets=row['targets'],source_sha256=sha(__file__),
            snapshot_sha256=sha(a.current),native_placement_legality=BLOCKED_RULE,
            native_blocked_layer_raster_clear=True,special_routing_shapes=len(current['special']),qualified=False,physical_acceptance=False))
    signal.alarm(0)
    return 0


def literal(value):
    value=str(value);need(not any(c in value for c in '\\{}\n\r\t'),'Unsupported Tcl literal')
    return '{'+value+'}'


def hook_tcl(request_path, output_dir=None, *, python_executable=None, helper_path=None, policy='A', initial_names=()):
    need(policy in POLICIES,'Undeclared hook policy')
    python_executable=python_executable or sys.executable;helper_path=helper_path or str(Path(__file__).resolve())
    prelude='namespace eval ::pgd {\n variable request '+literal(request_path)+'\n variable python '+literal(python_executable)+'\n variable helper '+literal(helper_path)+'\n variable policy '+literal(policy)+'\n variable counter 0\n variable output '+(literal(output_dir) if output_dir is not None else '[file join $::env(STEP_DIR) pg-diode]')+'\n variable initial [list '+' '.join(literal(n) for n in initial_names)+']\n}\n'
    return prelude+TCL


TCL = r'''
proc ::pgd::need {ok message} {if {!$ok} {error $message}}
proc ::pgd::row {f args} {
    foreach value $args {::pgd::need [expr {![regexp {[\t\r\n]} $value]}] {Unsupported snapshot identifier}}
    puts $f [join $args "\t"]
}
proc ::pgd::capture {path} {
    set block [ord::get_db_block];set f [open $path w]
    ::pgd::row $f SNAPSHOT 2
    ::pgd::row $f TOP [$block getName]
    foreach inst [$block getInsts] {
        set b [$inst getBBox]
        ::pgd::row $f INST [$inst getName] [[$inst getMaster] getName] [$b xMin] [$b yMin] [$b xMax] [$b yMax] [$inst getOrient] [$inst getPlacementStatus]
        foreach term [$inst getITerms] {
            set net [$term getNet];set n "";if {$net ne "NULL"} {set n [$net getName]}
            set m [$term getMTerm];::pgd::row $f ITERM [$inst getName] [$m getName] [$m getIoType] [$m getSigType] $n
        }
    }
    foreach net [$block getNets] {
        ::pgd::row $f NET [$net getName] [$net getSigType] [llength [$net getITerms]] [llength [$net getBTerms]] [$net isSpecial]
        if {[$net getSigType] in {POWER GROUND} || [$net isSpecial]} {
            foreach wire [$net getSWires] {foreach b [$wire getWires] {
                set layer *;set via [$b isVia];if {!$via} {set layer [[$b getTechLayer] getName]}
                if {[$net getSigType] in {POWER GROUND}} {::pgd::row $f PG [$net getName] $layer [$b xMin] [$b yMin] [$b xMax] [$b yMax] $via}
                if {[$net isSpecial] && !$via} {::pgd::row $f SPECIAL [$net getName] $layer [$b xMin] [$b yMin] [$b xMax] [$b yMax] [$b getWireShapeType]}
            }}
        }
    }
    foreach term [$block getBTerms] {
        set net [$term getNet];set n "";if {$net ne "NULL"} {set n [$net getName]}
        ::pgd::row $f BTERM [$term getName] [$term getIoType] [$term getSigType] $n
        foreach pin [$term getBPins] {foreach b [$pin getBoxes] {
            ::pgd::row $f BPIN [$term getName] [[$b getTechLayer] getName] [$b xMin] [$b yMin] [$b xMax] [$b yMax] [$pin getPlacementStatus]
        }}
    }
    foreach blockage [$block getBlockages] {
        set b [$blockage getBBox];::pgd::row $f BLOCKAGE [$b xMin] [$b yMin] [$b xMax] [$b yMax] [$blockage isSoft]
    }
    close $f
}
proc ::pgd::directory {} {
    variable counter;variable output;incr counter
    set d [file join $output [format call-%03d $counter]]
    ::pgd::need [expr {![file exists $d]}] {Preserve prior PG-diode call};file mkdir $d;return $d
}
proc ::pgd::apply {d explicit} {
    variable request;variable python;variable helper
    ::pgd::capture $d/postcanonical.tsv;write_def $d/postcanonical.def
    set args [list $python -B $helper plan --policy $::pgd::policy --request $request --before $d/before.tsv --current $d/postcanonical.tsv --def $d/postcanonical.def --output $d/plan.json --moves $d/moves.tsv]
    if {$explicit ne ""} {lappend args --explicit $explicit}
    exec {*}$args
    set f [open $d/moves.tsv r];set text [read $f];close $f
    set moves [list]
    foreach line [split [string trimright $text "\n"] "\n"] {
        if {$line eq ""} {continue};set row [split $line "\t"]
        ::pgd::need [expr {[llength $row]==4}] {Bad move response};lassign $row name x y orient
        set inst [[ord::get_db_block] findInst $name]
        ::pgd::need [expr {$inst ne "NULL" && [$inst getName] eq $name && [[$inst getMaster] getName] eq "sg13cmos5l_antennanp"}] {Move owner/master mismatch}
        ::pgd::need [expr {[string is integer -strict $x] && [string is integer -strict $y] && $orient in {R0 MX MY R180}}] {Bad move coordinates/orientation}
        lappend moves [list $inst $x $y $orient]
    }
    if {[llength $moves]} {
        grt::start_incremental
        foreach row $moves {lassign $row inst x y orient;$inst setOrient $orient;$inst setLocation $x $y}
        grt::end_incremental
    }
    ::pgd::capture $d/applied.tsv;write_def $d/applied.def;write_db $d/applied.odb;write_guides $d/applied.guide
    check_placement -verbose -report_file_name $d/placement.json
    set args [list $python -B $helper verify --policy $::pgd::policy --request $request --before $d/postcanonical.tsv --current $d/applied.tsv --def $d/applied.def --output $d/verified.json --moves $d/moves.tsv --plan $d/plan.json]
    exec {*}$args
    puts "PINWHEEL_PG_DIODE_VERIFIED $d";flush stdout
}
proc pg_diode_apply_existing {names} {
    set d [::pgd::directory];::pgd::capture $d/before.tsv
    set f [open $d/explicit.tsv w];foreach name $names {::pgd::row $f $name};close $f
    ::pgd::apply $d $d/explicit.tsv
}
proc pg_diode_bootstrap {} {pg_diode_apply_existing $::pgd::initial}
::pgd::need [expr {[llength [info commands ::pgd::canonical_repair_antennas]]==0}] {PG-diode hook already installed}
rename ::repair_antennas ::pgd::canonical_repair_antennas
proc ::repair_antennas {args} {
    set d [::pgd::directory];::pgd::capture $d/before.tsv
    set result [::pgd::canonical_repair_antennas {*}$args]
    ::pgd::apply $d ""
    return $result
}
'''


if __name__=='__main__':raise SystemExit(main())
