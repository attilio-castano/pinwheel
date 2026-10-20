"""Observe exact raw one-bit AND cones; no equivalence or timing acceptance."""
import argparse
import hashlib
import json
from pathlib import Path


def require(ok,message):
    if not ok:raise ValueError(message)


def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def one_and(cell):
    return cell['type']=='$and' and all(len(cell['connections'][pin])==1 for pin in ('A','B','Y'))


def drivers(module):
    result={}
    for name,cell in module['cells'].items():
        for pin,direction in cell['port_directions'].items():
            if direction!='output':continue
            for index,bit in enumerate(cell['connections'][pin]):
                require(type(bit)is int and bit not in result,'Ambiguous or literal cell output')
                result[bit]=(name,cell,pin,index)
    return result


def and_depths(drv):
    memo={};active=set()
    def depth(bit):
        if bit not in drv or not one_and(drv[bit][1]):return 0
        if bit in memo:return memo[bit]
        require(bit not in active,'Cyclic one-bit AND cone');active.add(bit)
        cell=drv[bit][1];memo[bit]=1+max(depth(cell['connections'][pin][0]) for pin in ('A','B'))
        active.remove(bit);return memo[bit]
    return {bit:depth(bit) for bit in drv if one_and(drv[bit][1])}


def literal(bits):
    return sum(int(bit)<<index for index,bit in enumerate(bits)) if all(bit in ('0','1') for bit in bits) else None


def evaluate(bit,cut,drv,cache=None,active=None):
    """Exact finite Boolean/unsigned comparison evaluation on an explicit cut."""
    if type(bit)is str:
        require(bit in ('0','1'),'Unknown literal');return int(bit)
    if bit in cut:return cut[bit]
    cache={} if cache is None else cache;active=set() if active is None else active
    if bit in cache:return cache[bit]
    require(bit in drv and bit not in active,'Cut does not cover the finite cone')
    _,cell,pin,index=drv[bit];active.add(bit);wires=cell['connections'];kind=cell['type']
    require(pin=='Y' and kind in ('$not','$and','$or','$xor','$logic_not','$reduce_or','$reduce_and','$lt','$gt','$eq','$ne'),
            'Unsupported finite cone operator')
    require(all(int(cell.get('parameters',{}).get(key,'0'),2)==0 for key in ('A_SIGNED','B_SIGNED')),
            'Signed operator is outside this unsigned cut observer')
    def value(port):return sum(evaluate(child,cut,drv,cache,active)<<i for i,child in enumerate(wires[port]))
    a=value('A');b=value('B') if 'B'in wires else None;width=len(wires['Y'])
    out={'$not':lambda:~a,'$and':lambda:a&b,'$or':lambda:a|b,'$xor':lambda:a^b,
        '$logic_not':lambda:int(a==0),'$reduce_or':lambda:int(a!=0),
        '$reduce_and':lambda:int(a==(1<<len(wires['A']))-1),'$lt':lambda:int(a<b),
        '$gt':lambda:int(a>b),'$eq':lambda:int(a==b),'$ne':lambda:int(a!=b)}[kind]()
    result=((out&((1<<width)-1))>>index)&1;active.remove(bit);cache[bit]=result;return result


def predicate_candidates(kind,module,drv):
    if kind=='core':
        selected=module['netnames']['r_written']['bits'];cutbits=module['ports']['count']['bits']
    else:
        selected=module['netnames']['r_request']['bits'][16:80]
        vectors=set()
        for cell in module['cells'].values():
            if cell['type']=='$lt' and len(cell['connections']['A'])==7 and literal(cell['connections']['B']) is not None:
                vectors.add(tuple(cell['connections']['A']))
        # Identify wanted by its repeated comparisons against tail thresholds.
        counts={bits:sum(c['type']=='$lt' and tuple(c['connections']['A'])==bits and
            literal(c['connections']['B']) in range(1,65) for c in module['cells'].values()) for bits in vectors}
        require(counts,'No wanted7 cut candidates')
        maximum=max(counts.values());choices=[bits for bits,count in counts.items() if count==maximum]
        require(len(choices)==1 and maximum>=32,'Ambiguous or insufficient wanted7 comparison cut')
        cutbits=list(choices[0])
    require(len(selected)==64 and len(set(selected))==64 and len(cutbits)==7 and len(set(cutbits))==7 and
        not set(selected)&set(cutbits),'Invalid semantic cut width/alias')
    candidates={index:[] for index in range(64)}
    for wire,(_,cell,pin,index) in drv.items():
        if pin!='Y' or index!=0 or cell['type']!='$not' or len(cell['connections']['A'])!=1:continue
        inner=drv.get(cell['connections']['A'][0])
        if not inner or not one_and(inner[1]):continue
        operands=[inner[1]['connections'][p][0] for p in ('A','B')]
        for operand in operands:
            target=operand
            if kind=='core':
                neg=drv.get(operand)
                if not neg or neg[1]['type']!='$not' or len(neg[1]['connections']['A'])!=1:continue
                target=neg[1]['connections']['A'][0]
            if target not in selected:continue
            slot=selected.index(target);matches=True
            try:
                for value in range(128):
                    for stored in (0,1):
                        cut={bit:(value>>i)&1 for i,bit in enumerate(cutbits)};cut[target]=stored
                        expected=int(not(slot<value) or stored) if kind=='core' else int(not(value<64-slot) or not stored)
                        if evaluate(wire,cut,drv)!=expected:matches=False;break
                    if not matches:break
            except ValueError:matches=False
            if matches:candidates[slot].append(wire)
    require(all(len(values)==1 for values in candidates.values()),'Missing or ambiguous exact semantic predicate leaf')
    return {values[0]:index for index,values in candidates.items()},cutbits,selected


def observe(path,top,kind):
    path=Path(path)
    require(kind in ('frontend','core') and path.is_file() and not path.is_symlink(),'Exact kind and regular raw JSON required')
    before=sha(path);payload=json.loads(path.read_text());module=payload['modules'][top];drv=drivers(module);depths=and_depths(drv)
    leaves,cutbits,statebits=predicate_candidates(kind,module,drv);memo={};active=set()
    def flatten(bit):
        if bit in leaves:return [leaves[bit]],0,0,[]
        if bit=='1':return [],-1,1,[]
        if bit in memo:return memo[bit]
        if bit not in drv or not one_and(drv[bit][1]):return [],-1,0,[bit]
        require(bit not in active,'Cyclic predicate context');active.add(bit)
        try:
            cell=drv[bit][1];a=flatten(cell['connections']['A'][0]);b=flatten(cell['connections']['B'][0])
            longest=max(a[1],b[1]);memo[bit]=(a[0]+b[0],longest+1 if longest>=0 else -1,a[2]+b[2],a[3]+b[3]);return memo[bit]
        finally:active.remove(bit)
    roots=[]
    for bit in depths:
        try:slots,depth,identities,context=flatten(bit)
        except ValueError:continue
        if sorted(slots)==list(range(64)):
            children=[flatten(drv[bit][1]['connections'][pin][0])[0] for pin in ('A','B')]
            if any(sorted(child)==list(range(64)) for child in children):continue
            roots.append(dict(wire=bit,cell=drv[bit][0],predicate_context_and_depth=depth,
                isolated_guard_wire=not context,constant_one_leaves=identities,
                ordered_predicate_slots=slots,context_leaf_wires=context))
    require(roots,'No AND context combines all64 exact predicates once')
    require(sha(path)==before,'Raw JSON changed during observation')
    return dict(schema='pinwheel.streaming-tt-raw-guard-depth.v1',qualified=False,timing_acceptance_claim=False,
        input=dict(path=str(path.resolve()),sha256=before),input_unchanged=True,top=top,kind=kind,one_bit_and_cells=len(depths),
        longest_consecutive_one_bit_and_depth=max(depths.values(),default=0),guard_roots=roots,
        predicate_leaves=[dict(slot=slot,wire=wire) for wire,slot in sorted(leaves.items(),key=lambda row:row[1])],
        cut_wire_bits=cutbits,state_or_payload_wire_bits=statebits,assignments_checked_per_leaf=256,
        boundary='Finite exact cut-function attribution and raw structural depth only. State/interface correspondence, mapped gates and physical timing require separate evidence.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for key in ('input','top','kind','out'):parser.add_argument('--'+key,required=True,**({'choices':('frontend','core')} if key=='kind' else {}))
    args=parser.parse_args();out=Path(args.out);require(not out.exists(),'Preserve prior depth observation')
    result=observe(args.input,args.top,args.kind);result['producer_sha256']=sha(__file__)
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+'\n');print(out)


if __name__=='__main__':main()
