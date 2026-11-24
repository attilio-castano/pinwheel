"""Strict streaming artifact interpretation and generated kernel certificates.

The emitted MLIR supplies proof hints, never acceptance. Every hint root is
connected to the typed circuit by Lean conversion. Imported Yosys equations
are independently reconstructed with complete state/output coverage.
"""
import importlib.util
from pathlib import Path
import sys
import json
import re

import buffered_sram_readback as shared
import paired_readback as decomposition
import readback_descriptor

ROOT = Path(__file__).resolve().parents[1]
# The frontend's physical inputs (not the core status it observes), as
# (RTL name, width, constructor); the wrapper read-backs claim these pins.
FRONTEND_INPUTS = [(port['name'], port['width'], port['term'][1:])
    for port in readback_descriptor.checked_in('frontend')['inputs'] if not port['term'].startswith('.status ')]


def backend(kind, addr_bits=1):
    """Configure the importer for one Streaming module from its checked-in Lean
    read-back descriptor; the namespace and Lean header stay here."""
    if kind not in ('core', 'frontend') or type(addr_bits) is not int or addr_bits not in (1,2):
        raise ValueError('Unsupported streaming artifact configuration')
    name = '_streaming_readback_' + kind + str(addr_bits)
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts/backend_readback.py')
    rb = importlib.util.module_from_spec(spec)
    sys.modules[name] = rb
    spec.loader.exec_module(rb)
    rb.KIND, rb.ADDR_BITS = kind, addr_bits
    readback_descriptor.apply(rb, readback_descriptor.checked_in(
        'streaming-core-d'+str(2**addr_bits) if kind == 'core' else 'frontend'))
    rb.NAMESPACE = ('Pinwheel.Artifact.StreamingCoreD'+str(2**addr_bits) if kind == 'core'
        else 'Pinwheel.Artifact.StreamingFrontend')
    rb.HEADER = ('import Pinwheel.Hardware.Streaming.FrontendEmit\n'
        'open Pinwheel.Hardware Pinwheel.Hardware.Streaming\nnamespace '+rb.NAMESPACE+'\n'
        'set_option maxRecDepth 100000\nset_option maxHeartbeats 8000000\n'
        'set_option linter.unusedVariables false\n')
    return rb


def adapt(rb,text):
    return (text.replace('Values Machine.Input','Values '+rb.INPUT_TYPE)
        .replace('Values Register','Values '+rb.REGISTER_TYPE)
        .replace('Values Sram.Input','Values '+rb.INPUT_TYPE)
        .replace('Values Sram.Register','Values '+rb.REGISTER_TYPE)
        .replace('Pinwheel.Artifact.Backend',rb.NAMESPACE)
        .replace('Pinwheel.Artifact.BufferedSram',rb.NAMESPACE))


def check_interface(rb,path):
    interface = shared.read_json(path)
    if type(interface.get('schema')) is not int or interface['schema'] != 1 or interface.get('module') != rb.TOP:
        raise ValueError('Changed streaming module/schema')
    decomposition.check_interface(rb,interface)
    if rb.KIND == 'core' and interface.get('addr_bits') != rb.ADDR_BITS:
        raise ValueError('Changed streaming queue depth')


def hints_source(rb,graph):
    return adapt(rb,rb.HEADER+graph.definitions('Source')+'end '+rb.NAMESPACE+'\n')


def graphs_source(rb,graph):
    return adapt(rb,'import Hints\n'+rb.HEADER+graph.definitions('RTL')+'end '+rb.NAMESPACE+'\n')


def sources_source(rb,graph):
    lines = ['import Hints\n'+rb.HEADER]
    factors = frontend_source_factors(rb,graph) if rb.KIND == 'frontend' else None
    if factors:
        lines.append(factors['helpers'])
    for operation,roots,interface in [('next',graph.next,rb.REGISTERS),('output',graph.outputs,rb.OUTPUTS)]:
        for name,node in roots.items():
            proof = factors['proofs'].get(name,'  rfl') if factors and operation == 'next' else '  rfl'
            lines.append('theorem source_'+operation+'_'+name+
                ' (i : Values '+rb.INPUT_TYPE+') (s : Values '+rb.REGISTER_TYPE+') :\n    '+
                rb.graph_value(graph,node,'Source')+' = ('+rb.CIRCUIT+'.'+operation+
                ' ('+interface[name][1]+')).eval i s := by\n'+proof+'\n')
    return adapt(rb,'\n'.join(lines)+'\nend '+rb.NAMESPACE+'\n')


def frontend_source_factors(rb,graph):
    """Share closed guard conversions without adding any theorem premise.

    Recover the three cut points from endpoint structure, rather than SSA
    numbering. These checks reject a changed graph shape before proposing
    proofs; Lean still checks every helper and all original endpoint types.
    """
    def require(condition):
        if not condition: raise ValueError('Changed frontend Source guard/endpoint shape')
    def node(name,op,width=None):
        require(name in graph.nodes)
        item=graph.nodes[name]
        require(item.op==op and (width is None or item.width==width))
        return item.args
    def raw(name):
        width=rb.REGISTERS[name][0]
        init,zero,result=node(graph.next[name],'mux',width)
        require(graph.nodes[init].op=='input' and graph.nodes[init].value=='initialize')
        require(graph.nodes[zero].op=='lit' and graph.nodes[zero].width==width and graph.nodes[zero].value==0)
        return result
    require(set(graph.next)==set(rb.REGISTERS) and set(graph.outputs)==set(rb.OUTPUTS))
    admitting=node(raw('r_tx_left'),'mux',7)[0]
    phase,bulk_admitted=node(admitting,'and',1)
    bulk,admitted=node(bulk_admitted,'and',1)
    _,offset_tail=node(admitted,'and',1)
    _,tail_rest=node(offset_tail,'and',1)
    tail,_=node(tail_rest,'and',1)
    leaves=[]
    def balanced(at,depth):
        if depth:
            a,b=node(at,'and',1);balanced(a,depth-1);balanced(b,depth-1)
        else:
            condition,=node(at,'not',1)
            node(condition,'and',1);leaves.append(at)
    balanced(tail,6)
    require(len(leaves)==len(set(leaves))==64)
    code_raw=raw('r_code')
    _,_,code_phase=node(code_raw,'mux',4)
    code_phase_guard,code_bulk,_=node(code_phase,'mux',4)
    code_bulk_guard,code_tail,_=node(code_bulk,'mux',4)
    code_tail_guard,code_admitted,_=node(code_tail,'mux',4)
    require(code_phase_guard==phase and code_bulk_guard==bulk and code_tail_guard==tail and
        node(code_admitted,'mux',4)[0]==admitted)
    _,_,phase_next=node(raw('r_phase'),'mux',3)
    phase_guard,phase_bulk,_=node(phase_next,'mux',3)
    phase_bulk_guard,phase_admitted,_=node(phase_bulk,'mux',3)
    require(phase_guard==phase and phase_bulk_guard==bulk and node(phase_admitted,'mux',3)[0]==admitted)
    def depends(root,target):
        seen=set();pending=[root]
        while pending:
            at=pending.pop()
            if at==target:return True
            if at not in seen:seen.add(at);pending.extend(graph.nodes[at].args)
        return False
    affected=('r_tx_left','r_tx_staging','r_rx_pending','r_work_bulk',
        'r_export_data','r_export_start','r_export_bits','r_ack_offset')
    require(all(depends(raw(name),admitting) for name in affected))
    helpers=f'''private theorem source_tail_correct (i : Values Frontend.Input) (s : Values Frontend.Register) :
    Source.{tail} i s = Frontend.tailCanonical.eval i s := by
  rfl

private theorem source_bulk_correct (i : Values Frontend.Input) (s : Values Frontend.Register) :
    Source.{admitted} i s = Frontend.bulkAdmitted.eval i s := by
  let context (tail : BitVec 1) : BitVec 1 :=
    Frontend.bulkOwner.eval i s &&& (Frontend.bulkOffsets.eval i s &&&
      (tail &&& ((Frontend.either (.zero Frontend.wanted) (Frontend.status .busy)).eval i s &&&
        (Expr.inv (.ult (Frontend.status .txFree) Frontend.beatsNeeded)).eval i s)))
  calc
    Source.{admitted} i s = context (Source.{tail} i s) := by rfl
    _ = context (Frontend.tailCanonical.eval i s) := congrArg context (source_tail_correct i s)
    _ = Frontend.bulkAdmitted.eval i s := by rfl

private theorem source_admitting_correct (i : Values Frontend.Input) (s : Values Frontend.Register) :
    Source.{admitting} i s = Frontend.admittingBulk.eval i s := by
  let context (admitted : BitVec 1) : BitVec 1 :=
    (Frontend.isPhase 1).eval i s &&& (Frontend.bulk.eval i s &&& admitted)
  calc
    Source.{admitting} i s = context (Source.{admitted} i s) := by rfl
    _ = context (Frontend.bulkAdmitted.eval i s) := congrArg context (source_bulk_correct i s)
    _ = Frontend.admittingBulk.eval i s := by rfl
'''
    contexts={
        'r_phase':('admitted', 'BitVec 1', admitted, 'Frontend.bulkAdmitted.eval i s','source_bulk_correct i s', '''if Frontend.closingRequest.eval i s = 1 then
      if Frontend.duplicate.eval i s = 1 then 0 else
      if (Expr.zero Frontend.closingCode).eval i s = 1 then 1 else 3
    else if (Frontend.isPhase 1).eval i s = 1 then
      if Frontend.bulk.eval i s = 1 then (if admitted = 1 then 2 else 3) else 3
    else if (Frontend.isPhase 2).eval i s = 1 then
      if (Frontend.either Frontend.stageDone Frontend.stageRejected).eval i s = 1 then 3 else 2
    else if (Frontend.isPhase 3).eval i s = 1 then 4 else
      if Frontend.finishingCRC.eval i s = 1 then 0 else s .phase'''),
        'r_code':('guards','BitVec 1 × BitVec 1',f'({tail},{admitted})',
            '(Frontend.tailCanonical.eval i s, Frontend.bulkAdmitted.eval i s)',
            'Prod.ext (source_tail_correct i s) (source_bulk_correct i s)', '''if Frontend.closingRequest.eval i s = 1 then Frontend.closingCode.eval i s else
    if (Frontend.isPhase 1).eval i s = 1 then
      if Frontend.bulk.eval i s = 1 then
        if guards.1 = 1 then (if guards.2 = 1 then 0 else 5) else 4
      else (if (Frontend.status .rejected).eval i s = 1 then 5 else s .code)
    else (if Frontend.stageRejected.eval i s = 1 then 5 else s .code)'''),
    }
    admitting_contexts={
        'r_tx_left':'''if admitting = 1 then Frontend.wanted.eval i s else
    if Frontend.stagedTX.eval i s = 1 then
      s .txLeft - ((0 : BitVec 1) ++ Frontend.stagedBits.eval i s)
    else s .txLeft''',
        'r_tx_staging':'''if admitting = 1 then (Frontend.payload 0 64 (by decide)).eval i s else
    if Frontend.stagedTX.eval i s = 1 then
      (s .txStaging).extractLsb' 0 32 ++ (0 : BitVec 32)
    else s .txStaging''',
        'r_rx_pending':'''if admitting = 1 then (Expr.inv (.zero (Frontend.status .rxQueued))).eval i s else
    if Frontend.stagedRX.eval i s = 1 then 0 else s .rxPending''',
        'r_work_bulk':'''if Frontend.closingRequest.eval i s = 1 then 0 else
    if admitting = 1 then 1 else s .workBulk''',
        'r_export_data':'''if Frontend.clearingExport.eval i s = 1 then 0 else
    if admitting = 1 then 0 else
    if Frontend.stagedRX.eval i s = 1 then (0 : BitVec 32) ++ (Frontend.status .rxData).eval i s
    else s .exportData''',
        'r_export_start':'''if Frontend.clearingExport.eval i s = 1 then 0 else
    if admitting = 1 then (Frontend.status .rxPopped).eval i s else s .exportStart''',
        'r_export_bits':'''if Frontend.clearingExport.eval i s = 1 then 0 else
    if admitting = 1 then 0 else
    if Frontend.stagedRX.eval i s = 1 then (0 : BitVec 1) ++ (Frontend.status .rxBits).eval i s
    else s .exportBits''',
        'r_ack_offset':'''if Frontend.clearingExport.eval i s = 1 then 0 else
    if admitting = 1 then (Frontend.payload 64 16 (by decide)).eval i s else s .ackOffset''',
    }
    contexts.update({name:('admitting','BitVec 1',admitting,'Frontend.admittingBulk.eval i s',
        'source_admitting_correct i s',body) for name,body in admitting_contexts.items()})
    proofs={}
    for name,(parameter,kind,cut,typed,equality,body) in contexts.items():
        width,ctor=rb.REGISTERS[name]
        actual=f'(Source.{tail} i s, Source.{admitted} i s)' if name=='r_code' else f'(Source.{cut} i s)'
        proofs[name]=f'''  let context ({parameter} : {kind}) : BitVec {width} :=
    if i .initialize = 1 then 0 else
    {body}
  calc
    Source.{graph.next[name]} i s = context {actual} := by rfl
    _ = context ({typed}) := congrArg context ({equality})
    _ = ({rb.CIRCUIT}.next ({ctor})).eval i s := by rfl'''
    return dict(helpers=helpers,proofs=proofs,cuts=dict(tail=tail,admitted=admitted,admitting=admitting))


def helper_source(rb,pairs):
    text = adapt(rb,shared.local_proofs_source(rb,pairs))
    text = 'import Pinwheel.Hardware.Streaming.Readback\n' + text
    text = text.replace('set_option linter.unusedSimpArgs false',
        'set_option linter.unusedSimpArgs false\nset_option linter.unnecessarySimpa false')
    text = text.replace('  abstract_local_',
        '  by simpa only [BitVec.and_assoc, BitVec.or_assoc] using abstract_local_')
    text = text.replace('  try simp only [BitVec.sub_eq_add_neg]',
        '  try simp only [BitVec.append_assoc, BitVec.cast_eq]\n  try simp only [BitVec.sub_eq_add_neg]')
    text = text.replace('  try simp only [inv_lt_zero,',
        '  try simp only [Pinwheel.Hardware.Streaming.Readback.count_lt2, Pinwheel.Hardware.Streaming.Readback.count_lt4, Pinwheel.Hardware.Streaming.Readback.lt64, Pinwheel.Hardware.Streaming.Readback.lt32, Pinwheel.Hardware.Streaming.Readback.lt16, Pinwheel.Hardware.Streaming.Readback.lt8, Pinwheel.Hardware.Streaming.Readback.lt4, Pinwheel.Hardware.Streaming.Readback.lt2, Pinwheel.Hardware.Streaming.Readback.lt1, inv_lt_zero,')
    for index,pair in enumerate(pairs):
        effective=pair.get('abstract',pair)
        proof=sparse_mask_proof(effective)
        if proof is None:continue
        name=('abstract_local_' if 'abstract' in pair else 'local_')+str(index)
        start=text.index('theorem '+name+' ')
        body=text.index(' := by\n',start)
        choice=text.index('  all_goals first\n',body)
        following=re.search(r'(?m)^(?:private )?theorem ',text[body+1:])
        if following and body+1+following.start()<choice:
            raise ValueError('Changed local proof generator body')
        insertion=choice+len('  all_goals first\n')
        text=text[:insertion]+proof+text[insertion:]
    return text


def sparse_mask_proof(pair):
    """Propose literal-index extensional proofs for exact sparse projections.

    The shape check avoids sending unrelated arithmetic identities through a
    finite bit split. Every emitted proof still checks the original equality.
    """
    left,right=pair['left'],pair['right']
    width,operation,args,_=left
    if not 0<width<=64 or operation!='and' or len(args)!=2:return None
    if args[0][1]=='lit' and args[1][1]=='var':constant,variable=args
    elif args[1][1]=='lit' and args[0][1]=='var':variable,constant=args
    else:return None
    if constant[0]!=width or variable[0]!=width or right[0]!=width:return None
    def projection(tree,offset):
        w,op,children,value=tree
        if op=='lit' and value==0:return 0
        if op=='concat' and len(children)==2 and sum(child[0] for child in children)==w:
            high=projection(children[0],offset+children[1][0]);low=projection(children[1],offset)
            return None if high is None or low is None else high|low
        if op=='slice' and len(children)==1 and children[0]==variable and value==offset and offset+w<=width:
            return ((1<<w)-1)<<offset
        return None
    mask=projection(right,0)
    if mask is None or constant[3]%(1<<width)!=mask:return None
    commute='rw [BitVec.and_comm]\n     ' if args[0][1]=='lit' else ''
    return ('''  | ('''+commute+'''apply BitVec.eq_of_getLsbD_eq
     intro k hk
     have range : '''+' ∨ '.join('k = '+str(k) for k in range(width))+''' := by omega
     rcases range with '''+' | '.join('rfl' for _ in range(width))+'''
     all_goals simp only [BitVec.getLsbD_and, BitVec.getLsbD_append,
       BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat]
     all_goals simp
     all_goals (intro; decide +kernel)
     done)
''')


def boolean_abstractions(rb,pairs,solver):
    """Propose a stronger local theorem with one shared long conjunction atom.

    This reduces propositional reconstruction size after the 64 canonical-tail
    checks have been flattened. SMT proposes the stronger statement only; the
    independent atom is universally quantified in the generated Lean theorem,
    then instantiated with the actual expression using associativity proofs.
    """
    oracle = rb.cut_oracle(solver)
    def key(t): return json.dumps(t,separators=(',',':'))
    def normalized(t):
        width,op,args,value = t
        args = tuple(normalized(a) for a in args)
        if op in ('and','or'):
            leaves = []
            def flatten(a):
                if a[0]==width and a[1]==op:
                    for child in a[2]: flatten(child)
                else: leaves.append(a)
            for a in args: flatten(a)
            result = leaves[-1]
            for a in reversed(leaves[:-1]): result = width,op,(a,result),value
            return result
        return width,op,args,value
    def collect(t,result):
        size = 1+sum(collect(a,result) for a in t[2])
        if t[0]==1 and t[1] in ('and','or') and size>=24:
            result[key(t)] = size,t
        return size
    result = []
    for pair in pairs:
        original = pair.get('abstract',pair)
        left,right = normalized(original['left']),normalized(original['right'])
        ls,rs = {},{}
        collect(left,ls);collect(right,rs)
        common = sorted(ls.keys() & rs.keys(),key=lambda k:-ls[k][0])
        if not common:
            result.append(pair);continue
        target = common[0]
        index = len(original['variables'])
        def replace(t):
            if key(t)==target: return 1,'var',(),index
            return t[0],t[1],tuple(replace(a) for a in t[2]),t[3]
        candidate = dict(left=replace(left),right=replace(right),
            variables=[*original['variables'],(1,'boolean',index)])
        if not oracle(candidate):
            result.append(pair);continue
        old_atoms = original.get('atoms',[])
        def expand(t):
            if t[1]=='var' and t[3]>=len(pair['variables']):
                return old_atoms[t[3]-len(pair['variables'])]
            return t[0],t[1],tuple(expand(a) for a in t[2]),t[3]
        atom = expand(ls[target][1])
        result.append({**pair,'abstract':{**candidate,'atoms':[*old_atoms,atom],
            'shared_boolean_abstraction':True}})
    return result


def links_source(rb,source,rtl,pairs):
    return adapt(rb,'import Hints\n'+rb.links_source(source,rtl,pairs,'LocalProofs','Graphs'))


def register_term(rb, constructor):
    if getattr(rb, 'RETAINED_REGISTER', None):
        return f'⟨{constructor}, trivial⟩'
    return constructor


def model_source(rb,graph):
    lines = ['import Graphs\n'+rb.HEADER]
    for method,interface,roots,result in [('Step',rb.REGISTERS,graph.next,rb.REGISTER_TYPE),
                                         ('Observe',rb.OUTPUTS,graph.outputs,rb.OUTPUT_TYPE)]:
        lines.append('def rtl'+method+' (i : Values '+rb.INPUT_TYPE+') (s : Values '+rb.REGISTER_TYPE+') : Values '+result)
        consumed = set()
        if method == 'Step':
            retained = getattr(rb, 'RETAINED_REGISTER', None)
            if retained:
                for name,ctor in readback_descriptor.plain(rb.DESCRIPTOR,'registers'):
                    if name not in interface:
                        lines.append(f'  | _, ⟨.{ctor}, kept⟩ => by simp [{retained}] at kept')
            for name,ctor,count,width in rb.FAMILIES:
                values = ', '.join('('+rb.graph_value(graph,roots['r_'+name+str(k)],'RTL')+')' for k in range(count))
                pattern = f'.{ctor} k'
                if retained:
                    pattern = f'⟨{pattern}, _⟩'
                lines.append(f'  | _, {pattern} => (#['+values+"])[k.toNat]'(by exact k.isLt)")
                consumed.update('r_'+name+str(k) for k in range(count))
        for name,(_,ctor) in interface.items():
            if name not in consumed:
                if method == 'Step':
                    ctor = getattr(rb, 'REGISTER_PATTERNS', {}).get(name, ctor)
                lines.append('  | _, '+ctor+' => '+rb.graph_value(graph,roots[name],'RTL'))
    return adapt(rb,'\n'.join(lines)+'\nend '+rb.NAMESPACE+'\n')


def endpoints_source(rb,source,rtl,pairs):
    matches = {(p['source'],p['rtl']):k for k,p in enumerate(pairs)}
    lines = ['import Sources\nimport Links\nimport Model\n'+rb.HEADER]
    for operation,roots,actual,interface in [('next',source.next,rtl.next,rb.REGISTERS),('output',source.outputs,rtl.outputs,rb.OUTPUTS)]:
        method,action = ('Step','step') if operation=='next' else ('Observe','observe')
        for name,sn in roots.items():
            rn,ctor = actual[name],interface[name][1]
            lines.append('theorem rtl_'+operation+'_'+name+
                ' (i : Values '+rb.INPUT_TYPE+') (s : Values '+rb.REGISTER_TYPE+') :\n    rtl'+method+
                ' i s ('+ctor+') = '+rb.CIRCUIT+'.'+action+' i s ('+ctor+') := by\n  change ('+
                rb.graph_value(rtl,rn,'RTL')+') = _')
            if (sn,rn) in matches:
                lines.append('  exact (link_'+str(matches[(sn,rn)])+' i s).symm.trans (source_'+operation+'_'+name+' i s)')
            elif sn==rn and source.nodes[sn].op in ('input','reg','lit'):
                lines.append('  exact source_'+operation+'_'+name+' i s')
            else:
                raise ValueError('Missing streaming certificate endpoint: '+name)
    return adapt(rb,'\n'.join(lines)+'\nend '+rb.NAMESPACE+'\n')


def proof_source(rb):
    retained = getattr(rb, 'RETAINED_REGISTER', None)
    lines = ['import Endpoints\nimport Pinwheel.Hardware.Streaming.Package\n'+rb.HEADER,
        'theorem step_correct (i : Values '+rb.INPUT_TYPE+') (s : Values '+rb.REGISTER_TYPE+')',
        '    (r : '+rb.REGISTER_TYPE+' w) : rtlStep i s r = '+rb.CIRCUIT+'.step i s r := by']
    if retained:
        lines.append('  rcases r with ⟨r, kept⟩')
    lines.append('  cases r with')
    if rb.KIND == 'core':
        for name,ctor,count,width in rb.FAMILIES:
            term = '(fun j => Fin.elim0 j)'
            for k in reversed(range(count)):
                term = '(Fin.cases (rtl_next_r_'+name+str(k)+' i s) '+term+')'
            register = register_term(rb, f'.{ctor} (BitVec.ofFin j)')
            lines += ['  | '+ctor+' k =>',
                '    have h : ∀ j : Fin '+str(count)+', rtlStep i s ('+register+') =',
                '        '+rb.CIRCUIT+'.step i s ('+register+') := '+term,
                '    exact h k.toFin']
        for name,ctor in readback_descriptor.plain(rb.DESCRIPTOR,'registers'):
            if retained and name not in rb.REGISTERS:
                lines.append(f'  | {ctor} => simp [{retained}] at kept')
            else:
                lines.append('  | '+ctor+' => exact rtl_next_'+name+' i s')
    else:
        for name,ctor in readback_descriptor.plain(rb.DESCRIPTOR,'registers'):
            lines.append('  | '+ctor+' => exact rtl_next_'+name+' i s')
    lines += ['theorem observe_correct (i : Values '+rb.INPUT_TYPE+') (s : Values '+rb.REGISTER_TYPE+')',
        '    (o : '+rb.OUTPUT_TYPE+' w) : rtlObserve i s o = '+rb.CIRCUIT+'.observe i s o := by',
        '  cases o with']
    if rb.KIND == 'core':
        for name,ctor in readback_descriptor.plain(rb.DESCRIPTOR,'outputs'):
            lines.append('  | '+ctor+' => exact rtl_output_'+name+' i s')
    else:
        lines += ['  | miso => exact rtl_output_miso i s','  | ready => exact rtl_output_ready i s',
            '  | core p =>','    cases p with']
        for name,term in readback_descriptor.plain(rb.DESCRIPTOR,'outputs'):
            if not term.startswith('core .'):
                continue
            ctor = term.removeprefix('core .')
            pattern = '«initialize»' if ctor=='initialize' else ctor
            lines.append('    | '+pattern+' => exact rtl_output_'+name+' i s')
    lines += ['def behavior : Pinwheel.Hardware.Streaming.Package.Behavior '+
        rb.INPUT_TYPE+' '+rb.REGISTER_TYPE+' '+rb.OUTPUT_TYPE+' := ⟨rtlStep,rtlObserve⟩']
    return adapt(rb,'\n'.join(lines)+'\nend '+rb.NAMESPACE+'\n')


def prefix_imports(text,prefix):
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',prefix):
        raise ValueError('Invalid streaming certificate prefix')
    modules = ('Hints','Sources','Graphs','LocalProofs','Links','Model','Endpoints','Proof',
        'MutantGraphs','MutantModel','Reject','Unchanged','PrivateAxiom','Audit')
    for name in modules:
        text = re.sub(r'(?m)^import '+name+r'$', 'import '+prefix+name,text)
    return text


def mutation_specs(kind):
    """Changes to real consumed state/output drivers, plus a positive reimport."""
    if kind == 'core':
        return [('unchanged',None,None,'both'),
            ('program-bank',r'(r_word0 <=[^;]*\? )word( : r_word0;)',
                r"\g<1>(word ^ 64'h1)\g<2>",'next'),
            ('owner-output',r'assign busy = [^;]+;',"assign busy = 1'h0;",'output')]
    if kind == 'frontend':
        return [('unchanged',None,None,'both'),
            ('retained-export',r'(r_export_bits <=[^;]*: )r_export_bits;',r"\g<1>(r_export_bits ^ 7'h1);",'next'),
            ('ready-output',r'assign ready = [^;]+;',"assign ready = 1'h0;",'output')]
    raise ValueError('Unsupported mutation kind')


def mutation_sources(rb,graph,operation):
    """Kernel-reconstruct candidate equations and test the same universal claim.

    A changed candidate cannot borrow the accepted theorem: both theorem types
    include the candidate's independently imported equations. The unchanged
    case must pass these very same declarations.
    """
    if operation not in ('next','output','both'):
        raise ValueError('Unsupported mutation operation')
    graphs = graphs_source(rb,graph).replace('namespace RTL\n','namespace Mutant\n').replace('end RTL\n','end Mutant\n')
    model = model_source(rb,graph).replace('import Graphs\n','import MutantGraphs\n').replace(
        'RTL.','Mutant.').replace('rtlStep','mutantStep').replace('rtlObserve','mutantObserve')
    lines = ['import Proof\nimport MutantModel\n'+rb.HEADER]
    for op,method,typ,theorem in [('next','Step',rb.REGISTER_TYPE,'step_correct'),
                                  ('output','Observe',rb.OUTPUT_TYPE,'observe_correct')]:
        if operation in (op,'both'):
            lines += ['theorem candidate_'+op+' (i : Values '+rb.INPUT_TYPE+') (s : Values '+rb.REGISTER_TYPE+')',
                '    (p : '+typ+' w) : mutant'+method+' i s p = '+rb.CIRCUIT+'.'+
                ('step' if op=='next' else 'observe')+' i s p := by',
                '  exact '+theorem+' i s p']
    lines.append('end '+rb.NAMESPACE)
    return dict(MutantGraphs=graphs,MutantModel=model,Reject='\n'.join(lines)+'\n')

