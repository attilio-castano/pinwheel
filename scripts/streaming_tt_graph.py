"""Small kernel-checkable tables for actual post-physical cell networks.

Balanced lookup and range-cover proofs avoid a quadratic flat-table universal
decision procedure.  Every gate still has an explicit actual function/source
definition and an individual checked topological bound.
"""
from streaming_mapped_certificate import lean_expression, lean_bool, namespace_name, support, substitute
from streaming_mapped_liberty import require


def atom_source(atom):
    if atom[0]=='constant':return '.constant '+str(atom[1]).lower()
    require(atom[0]=='wire','Unknown generated physical atom')
    return '.wire '+str(atom[1])+' '+str(atom[2]).lower()


def tree_term(items,join):
    require(items,'Empty generated proof tree')
    if len(items)==1:return items[0]
    middle=len(items)//2
    return join(tree_term(items[:middle],join),tree_term(items[middle:],join))


def cover_term(items):
    return tree_term(items,lambda left,right:'(Cover.append '+left+' '+right+')')


def lookup_source(name,values,*,result_type,default,block=16,parameters='',arguments=''):
    """Return a total Nat-indexed table; its used range is separately proved."""
    require(values,'Empty generated lookup')
    lines=[];leaves=[]
    for start in range(0,len(values),block):
        end=min(start+block,len(values));local=name+'_'+str(start)+'_'+str(end)
        branches='\n'.join('  | '+str(index-start)+' => '+value for index,value in enumerate(values[start:end],start))
        lines.append(f'def {local} {parameters} (index : Nat) : {result_type} :=\n  match index - {start} with\n{branches}\n  | _ => {default}')
        leaves.append((start,end,local))
    def link(parts):
        if len(parts)==1:return parts[0][2]
        middle=len(parts)//2;left,right=link(parts[:middle]),link(parts[middle:])
        local=name+'_range_'+str(parts[0][0])+'_'+str(parts[-1][1])
        lines.append(f'def {local} {parameters} (index : Nat) : {result_type} :=\n  if index < {parts[middle][0]} then {left} {arguments} index else {right} {arguments} index')
        return local
    root=link(leaves)
    lines.append(f'def {name} {parameters} (index : Nat) : {result_type} := {root} {arguments} index')
    return '\n\n'.join(lines)


def header(imports,namespace):
    return '\n'.join('import '+name for name in imports)+f'''

namespace {namespace}
open Pinwheel.Hardware.StreamingMapped Pinwheel.Hardware.StreamingPhysical
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
'''


def network_sources(model,*,prefix,namespace,chunk=256):
    namespace_name(prefix);namespace_name(namespace)
    require(type(chunk) is int and 1<=chunk<=512,'Unsupported physical proof chunk size')
    nodes,base=model['nodes'],len(model['labels']);modules={};chunks=[]
    for start in range(0,len(nodes),chunk):
        name=prefix+'Nodes'+str(start//chunk);chunks.append(name)
        lines=[header(['Pinwheel.Hardware.StreamingPhysical.Network'],namespace)]
        for index,node in enumerate(nodes[start:start+chunk],start):
            arity=len(node['sources']);sources=node['sources']
            function=('fun _ => 0' if not arity else 'fun pin => match pin.val with '+
                ' '.join('| '+str(k)+' => '+str(source) for k,source in enumerate(sources[:-1]))+
                ' | _ => '+str(sources[-1]))
            lines.append(f'def node{index} : Node :=\n  ⟨{arity}, {function}, {lean_expression(node["expression"],tuple("p"+str(k) for k in range(arity)))}⟩')
        lines += ['end '+namespace,''];modules[name]='\n\n'.join(lines)
    lookup=prefix+'Lookup'
    lines=[header(chunks+['Pinwheel.Hardware.StreamingPhysical.Network','Pinwheel.Hardware.StreamingPhysical.Cover'],namespace)]
    if nodes:lines += [lookup_source('lookup',[f'node{index}' for index in range(len(nodes))],result_type='Node',default='⟨0,fun _ => 0,.constant false⟩')]
    else:lines += ['def lookup (_ : Nat) : Node := ⟨0,fun _ => 0,.constant false⟩']
    lines += [f'def safeAt (index : Nat) : Prop := (lookup index).Safe ({base} + index)','end '+namespace,'']
    modules[lookup]='\n\n'.join(lines);covers=[]
    for start in range(0,len(nodes),chunk):
        end=min(start+chunk,len(nodes));name=prefix+'Order'+str(start//chunk);covers.append((name,start,end))
        lines=[header([lookup],namespace)]
        for index in range(start,end):lines.append(f'theorem safe{index} : safeAt {index} := by unfold safeAt Node.Safe; decide +kernel')
        lines += [f'theorem cover{start} : Cover safeAt {start} {end-start} :=\n  '+
            cover_term([f'(Cover.single safe{index})' for index in range(start,end)]),'end '+namespace,'']
        modules[name]='\n\n'.join(lines)
    name=prefix+'Network';lines=[header([item[0] for item in covers] or [lookup],namespace)]
    if nodes:
        lines += [f'theorem allOrdered : Cover safeAt 0 {len(nodes)} :=\n  '+cover_term([f'cover{start}' for _,start,_ in covers]),
            f'def network : Network where\n  inputs := {base}\n  nodes := {len(nodes)}\n  node := fun index => lookup index.val\n  ordered := fun index => allOrdered.get index.val (Nat.zero_le _) index.isLt']
    else:
        lines += [f'def network : Network where\n  inputs := {base}\n  nodes := 0\n  node := Fin.elim0\n  ordered := fun index => Fin.elim0 index']
    lines += ['end '+namespace,''];modules[name]='\n\n'.join(lines)
    return modules,dict(module=name,namespace=namespace,nodes=len(nodes),inputs=base)


def term_source(node):
    kind=node[0]
    if kind=='constant':return '.constant '+str(node[1]).lower()
    if kind=='variable':return '.variable '+node[1][1:]
    if kind=='not':return '.inv ('+term_source(node[1])+')'
    require(kind in ('*','+','^'),'Unknown physical term operator')
    return '.'+{'*':'conj','+':'disj','^':'xor'}[kind]+' ('+term_source(node[1])+') ('+term_source(node[2])+')'

def contraction_sources(model,plan,reference,actual,*,prefix,namespace,chunk=256):
    namespace_name(prefix);namespace_name(namespace)
    require(len(model['nodes'])==len(plan['rules']) and len(plan['image'])==len(model['labels'])+len(model['nodes']),
        'Physical rule/image inventory mismatch')
    base=len(model['labels']);modules={};patterns={};records=[]
    for rule in plan['rules']:
        names=tuple(sorted(support(rule['actual'])|support(rule['expected']),key=lambda name:int(name[1:])))
        local={name:('variable','v'+str(index)) for index,name in enumerate(names)}
        key=(substitute(rule['actual'],local),substitute(rule['expected'],local),len(names))
        if key not in patterns:patterns[key]=len(patterns)
        records.append((patterns[key],names))
    pattern_module=prefix+'Patterns';lines=[header(['Pinwheel.Hardware.StreamingPhysical.Local'],namespace)]
    for (left,right,count),index in patterns.items():
        local={'v'+str(k):'v'+str(k) for k in range(count)}
        params=' '.join('(v'+str(k)+' : Bool)' for k in range(count))
        lines += [f'theorem pattern{index} {params} : {lean_bool(left,local)} = {lean_bool(right,local)} := by decide +kernel +revert']
    lines += ['end '+namespace,''];modules[pattern_module]='\n\n'.join(lines)
    image_module=prefix+'Image';lines=[header([pattern_module,reference['module'],actual['module']],namespace),
        lookup_source('imageTail',[atom_source(atom) for atom in plan['image'][base:]],result_type='Atom',default='.constant false')
            if model['nodes'] else 'def imageTail (_ : Nat) : Atom := .constant false',
        f'def image (wire : Nat) : Atom :=\n  if wire < {base} then .wire wire false else imageTail (wire - {base})',
        f'def ruleAt (index : Nat) : Prop := ∀ bound : index < {actual["namespace"]}.network.nodes,\n  NodeRule {reference["namespace"]}.network {actual["namespace"]}.network image ⟨index,bound⟩',
        'end '+namespace,'']
    modules[image_module]='\n\n'.join(lines);covers=[]
    for start in range(0,len(model['nodes']),chunk):
        end=min(start+chunk,len(model['nodes']));name=prefix+'Rules'+str(start//chunk);covers.append((name,start))
        lines=[header([image_module],namespace)]
        for index in range(start,end):
            rule=plan['rules'][index];pattern,names=records[index]
            term='pattern'+str(pattern)+' '+ ' '.join('(values '+name[1:]+')' for name in names)
            values={name:'(values '+name[1:]+')' for name in names}
            goal=lean_bool(rule['actual'],values)+' = '+lean_bool(rule['expected'],values)
            lines += [f'def actualTerm{index} : Term := '+term_source(rule['actual']),
                f'theorem connected{index} : ({actual["namespace"]}.network.node ⟨{index},by decide⟩).term image = actualTerm{index} := by decide +kernel']
            if rule['kind']=='transport':
                right=atom_source(plan['image'][base+index])
                lines += [f'theorem output{index} : image ({actual["namespace"]}.network.inputs + {index}) = {right} := by decide +kernel']
                body='  intro bound\n  exact NodeRule.transport_local actualTerm'+str(index)+' ('+right+') connected'+str(index)+' output'+str(index)+' (fun values => by\n    change '+goal+'\n    exact '+term+')'
            else:
                selected=rule['selected']
                lines += [f'def referenceTerm{index} : Term := '+term_source(rule['expected']),
                    f'theorem referenceCell{index} : ({reference["namespace"]}.network.node ⟨{selected},by decide⟩).term (fun wire => .wire wire false) = referenceTerm{index} := by decide +kernel',
                    f'theorem output{index} : image ({actual["namespace"]}.network.inputs + {index}) = .wire ({reference["namespace"]}.network.inputs + {selected}) false := by decide +kernel']
                body='  intro bound\n  exact NodeRule.cell_local ⟨'+str(selected)+',by decide⟩ actualTerm'+str(index)+' referenceTerm'+str(index)+' connected'+str(index)+' referenceCell'+str(index)+' output'+str(index)+' (fun values => by\n    change '+goal+'\n    exact '+term+')'
            lines.append(f'theorem rule{index} : ruleAt {index} := by\n{body}')
        lines += [f'theorem rules{start} : Cover ruleAt {start} {end-start} :=\n  '+
            cover_term([f'(Cover.single rule{index})' for index in range(start,end)]),'end '+namespace,'']
        modules[name]='\n\n'.join(lines)
    name=prefix+'Proof';lines=[header([item[0] for item in covers] or [image_module],namespace)]
    if model['nodes']:
        lines += [f'theorem allRules : Cover ruleAt 0 {len(model["nodes"])} :=\n  '+cover_term([f'rules{start}' for _,start in covers])]
        node='fun index => allRules.get index.val (Nat.zero_le _) index.isLt index.isLt'
    else:node='fun index => Fin.elim0 index'
    lines += [f'def contraction : Contraction {reference["namespace"]}.network {actual["namespace"]}.network where',
        '  sameInputs := rfl','  image := image',
        '  input := by intro wire bound; exact if_pos bound',
        '  node := '+node,'end '+namespace,''];modules[name]='\n\n'.join(lines)
    return modules,dict(module=name,namespace=namespace,patterns=len(patterns),rules=len(model['nodes']))


def device_sources(model,network,*,prefix,namespace):
    """Explicit all-D and all-output roots in the same full-state bit basis."""
    from streaming_tt_finite import finite_forall
    registers=len(model['next']);inputs=len(model['labels'])-registers
    require(inputs>=0 and registers>0,'Missing physical device state basis')
    require(tuple(label[1] for label in model['labels'][inputs:])==tuple(model['next']),
        'Device D order differs from its Q input basis')
    outputs=[(port,index,atom) for port,atoms in model['outputs'].items() for index,atom in enumerate(atoms)]
    name=prefix+'Device';lines=[header([network['module'],'Pinwheel.Hardware.StreamingPhysical.Device'],namespace),
        lookup_source('nextTable',[atom_source(atom) for atom in model['next'].values()],result_type='Atom',default='.constant false'),
        lookup_source('outputTable',[atom_source(atom) for _,_,atom in outputs],result_type='Atom',default='.constant false'),
        finite_forall('nextBound', registers, lambda index:
            f'(nextTable {index}.val).Bounded ({network["namespace"]}.network.inputs + {network["namespace"]}.network.nodes)'),
        finite_forall('outputBound', len(outputs), lambda index:
            f'(outputTable {index}.val).Bounded ({network["namespace"]}.network.inputs + {network["namespace"]}.network.nodes)'),
        f'def device : Device {inputs} {registers} {len(outputs)} where',
        f'  network := {network["namespace"]}.network','  dimensions := rfl',
        '  next := fun index => nextTable index.val','  output := fun index => outputTable index.val',
        '  nextBound := nextBound','  outputBound := outputBound','end '+namespace,'']
    return {name:'\n\n'.join(lines)},dict(module=name,namespace=namespace,inputs=inputs,
        registers=registers,outputs=tuple((port,index) for port,index,_ in outputs))


def correspondence_sources(reference,actual,contraction,*,module,namespace):
    from streaming_tt_finite import finite_forall
    require((reference['inputs'],reference['registers'],reference['outputs'])==
        (actual['inputs'],actual['registers'],actual['outputs']),'Device endpoint interfaces differ')
    r=reference['namespace'];a=actual['namespace'];c=contraction['namespace']
    lines=[header([reference['module'],actual['module'],contraction['module']],namespace),
        finite_forall('next', actual['registers'], lambda index:
            f'({a}.device.next {index}).rename {c}.contraction.image = {r}.device.next {index}', chunk_width=64),
        finite_forall('output', len(actual['outputs']), lambda index:
            f'({a}.device.output {index}).rename {c}.contraction.image = {r}.device.output {index}', chunk_width=64),
        f'def correspondence : Device.Correspondence {r}.device {a}.device := ⟨{c}.contraction,next,output⟩',
        f'theorem step_correct (input : Fin {actual["inputs"]} → Bool) (state : Fin {actual["registers"]} → Bool) (index : Fin {actual["registers"]}) :',
        f'    {a}.device.step input state index = {r}.device.step input state index := correspondence.step input state index',
        f'theorem observe_correct (input : Fin {actual["inputs"]} → Bool) (state : Fin {actual["registers"]} → Bool) (index : Fin {len(actual["outputs"])}) :',
        f'    {a}.device.observe input state index = {r}.device.observe input state index := correspondence.observe input state index',
        f'theorem run_correct (state : Fin {actual["registers"]} → Bool) (inputs : List (Fin {actual["inputs"]} → Bool)) :',
        f'    {a}.device.run state inputs = {r}.device.run state inputs := correspondence.run state inputs',
        'end '+namespace,'']
    return {module:'\n\n'.join(lines)}
