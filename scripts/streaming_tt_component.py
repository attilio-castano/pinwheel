"""Actual scalar cells to the already certified typed component functions.

Every gate equation is proved from its interpreted function and connected
sources. Word boundary equalities come from independently reconstructed scalar
leaf values. They are derived lemmas, never certificate assumptions.
"""
import json
from streaming_mapped_certificate import lean_bool,substitute,namespace_name
from streaming_mapped_liberty import require
from streaming_mapped_netlist import expand_hierarchy
from streaming_tt_certificate import parse_graph,data_model
from streaming_tt_hierarchy import trace_hierarchy
from streaming_tt_graph import header,network_sources,lookup_source,term_source,cover_term


def generate(rb,document,library,trace,leaf_values,*,prefix,namespace,chunk=1):
    namespace_name(prefix);namespace_name(namespace)
    top=rb.TOP;body=document['modules'][top]
    flat=expand_hierarchy(document,top,library)['modules'][top]
    hierarchy=trace_hierarchy(document,top,library)
    graph=parse_graph(document,top,library)
    positions={}
    state_order=[]
    for name,(width,ctor) in rb.REGISTERS.items():
        bits=flat['netnames'][name]['bits']
        require(len(bits)==width and all(type(wire) is int for wire in bits),'Changed actual register metadata')
        for index,wire in enumerate(bits):
            require(wire not in positions,'Physical state metadata aliases a Q')
            label=name+':'+str(index);positions[wire]=label;state_order.append(label)
    state_labels={ff.name:positions[ff.q] for ff in graph.flipflops}
    model=data_model(graph,state_labels=state_labels,state_order=tuple(state_order))
    # The same explicit wire index table is independently reconstructed here.
    wire_indices={}
    for index,label in enumerate(model['labels']):
        if label[0]=='input':wire_indices[graph.inputs[label[1]][label[2]]]=index
    label_ff={state_labels[ff.name]:ff for ff in graph.flipflops}
    for index,label in enumerate(model['labels']):
        if label[0]=='state':wire_indices[label_ff[label[1]].q]=index
    for index,gate in enumerate(graph.gates):wire_indices[gate.output]=len(model['labels'])+index
    require(len(graph.gates)==len(model['nodes']),'Unexpected component clock logic')
    def root(wire):
        return ('constant',wire=='1') if type(wire) is str else ('wire',wire_indices[wire],False)
    def atom_value(atom,function='assignment'):
        if atom[0]=='constant':return str(atom[1]).lower()
        require(not atom[2],'Unexpected inversion outside actual physical gates')
        return f'({function} i s {atom[1]})'
    parameters=f'(i : Values {rb.INPUT_TYPE}) (s : Values {rb.REGISTER_TYPE})'
    old=trace['namespace'];old_proof=trace['proof_module']
    modules,network=network_sources(model,prefix=prefix,namespace=namespace)
    require(len(trace['cells'])>0,'No actual source-bound word instances')
    primary_values=[];primary_descriptors=[];fields=[];field_indices={}
    for kind,interface,variable in [('input',rb.INPUTS,'i'),('state',rb.REGISTERS,'s')]:
        for field,(_,ctor) in interface.items():
            field_indices[kind,field]=len(fields);fields.append(f'({variable} ({ctor}))')
    for label in model['labels']:
        if label[0]=='input':
            primary_values.append(f'(i ({rb.INPUTS[label[1]][1]})).getLsbD {label[2]}')
            primary_descriptors.append((field_indices['input',label[1]],label[2]))
        else:
            name,index=label[1].rsplit(':',1)
            primary_values.append(f'(s ({rb.REGISTERS[name][1]})).getLsbD {index}')
            primary_descriptors.append((field_indices['state',name],int(index)))
    owners={}
    for name,(width,ctor) in rb.INPUTS.items():
        for index,wire in enumerate(body['ports'][name]['bits']):
            owners[wire]=dict(value=f'(i ({ctor}))',bit=index,width=width,source=None,
                root=root(hierarchy[()]['ports'][name][index]))
    for name,(width,ctor) in rb.REGISTERS.items():
        for index,wire in enumerate(body['netnames'][name]['bits']):
            owners[wire]=dict(value=f'(s ({ctor}))',bit=index,width=width,source=None,
                root=root(hierarchy[()]['local'][wire]))
    def bundle(bits):
        parts=[];at=0
        while at<len(bits):
            start=at;wire=bits[at]
            if type(wire) is str:
                while at<len(bits) and type(bits[at]) is str:at+=1
                require(all(value in ('0','1') for value in bits[start:at]),'Functional X/Z in source word port')
                parts.append(f'{int("".join(reversed(bits[start:at])),2)}#{at-start}')
            else:
                require(wire in owners,'Missing previous actual word source')
                owner=owners[wire];at+=1
                while at<len(bits) and type(bits[at]) is int and bits[at] in owners and \
                        owners[bits[at]]['value']==owner['value'] and owners[bits[at]]['bit']==owner['bit']+at-start:at+=1
                parts.append(owner['value'] if owner['bit']==0 and at-start==owner['width'] else
                    f'({owner["value"]}).extractLsb\' {owner["bit"]} {at-start}')
        result=parts[-1]
        for part in reversed(parts[:-1]):result=f'({result}) ++ ({part})'
        return result
    node_indices={node['name']:index for index,node in enumerate(model['nodes'])}
    assigned={};records=[];imports={old_proof}
    for ordinal,item in enumerate(trace['cells']):
        require(item['ordinal']==ordinal and item['source_cell'] in body['cells'],'Changed actual word-cell order')
        cell=body['cells'][item['source_cell']]
        require(cell['type']==item['mapped_module'] and cell['connections']==item['connections'],
            'Source-bound word trace differs from actual component')
        local=leaf_values[item['mapped_module']];imports.add(local['module'])
        ports=local['ports'];args={pin:bundle(cell['connections'][pin]) for pin in ports}
        arguments=' '.join('('+args[pin]+')' for pin in ports)
        actual_ports=hierarchy[(item['source_cell'],)]['ports']
        inputs=[]
        for pin in ports:
            for index,wire in enumerate(cell['connections'][pin]):
                actual_root=root(actual_ports[pin][index]);source=owners.get(wire)
                if type(wire) is str:
                    require(actual_root==('constant',wire=='1'),'Hierarchy changed a word literal')
                else:require(source is not None and source['root']==actual_root,'Hierarchy word input alias differs')
                inputs.append(dict(pin=pin,bit=index,root=actual_root,source=source,
                    name=f'pin_{ordinal}_{pin}_{index}',argument=args[pin]))
        gates=[]
        for local_index,node in enumerate(local['nodes']):
            full=json.dumps((item['source_cell'],*json.loads(node['name'])),separators=(',',':'))
            require(full in node_indices,'Actual local primitive absent from component graph')
            index=node_indices[full]
            require(index not in assigned,'Actual gate belongs to multiple word leaves')
            assigned[index]=f'{local["namespace"]}.value{local_index} {arguments}'
            gates.append(dict(index=index,local=local_index))
        outputs=[]
        for index,(wire,local_root) in enumerate(zip(cell['connections']['Y'],local['outputs']['Y'])):
            actual_root=root(actual_ports['Y'][index]);source=None
            if local_root[0]=='wire' and local_root[1]<len(local['labels']):
                _,pin,bit=local['labels'][local_root[1]]
                source=next(value for value in inputs if value['pin']==pin and value['bit']==bit)
            elif local_root[0]=='constant':require(actual_root==local_root,'Changed constant word output')
            outputs.append(dict(index=index,root=actual_root,local_root=local_root,input=source,
                name=f'output_{ordinal}_{index}'))
            require(type(wire) is int and wire not in owners,'Source word output aliases an existing logical source')
            owners[wire]=dict(value=f'({old}.cell{ordinal} i s)',bit=index,width=len(cell['connections']['Y']),
                source=f'output_{ordinal}_{index}',root=actual_root)
        records.append(dict(ordinal=ordinal,args=args,arguments=arguments,local=local,
            inputs=inputs,gates=gates,outputs=outputs))
    require(set(assigned)==set(range(len(model['nodes']))),'Actual component primitive inventory is not exactly covered')
    base=len(model['labels']);assignment_module=prefix+'Assignment'
    lines=[header([network['module'],'Pinwheel.Hardware.StreamingPhysical.Local',*sorted(imports)],namespace),
        'open Pinwheel.Hardware',
        f'def inputRead {parameters} (field bit : Nat) : Bool :=\n  match field with\n'+
            '\n'.join(f'  | {index} => {value}.getLsbD bit' for index,value in enumerate(fields))+'\n  | _ => false',
        '\n\n'.join(f'theorem input_read_field{index} {parameters} (bit : Nat) :\n'
            f'    inputRead i s {index} bit = {value}.getLsbD bit := by rfl'
            for index,value in enumerate(fields)),
        lookup_source('inputDescriptor',[f'({field},{bit})' for field,bit in primary_descriptors],
            result_type='Nat × Nat',default='(0,0)'),
        f'def inputValues {parameters} (index : Nat) : Bool :=\n'
            '  inputRead i s (inputDescriptor index).1 (inputDescriptor index).2',
        lookup_source('assignmentTail',[assigned[index] for index in range(len(model['nodes']))],
            result_type='Bool',default='false',parameters=parameters,arguments='i s'),
        f'def assignment {parameters} (wire : Nat) : Bool := if wire < {base} then inputValues i s wire else assignmentTail i s (wire - {base})',
        f'def cellAt {parameters} (index : Nat) : Prop := ∀ bound : index < network.nodes,\n  assignment i s (network.inputs + index) =\n    (network.node ⟨index,bound⟩).expression.eval (fun pin => assignment i s ((network.node ⟨index,bound⟩).source pin))',
        'end '+namespace,'']
    modules[assignment_module]='\n\n'.join(lines);previous=assignment_module;point_modules=[]
    for start in range(0,len(primary_values),128):
        name=prefix+'Primary'+str(start//128)
        lines=[header([previous],namespace),'open Pinwheel.Hardware']
        for index in range(start,min(start+128,len(primary_values))):
            field,bit=primary_descriptors[index]
            lines += [f'theorem input_point{index} {parameters} : inputValues i s {index} = {primary_values[index]} :=',
                f'  (congrArg (fun slot : Nat × Nat => inputRead i s slot.1 slot.2)',
                f'    (by decide +kernel : inputDescriptor {index} = ({field},{bit}))).trans',
                f'    (input_read_field{field} i s {bit})']
        lines += ['end '+namespace,''];modules[name]='\n\n'.join(lines);previous=name
    primary_module=previous
    simplify='simp only [BitVec.getLsbD_extractLsb\',BitVec.getLsbD_append]'
    for start in range(0,len(records),chunk):
        name=prefix+'Cells'+str(start//chunk);point_modules.append(name)
        lines=[header([previous],namespace),'open Pinwheel.Hardware']
        for record in records[start:start+chunk]:
            ordinal=record['ordinal'];local=record['local'];arguments=record['arguments']
            for pin in record['inputs']:
                statement=f'{atom_value(pin["root"])} = ({pin["argument"]}).getLsbD {pin["bit"]}'
                source=pin['source'];proof='rfl' if source is None or source['source'] is None else source['source']+' i s'
                rules=[]
                if "extractLsb'" in pin['argument']:rules.append("BitVec.getLsbD_extractLsb'")
                if '++' in pin['argument']:rules.append('BitVec.getLsbD_append')
                normal=('simp only ['+','.join(rules)+']; ' if rules else '')
                if source is not None and source['source'] is None and pin['root'][0]=='wire':
                    # Select the literal descriptor before interpreting a wide
                    # word. The field lemma was checked at a variable bit, so
                    # kernel conversion never expands a large concrete bit.
                    wire=pin['root'][1]
                    require(wire<base,'A source register/input is outside the primary basis')
                    body=(f'  have selected : assignment i s {wire} = ({source["value"]}).getLsbD {source["bit"]} := by\n'
                        f'    unfold assignment\n    rw [if_pos (by decide : {wire} < {base})]\n'
                        f'    exact input_point{wire} i s\n'
                        f'  exact selected.trans (by '+normal+'all_goals rfl)')
                elif source is None or source['source'] is None:
                    body='  '+normal+'rfl'
                else:body=f'  exact ({proof}).trans (by '+normal+'rfl)'
                lines.append(f'theorem {pin["name"]} {parameters} : {statement} := by\n{body}')
            for gate in record['gates']:
                index=gate['index'];wire=base+index;start=index//16*16;end=min(start+16,len(model['nodes']))
                lines += [f'theorem assignment_gate{index} {parameters} : assignment i s {wire} = {assigned[index]} := by',
                    '  unfold assignment',f'  rw [if_neg (by decide : ¬ {wire} < {base})]',
                    f'  change assignmentTail_{start}_{end} i s {index} = _','  rfl']
            for output in record['outputs']:
                index=output['index'];goal=f'{atom_value(output["root"])} = ({old}.cell{ordinal} i s).getLsbD {index}'
                if output['input'] is not None:
                    body=f'  exact ({output["input"]["name"]} i s).trans ({local["namespace"]}.output{index} {arguments})'
                else:
                    body=''
                    if output['root'][0]=='wire':
                        gate_index=output['root'][1]-base
                        require(gate_index in assigned,'Actual word output lacks a complete gate assignment')
                        body=f'  rw [assignment_gate{gate_index} i s]\n'
                    body+=f'  change _ = ({local["previous"]["namespace"]}.actual {arguments}).getLsbD {index}\n  exact {local["namespace"]}.output{index} {arguments}'
                lines.append(f'theorem {output["name"]} {parameters} : {goal} := by\n{body}')
            for gate in record['gates']:
                index=gate['index'];node=model['nodes'][index]
                term=term_source(substitute(node['expression'],{'p'+str(k):('variable','w'+str(wire))
                    for k,wire in enumerate(node['sources'])}))
                formula=lean_bool(node['expression'],{'p'+str(k):f'(assignment i s {wire})'
                    for k,wire in enumerate(node['sources'])})
                rewrites=[];rewritten_arguments=set()
                local_primary={local['labels'][source][1:] for source in local['nodes'][gate['local']]['sources']
                    if source<len(local['labels'])}
                for pin in record['inputs']:
                    argument=(pin['argument'],pin['bit'])
                    if (pin['pin'],pin['bit']) in local_primary and argument not in rewritten_arguments:
                        # Rewrite each consumed typed argument back to its actual
                        # source root. Distinct typed bits may share one real
                        # wire; selecting a representative bit is insufficient.
                        rewrites.append(pin['name']);rewritten_arguments.add(argument)
                body=f'  intro bound\n  exact Node.connected_value _ term{index} (assignment i s) _ connected{index} (by\n    change assignment i s {base+index} = term{index}.eval (assignment i s)\n    rw [assignment_gate{index} i s]\n    change {local["namespace"]}.value{gate["local"]} {arguments} = {formula}\n'
                body+='    unfold '+local['namespace']+'.value'+str(gate['local'])+'\n'
                if rewrites:body+='    conv =>\n      lhs\n      simp only ['+','.join('← '+value+' i s' for value in rewrites)+']\n'
                body+='    all_goals rfl)'
                lines += [f'def term{index} : Term := {term}',
                    f'theorem connected{index} : (network.node ⟨{index},by decide⟩).term (fun wire => .wire wire false) = term{index} := by decide +kernel',
                    f'theorem cell{index} {parameters} : cellAt i s {index} := by\n{body}']
        lines += ['end '+namespace,''];modules[name]='\n\n'.join(lines);previous=name
    name=prefix+'Realizes';lines=[header([previous],namespace),'open Pinwheel.Hardware',
        f'theorem allCells {parameters} : Cover (cellAt i s) 0 {len(model["nodes"])} :=\n  '+
            cover_term([f'(Cover.single (cell{index} i s))' for index in range(len(model['nodes']))]),
        f'theorem realizes {parameters} : network.Realizes (inputValues i s) (assignment i s) where',
        '  input := by intro wire bound; exact if_pos bound',
        '  node := fun index => (allCells i s).get index.val (Nat.zero_le _) index.isLt index.isLt',
        f'theorem computed {parameters} (wire : Nat) (bound : wire < network.inputs + network.nodes) :',
        '    network.value (inputValues i s) wire = assignment i s wire :=',
        '  (Network.Realizes.unique network _ _ (realizes i s) wire bound).symm',
        'end '+namespace,''];modules[name]='\n\n'.join(lines)
    return modules,dict(network,assignment_module=assignment_module,primary_module=primary_module,realizes_module=name,namespace=namespace,model=model,
        owners=owners,hierarchy=hierarchy,source_proof=old_proof,source_namespace=old)


def endpoint_sources(rb,document,library,metadata,*,prefix):
    """All connected D/public-output roots, then full typed step/observe."""
    namespace=metadata['namespace'];old=metadata['source_namespace'];model=metadata['model']
    body=document['modules'][rb.TOP];top_map=metadata['hierarchy'][()]['local'];owners=metadata['owners']
    d_by_q={}
    for cell in body['cells'].values():
        if cell['type'] in library.cells and library.cells[cell['type']].sequential:
            require(len(cell['connections']['Q'])==len(cell['connections']['D'])==1,'Resized actual FF')
            q,d=cell['connections']['Q'][0],cell['connections']['D'][0]
            require(q not in d_by_q,'Aliased original FF')
            d_by_q[q]=d
    parameters=f'(i : Values {rb.INPUT_TYPE}) (s : Values {rb.REGISTER_TYPE})'
    def atom_value(atom,values):
        return str(atom[1]).lower() if atom[0]=='constant' else f'({values} {atom[1]})'
    def atom_of_wire(wire):
        if type(wire) is str:return ('constant',wire=='1')
        require(wire in owners,'Actual endpoint has no source-bound owner')
        return owners[wire]['root']
    simplify='simp only [BitVec.getLsbD_extractLsb\',BitVec.getLsbD_append]'
    modules={};previous=metadata['realizes_module']
    endpoints=[]
    for kind,interface,method in [('next',rb.REGISTERS,'step'),('output',rb.OUTPUTS,'observe')]:
        for field,(width,ctor) in interface.items():
            lines=[header([previous],namespace),'open Pinwheel.Hardware']
            wires=([d_by_q[q] for q in body['netnames'][field]['bits']] if kind=='next'
                else body['ports'][field]['bits'])
            atoms=[atom_of_wire(wire) for wire in wires]
            fn=kind+'_'+field
            # Fin width restricts the final fallback to the last actual bit.
            branches=' '.join('| '+str(index)+' => '+__import__('streaming_tt_graph').atom_source(atom)
                for index,atom in enumerate(atoms[:-1]))+' | _ => '+__import__('streaming_tt_graph').atom_source(atoms[-1])
            lines += [f'def roots_{fn} (bit : Fin {width}) : Atom := match bit.val with {branches}',
                f'def {fn} {parameters} : BitVec {width} := Word.pack (fun bit => (roots_{fn} bit).eval (network.value (inputValues i s)))']
            point_names=[]
            for index,(wire,atom) in enumerate(zip(wires,atoms)):
                point=f'point_{fn}_{index}';point_names.append(point)
                goal=f'(roots_{fn} ⟨{index},by decide⟩).eval (network.value (inputValues i s)) = ({old}.{method} i s ({ctor})).getLsbD {index}'
                proof=['  change '+atom_value(atom,'network.value (inputValues i s)')+' = _']
                if atom[0]=='wire' and atom[1]<len(model['labels']):
                    owner=owners[wire];position=atom[1]
                    proof += [f'  rw [Network.value_input network (inputValues i s) {position} (by decide)]',
                        f'  have selected : inputValues i s {position} = ({owner["value"]}).getLsbD {owner["bit"]} := input_point{position} i s',
                        '  exact selected.trans (by',
                        f'    simp only [{old}.{method},BitVec.getLsbD_extractLsb\',BitVec.getLsbD_append]', '    all_goals rfl)']
                elif type(wire) is str:
                    proof += [f'  simp only [{old}.{method},BitVec.getLsbD_extractLsb\',BitVec.getLsbD_append]', '  all_goals rfl']
                elif owners[wire]['source']:
                    if atom[0]=='wire':proof.append(f'  rw [computed i s {atom[1]} (by decide)]')
                    proof += [f'  exact ({owners[wire]["source"]} i s).trans (by',
                        f'    simp only [{old}.{method},BitVec.getLsbD_extractLsb\',BitVec.getLsbD_append]', '    all_goals rfl)']
                else:proof += [f'  simp only [{old}.{method},BitVec.getLsbD_extractLsb\',BitVec.getLsbD_append]','  all_goals rfl']
                lines.append(f'theorem {point} {parameters} : {goal} := by\n'+'\n'.join(proof))
            term='(fun bit => Fin.elim0 bit)'
            for point in reversed(point_names):term=f'(Fin.cases ({point} i s) {term})'
            lines += [f'theorem endpoint_{fn} {parameters} : {fn} i s = {old}.{method} i s ({ctor}) := by',
                '  apply Word.from_bits','  intro index within',f'  rw [{fn},Word.pack_bit _ index within]',
                f'  have all : ∀ bit : Fin {width}, (roots_{fn} bit).eval (network.value (inputValues i s)) =',
                f'      ({old}.{method} i s ({ctor})).getLsbD bit.val := {term}',
                '  exact all ⟨index,within⟩']
            endpoints.append((kind,field,width,ctor))
            name=prefix+'Endpoint_'+fn
            lines += ['end '+namespace,''];modules[name]='\n\n'.join(lines);previous=name
    lines=[header([previous],namespace),'open Pinwheel.Hardware']
    for kind,interface,method,result in [('next',rb.REGISTERS,'step',rb.REGISTER_TYPE),('output',rb.OUTPUTS,'observe',rb.OUTPUT_TYPE)]:
        lines.append(f'def {method} {parameters} : Values {result}')
        consumed=set()
        if kind=='next':
            for family,ctor,count,_ in rb.FAMILIES:
                values=', '.join(f'(next_r_{family}{index} i s)' for index in range(count))
                lines.append(f'  | _, .{ctor} address => (#[{values}])[address.toNat]\'(by exact address.isLt)')
                consumed.update('r_'+family+str(index) for index in range(count))
        for field,(_,ctor) in interface.items():
            if field not in consumed:lines.append(f'  | _, {ctor} => {kind}_{field} i s')
    # The proof splits only the real typed register/port constructors.
    for kind,interface,method,ty in [('next',rb.REGISTERS,'step',rb.REGISTER_TYPE),('output',rb.OUTPUTS,'observe',rb.OUTPUT_TYPE)]:
        lines += [f'theorem {method}_correct {parameters} (field : {ty} width) :',
            f'    {method} i s field = {old}.{method} i s field := by','  cases field with']
        consumed=set()
        if kind=='next':
            for family,ctor,count,_ in rb.FAMILIES:
                term='(fun index => Fin.elim0 index)'
                for index in reversed(range(count)):term=f'(Fin.cases (endpoint_next_r_{family}{index} i s) {term})'
                lines += [f'  | {ctor} address =>',
                    f'    have all : ∀ index : Fin {count}, step i s (.{ctor} (BitVec.ofFin index)) =',
                    f'        {old}.step i s (.{ctor} (BitVec.ofFin index)) := {term}',
                    '    exact all address.toFin']
                consumed.update('r_'+family+str(index) for index in range(count))
        nested=[]
        for field,(_,ctor) in interface.items():
            if field in consumed:continue
            tokens=ctor.replace('(','').replace(')','').split()
            if len(tokens)>1:nested.append((field,tokens));continue
            name=tokens[0][1:];name='«initialize»' if name=='initialize' else name
            lines.append(f'  | {name} => exact endpoint_{kind}_{field} i s')
        if nested:
            require(all(tokens[0]=='.core' and len(tokens)==2 for _,tokens in nested),'Unexpected nested output type')
            lines += ['  | core field =>','    cases field with']
            for field,tokens in nested:
                name=tokens[1][1:];name='«initialize»' if name=='initialize' else name
                lines.append(f'    | {name} => exact endpoint_{kind}_{field} i s')
    lines += ['end '+namespace,'']
    modules[prefix+'Proof']='\n\n'.join(lines)
    return modules
