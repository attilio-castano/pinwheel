"""Scalar values of actual connected word leaves, joined to prior certificates.

The existing word certificate is used as a theorem about its actual function.
Every internal value below is independently reconstructed from the actual
Liberty function and pin connectivity. Definitional equality checks their join.
No word opcode supplies a value or an equivalence premise.
"""
from streaming_mapped_certificate import lean_bool, namespace_name
from streaming_mapped_liberty import require
from streaming_mapped_netlist import MappedGraph, load_mapped, bit
from streaming_tt_certificate import read_json
from streaming_tt_certificate import combinational_model
from streaming_tt_graph import header,lookup_source,network_sources,term_source,cover_term


def read_leaf(path, top, library):
    """A zero-gate specialized leaf is checked as explicit wires/constants."""
    document=read_json(path)
    require(top in document.get('modules',{}),'Missing actual leaf module')
    body=document['modules'][top]
    if body.get('cells'):
        return load_mapped(path,top,library,combinational=True)
    require(body.get('cells')=={} and not body.get('memories') and not body.get('processes') and
        not body.get('parameter_default_values'),'Unsupported empty-leaf behavior')
    require(not any(body.get('attributes',{}).get(key,'0').strip('0')
        for key in ('blackbox','whitebox')),'Opaque empty leaf')
    inputs,outputs={},{}
    for name,port in body.get('ports',{}).items():
        require(port.get('direction') in ('input','output') and port.get('bits') and
            port.get('upto',0)==0 and port.get('offset',0)==0,'Unsupported empty-leaf port')
        (inputs if port['direction']=='input' else outputs)[name]=tuple(bit(value) for value in port['bits'])
    primary=[wire for wires in inputs.values() for wire in wires]
    require(inputs and outputs and all(type(wire) is int for wire in primary) and
        len(primary)==len(set(primary)),'Empty-leaf primary aliases')
    require(all(type(wire) is str or wire in primary for wires in outputs.values() for wire in wires),
        'Undriven empty-leaf output')
    return MappedGraph(top,library,inputs,outputs,None,(),(),{},0)


def generate(graph, previous, *, module, namespace):
    namespace_name(module);namespace_name(namespace)
    require(set(previous)>={'module','namespace','style'},'Missing source-bound word certificate')
    require(previous['style'] in ('word','bit'),'Unsupported actual word definition shape')
    namespace_name(previous['module']);namespace_name(previous['namespace'])
    model=combinational_model(graph)
    ports=tuple(sorted(graph.inputs));base=len(model['labels'])
    parameters=' '.join(f'({pin} : BitVec {len(graph.inputs[pin])})' for pin in ports)
    arguments=' '.join(ports)
    inputs=[f'{port}.getLsbD {index}' for _,port,index in model['labels']]
    def value(wire):
        if wire<base:return '('+inputs[wire]+')'
        return '(value'+str(wire-base)+' '+arguments+')'
    def atom_value(atom):
        if atom[0]=='constant':return str(atom[1]).lower()
        text=value(atom[1]);return '(!'+text+')' if atom[2] else text
    lines=[header([previous['module'],'Pinwheel.Hardware.StreamingMapped.Word',
        'Pinwheel.Hardware.StreamingPhysical.Network'],namespace)]
    for index,node in enumerate(model['nodes']):
        values={'p'+str(pin):value(source) for pin,source in enumerate(node['sources'])}
        lines.append(f'def value{index} {parameters} : Bool := '+lean_bool(node['expression'],values))
    require(set(model['outputs'])=={'Y'},'Expected actual scalar-leaf Y interface')
    width=len(model['outputs']['Y'])
    if previous['style']=='bit':require(width==1,'Bit-valued prior certificate has wide Y')
    for index,atom in enumerate(model['outputs']['Y']):
        body=(f'  rw [{previous["namespace"]}.actual, Word.pack_bit _ {index} (by decide)]\n  rfl'
            if previous['style']=='word' else
            f'  rw [{previous["namespace"]}.actual, BitVec.getLsbD_ofBool]\n  rfl')
        lines.append(f'theorem output{index} {parameters} :\n  {atom_value(atom)} = ({previous["namespace"]}.actual {arguments}).getLsbD {index} := by\n'+body)
    lines += ['end '+namespace,'']
    metadata=dict(module=module,namespace=namespace,ports=ports,
        port_widths={pin:len(graph.inputs[pin]) for pin in ports},
        labels=model['labels'],nodes=model['nodes'],outputs=model['outputs'],
        actual_gate_names=tuple(node['name'] for node in model['nodes']),
        previous=previous)
    return {module:'\n\n'.join(lines)},metadata


def network_bridge(metadata, *, prefix, namespace=None):
    """Join actual scalar-network evaluation to the certified word function."""
    namespace=metadata['namespace'] if namespace is None else namespace
    model={key:metadata[key] for key in ('labels','nodes','outputs')};model['next']={}
    modules,network=network_sources(model,prefix=prefix,namespace=namespace)
    ports=metadata['ports'];widths=metadata['port_widths'];base=len(model['labels'])
    parameters=' '.join(f'({pin} : BitVec {widths[pin]})' for pin in ports);arguments=' '.join(ports)
    values=[f'{port}.getLsbD {index}' for _,port,index in model['labels']]
    values += [f'value{index} {arguments}' for index in range(len(model['nodes']))]
    name=prefix+'Evaluation';lines=[header([network['module'],metadata['module'],
        'Pinwheel.Hardware.StreamingPhysical.Local'],namespace),
        lookup_source('inputValues',values[:base],result_type='Bool',default='false',parameters=parameters,arguments=arguments),
        (lookup_source('assignmentTail',values[base:],result_type='Bool',default='false',parameters=parameters,arguments=arguments) if values[base:] else f'def assignmentTail {parameters} (_ : Nat) : Bool := false'),
        f'def assignment {parameters} (wire : Nat) : Bool := if wire < {base} then inputValues {arguments} wire else assignmentTail {arguments} (wire - {base})',
        f'def cellAt {parameters} (index : Nat) : Prop := ∀ bound : index < network.nodes,\n  assignment {arguments} (network.inputs + index) =\n    (network.node ⟨index,bound⟩).expression.eval (fun pin => assignment {arguments} ((network.node ⟨index,bound⟩).source pin))']
    for index,node in enumerate(model['nodes']):
        term=term_source(__import__('streaming_mapped_certificate').substitute(node['expression'],
            {'p'+str(k):('variable','w'+str(wire)) for k,wire in enumerate(node['sources'])}))
        lines += [f'def term{index} : Term := {term}',
            f'theorem connected{index} : (network.node ⟨{index},by decide⟩).term (fun wire => .wire wire false) = term{index} := by decide +kernel',
            f'theorem cell{index} {parameters} : cellAt {arguments} {index} := by\n  intro bound\n  exact Node.connected_value _ term{index} (assignment {arguments}) _ connected{index} (by rfl)']
    if model['nodes']:
        lines += [f'theorem allCells {parameters} : Cover (cellAt {arguments}) 0 {len(model["nodes"])} :=\n  '+
            cover_term([f'(Cover.single (cell{index} {arguments}))' for index in range(len(model['nodes']))])]
        node=f'fun index => (allCells {arguments}).get index.val (Nat.zero_le _) index.isLt index.isLt'
    else:node='fun index => Fin.elim0 index'
    # Only the finite input range is required; the two total tables may differ outside it.
    lines += [f'theorem input_eq {parameters} (wire : Nat) (bound : wire < {base}) : assignment {arguments} wire = inputValues {arguments} wire := if_pos bound',
        f'theorem realizes {parameters} : network.Realizes (inputValues {arguments}) (assignment {arguments}) where',
        f'  input := fun wire bound => input_eq {arguments} wire bound',
        '  node := '+node,
        f'theorem computed {parameters} (wire : Nat) (bound : wire < network.inputs + network.nodes) :',
        f'    network.value (inputValues {arguments}) wire = assignment {arguments} wire :=',
        f'  (Network.Realizes.unique network _ _ (realizes {arguments}) wire bound).symm']
    for index,atom in enumerate(model['outputs']['Y']):
        root=(f'Atom.constant {str(atom[1]).lower()}' if atom[0]=='constant' else f'Atom.wire {atom[1]} {str(atom[2]).lower()}')
        previous=metadata['previous']['namespace'];righthand=f'({previous}.actual {arguments}).getLsbD {index}'
        lines += [f'theorem output_value{index} {parameters} : ({root}).eval (network.value (inputValues {arguments})) = {righthand} := by']
        if atom[0]=='constant':lines += [f'  exact output{index} {arguments}']
        else:
            require(not atom[2],'Unexpected inverted physical word root')
            lines += [f'  change network.value (inputValues {arguments}) {atom[1]} = _',
                f'  rw [computed {arguments} {atom[1]} (by decide)]',f'  exact output{index} {arguments}']
    lines += ['end '+namespace,''];modules[name]='\n\n'.join(lines)
    return modules,dict(network,values_module=name,ports=ports,port_widths=widths,
        previous=metadata['previous'],outputs=model['outputs'])
