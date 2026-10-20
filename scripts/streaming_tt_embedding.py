"""Certified embedding of actual component cells in the actual full device.

Names select candidate pin correspondences. Every complete child gate function,
connected source, and output image is then checked by the generated kernel rule.
No component endpoint or execution agreement is a certificate premise.
"""
import json
from streaming_mapped_liberty import require
from streaming_mapped_certificate import substitute
from streaming_tt_certificate import atom_expression, expression_signature, normalized_expression
from streaming_tt_graph import contraction_sources, lookup_source, atom_source


def wire_indices(graph, model, state_wires):
    """Recover the exact full-state data-model indexing from actual connected Qs."""
    result={}
    for index,label in enumerate(model['labels']):
        wire=graph.inputs[label[1]][label[2]] if label[0]=='input' else state_wires[label[1]]
        require(wire not in result,'Aliased parent input/state position')
        result[wire]=index
    gates={gate.name:gate for gate in graph.gates}
    for index,node in enumerate(model['nodes']):
        gate=gates[node['name']]
        require(gate.output not in result,'Aliased actual parent gate result')
        result[gate.output]=len(model['labels'])+index
    return result


def component_plan(parent_model,child_model,parent_wires,parent_hierarchy,child_body,component_path):
    require(component_path in parent_hierarchy,'Missing actual component hierarchy')
    local=parent_hierarchy[component_path];image=[]
    def parent_atom(wire):
        if type(wire) is str:
            require(wire in ('0','1'),'Functional X/Z in embedding')
            return ('constant',wire=='1')
        require(wire in parent_wires,'Component pin absent from actual parent data graph')
        return ('wire',parent_wires[wire],False)
    for label in child_model['labels']:
        if label[0]=='input':wire=local['ports'][label[1]][label[2]]
        else:
            name,index=label[1].rsplit(':',1);wire=local['local'][child_body['netnames'][name]['bits'][int(index)]]
        image.append(parent_atom(wire))
    parent_nodes={node['name']:index for index,node in enumerate(parent_model['nodes'])};rules=[]
    for node in child_model['nodes']:
        name=json.dumps((*component_path,*json.loads(node['name'])),separators=(',',':'))
        require(name in parent_nodes,'Actual child primitive absent from parent inventory')
        selected=parent_nodes[name];target=parent_model['nodes'][selected]
        actual=normalized_expression(node,image)
        expected=substitute(target['expression'],{'p'+str(k):('variable','w'+str(source))
            for k,source in enumerate(target['sources'])})
        require(expression_signature(actual)==expression_signature(expected),'Child/parent connected Boolean cell differs')
        image.append(('wire',len(parent_model['labels'])+selected,False))
        rules.append(dict(kind='cell',selected=selected,actual=actual,expected=expected))
    return dict(image=tuple(image),rules=tuple(rules),parent_ports={pin:tuple(parent_atom(wire) for wire in bits)
        for pin,bits in local['ports'].items() if pin!='clk'},clock_port=local['ports'].get('clk'),
        component_path=component_path)


def generate(child_model,plan,parent,child,*,prefix,namespace,chunk=256):
    """Reuse local cell truth proofs, without the contraction's equal-input law."""
    modules,metadata=contraction_sources(child_model,plan,parent,child,prefix=prefix,namespace=namespace,chunk=chunk)
    name=prefix+'Image';source=modules[name];base=len(child_model['labels'])
    needle=f'def image (wire : Nat) : Atom :=\n  if wire < {base} then .wire wire false else imageTail (wire - {base})'
    require(needle in source,'Changed checked rule generator image layout')
    primary=lookup_source('imageInput',[atom_source(atom) for atom in plan['image'][:base]],result_type='Atom',default='.constant false')
    source=source.replace(needle,primary+'\n\n'+needle.replace('.wire wire false','imageInput wire'))
    modules[name]=source
    name=prefix+'Proof';source=modules[name];source='import Pinwheel.Hardware.StreamingPhysical.Embedding\n'+source
    source=source.replace(f'def contraction : Contraction {parent["namespace"]}.network {child["namespace"]}.network where',
        f'def embedding : Embedding {parent["namespace"]}.network {child["namespace"]}.network where')
    source=source.replace('  sameInputs := rfl\n','').replace('  input := by intro wire bound; exact if_pos bound\n','')
    require('def embedding :' in source and 'def contraction :' not in source,'Changed checked rule generator proof layout')
    modules[name]=source
    return modules,{**metadata,'image_module':prefix+'Image','parent_ports':plan['parent_ports'],'component_path':plan['component_path']}


def input_sources(rb,child_model,plan,embedding,child,*,prefix,chunk=128):
    """Decode actual parent pin images and prove the entire child input basis."""
    from streaming_tt_graph import header,cover_term
    namespace=embedding['namespace'];module=prefix+'InputViews';label_index={label:index for index,label in enumerate(child_model['labels'])}
    lines=[header([embedding.get('image_module',embedding['module']),
        'Pinwheel.Hardware.StreamingMapped.Word',
        'Pinwheel.Hardware.StreamingPhysical.Input','Pinwheel.Hardware.StreamingReady.Package'],namespace),'open Pinwheel.Hardware']
    field_views={};port_metadata={}
    for kind,interface in [('input',rb.INPUTS),('state',rb.REGISTERS)]:
        for field,(width,ctor) in interface.items():
            indices=[label_index[('input',field,index)] if kind=='input' else label_index[('state',field+':'+str(index))] for index in range(width)]
            name='read_'+kind+'_'+field;field_views[kind,field]=name;port_metadata[kind,field]=tuple(plan['image'][index] for index in indices)
            lines += [lookup_source(name+'Root',[atom_source(plan['image'][index]) for index in indices],result_type='Atom',default='.constant false'),
                f'def {name} (values : Nat → Bool) : BitVec {width} := Word.pack (fun bit => ({name}Root bit.val).eval values)']
    for kind,interface,ty,name in [('input',rb.INPUTS,rb.INPUT_TYPE,'readInputs'),('state',rb.REGISTERS,rb.REGISTER_TYPE,'readState')]:
        lines.append(f'def {name} (values : Nat → Bool) : Values {ty}');consumed=set()
        if kind=='state':
            for family,ctor,count,_ in rb.FAMILIES:
                values=', '.join(f'({field_views[kind,"r_"+family+str(index)]} values)' for index in range(count))
                lines.append(f'  | _, .{ctor} address => (#[{values}])[address.toNat]\'(by exact address.isLt)')
                consumed.update('r_'+family+str(index) for index in range(count))
        for field,(_,ctor) in interface.items():
            if field not in consumed:lines.append(f'  | _, {ctor} => {field_views[kind,field]} values')
    for kind,interface,name in [('input',rb.INPUTS,'readInputs'),('state',rb.REGISTERS,'readState')]:
        for field,(_,ctor) in interface.items():
            view=field_views[kind,field]
            lines += [f'theorem {view}_value (values : Nat → Bool) : {name} values ({ctor}) = {view} values := by rfl']
    lines += ['end '+namespace,''];modules={module:'\n\n'.join(lines)};previous=module;covers=[]
    for start in range(0,len(child_model['labels']),chunk):
        end=min(start+chunk,len(child_model['labels']));name=prefix+'InputPoints'+str(start//chunk)
        dependencies=[previous]
        if start==0:dependencies += [embedding['module'],child.get('primary_module',child['assignment_module'])]
        lines=[header(dependencies,namespace),'open Pinwheel.Hardware']
        for index in range(start,end):
            label=child_model['labels'][index]
            if label[0]=='input':kind,field,bit='input',label[1],label[2]
            else:kind='state';field,bit=label[1].rsplit(':',1);bit=int(bit)
            width=rb.INPUTS[field][0] if kind=='input' else rb.REGISTERS[field][0];view=field_views[kind,field]
            lines += [f'theorem point{index} (values : Nat → Bool) : (image {index}).eval values =',
                f'    {child["namespace"]}.inputValues (readInputs values) (readState values) {index} := by',
                f'  rw [{child["namespace"]}.input_point{index}]',
                f'  rw [{view}_value, {view},Word.pack_bit _ {bit} (by decide)]','  rfl']
        lines += [f'theorem points{start} (values : Nat → Bool) : Cover (fun index => (image index).eval values =',
            f'    {child["namespace"]}.inputValues (readInputs values) (readState values) index) {start} {end-start} :=',
            '  '+cover_term([f'(Cover.single (point{index} values))' for index in range(start,end)]),'end '+namespace,'']
        modules[name]='\n\n'.join(lines);previous=name;covers.append(start)
    name=prefix+'Inputs';lines=[header([previous],namespace),
        f'theorem allPoints (values : Nat → Bool) : Cover (fun index => (image index).eval values =',
        f'    {child["namespace"]}.inputValues (readInputs values) (readState values) index) 0 {len(child_model["labels"])} :=',
        '  '+cover_term([f'(points{start} values)' for start in covers]),
        f'theorem input_agreement (values : Nat → Bool) (wire : Nat) (bound : wire < {child["namespace"]}.network.inputs) :',
        f'    (image wire).eval values = {child["namespace"]}.inputValues (readInputs values) (readState values) wire :=',
        '  (allPoints values).get wire (Nat.zero_le _) bound',
        f'theorem atom_read (incoming : Nat → Bool) (root : Atom) (bound : root.Bounded ({child["namespace"]}.network.inputs + {child["namespace"]}.network.nodes)) :',
        f'    (root.rename embedding.image).eval ({embedding["parent_namespace"]}.network.value incoming) =',
        f'    root.eval ({child["namespace"]}.network.value ({child["namespace"]}.inputValues',
        f'      (readInputs ({embedding["parent_namespace"]}.network.value incoming)) (readState ({embedding["parent_namespace"]}.network.value incoming)))) :=',
        '  embedding.atom_input_congr incoming _ (input_agreement _) root bound','end '+namespace,'']
    modules[name]='\n\n'.join(lines)
    return modules,dict(module=name,namespace=namespace,views_module=module,port_metadata=port_metadata)
