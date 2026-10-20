"""Kernel source for connecting complete physical state views to typed storage.

All register bits remain arbitrary. Finite root equalities check the actual
selected pin images, rather than taking state or execution agreement as input.
"""
from streaming_mapped_liberty import require
from streaming_tt_graph import header


def state_sources(rb, views, *, component, prefix, packing_module='PhysicalStateCodec',
                  packing_namespace='Pinwheel.Artifact.StreamingPhysicalState',
                  parent_module='PhysicalGRTOriginalNetwork',
                  parent_namespace='Pinwheel.Artifact.StreamingPhysicalGRT.Original',
                  input_count=18, state_count=6039):
    require(component in ('frontend','core'),'Unknown complete state component')
    require(input_count==18 and state_count==6039,'Changed full TT D2 basis')
    ns=views['namespace']; module=prefix+'StateJoin'; packing=packing_namespace+'.packing'
    args=f'(input : Fin {input_count} → Bool) (bits : Fin {state_count} → Bool)'
    values=f'{parent_namespace}.network.value (Device.environment input bits)'
    lines=[header([views['views_module'],packing_module,parent_module,
        'Pinwheel.Hardware.StreamingPhysical.Device'],ns),'open Pinwheel.Hardware',
        f'theorem state_atom {args} (index : Fin {state_count}) :',
        f'    (Atom.wire ({input_count}+index.val) false).eval ({values}) = bits index := by',
        f'  change {parent_namespace}.network.value (Device.environment input bits) ({input_count}+index.val) = bits index',
        '  have indexBound := index.isLt',
        f'  rw [Network.value_input _ _ _ (by change {input_count}+index.val < {input_count+state_count}; omega)]',
        '  rw [Device.environment, dif_neg (by omega), Nat.add_sub_cancel_left, dif_pos index.isLt]']
    endpoints=[]
    for field,(width,ctor) in rb.REGISTERS.items():
        fn='read_state_'+field; target=f'{packing}.decode bits (.{component} ({ctor}))'
        lines += [f'theorem state_root_{field} : ∀ (bit : Fin {width}), {fn}Root bit.val =',
            f'    .wire ({input_count}+({packing}.index ⟨{width},.{component} ({ctor}),bit⟩).val) false := by decide +kernel',
            f'theorem state_field_{field} {args} : {fn} ({values}) = {target} := by',
            '  apply Word.from_bits','  intro index bound',
            f'  rw [{fn}, Word.pack_bit _ index bound, Packing.decode_bit _ _ _ ⟨index,bound⟩]',
            f'  rw [state_root_{field} ⟨index,bound⟩]',
            '  exact state_atom input bits _']
        endpoints.append(field)
    lines += [f'theorem readState_correct {args} :',
        f'    (readState ({values}) : Values {rb.REGISTER_TYPE}) =',
        f'      (fun {{w}} field => {packing}.decode bits (.{component} field)) := by',
        '  funext width field','  cases field with']
    consumed=set()
    for family,ctor,count,_ in rb.FAMILIES:
        term='(fun index => Fin.elim0 index)'
        for index in reversed(range(count)):term=f'(Fin.cases (state_field_r_{family}{index} input bits) {term})'
        lines += [f'  | {ctor} address =>',
            f'    have all : ∀ index : Fin {count}, readState ({values}) (.{ctor} (BitVec.ofFin index)) =',
            f'        {packing}.decode bits (.{component} (.{ctor} (BitVec.ofFin index))) := {term}',
            '    exact all address.toFin']
        consumed.update('r_'+family+str(index) for index in range(count))
    for field,(_,ctor) in rb.REGISTERS.items():
        if field in consumed:continue
        require(ctor.startswith('.') and ' ' not in ctor,'Unexpected scalar register constructor')
        name=ctor[1:];name='«initialize»' if name=='initialize' else name
        lines.append(f'  | {name} => exact state_field_{field} input bits')
    lines += ['end '+ns,'']
    return {module:'\n\n'.join(lines)}


def wire_sources(frontend_rb, core_rb, frontend, core, frontend_views, core_views,
                 *, prefix='PhysicalGRT', namespace='Pinwheel.Artifact.StreamingPhysicalGRT.Join',
                 frontend_module='PhysicalFrontendProof',core_module='PhysicalCoreProof',
                 frontend_inputs='PhysicalGRTFrontendInputs',core_inputs='PhysicalGRTCoreInputs',
                 parent_namespace='Pinwheel.Artifact.StreamingPhysicalGRT.Original'):
    """Derive both directed component port connections from actual root images."""
    fns=frontend['namespace'];cns=core['namespace'];fv=frontend_views['namespace'];cv=core_views['namespace']
    module=prefix+'ComponentWires';lines=[header([frontend_module,core_module,frontend_inputs,core_inputs],namespace),
        'open Pinwheel.Hardware']
    incoming='(incoming : Nat → Bool)';values=f'{parent_namespace}.network.value incoming'
    for receiver,source_rb,source,source_views,source_ns,source_input,source_state,fields in [
            (cv,frontend_rb,frontend,frontend_views,fns,f'{fv}.readInputs ({values})',f'{fv}.readState ({values})',
                [(field,width,ctor,'core_'+field) for field,(width,ctor) in core_rb.INPUTS.items()]),
            (fv,core_rb,core,core_views,cns,f'{cv}.readInputs ({values})',f'{cv}.readState ({values})',
                [('status_'+field,width,'.status '+ctor,field) for field,(width,ctor) in core_rb.OUTPUTS.items()])]:
        for field,width,_,output in fields:
            require(output in source_rb.OUTPUTS and source_rb.OUTPUTS[output][0]==width,'Changed actual connected component port width')
            ctor=source_rb.OUTPUTS[output][1];root=f'{source_ns}.roots_output_{output}';read=f'{receiver}.read_input_{field}'
            tag=('core_' if receiver==cv else 'status_')+field
            lines += [f'theorem {tag}_roots : ∀ bit : Fin {width}, {read}Root bit.val =',
                f'    ({root} bit).rename {source_views["namespace"]}.embedding.image := by decide +kernel',
                f'theorem {tag}_bounded : ∀ bit : Fin {width}, ({root} bit).Bounded ({source_ns}.network.inputs + {source_ns}.network.nodes) := by decide +kernel',
                f'theorem {tag}_wire {incoming} : {read} ({values}) =',
                f'    {source_ns}.observe ({source_input}) ({source_state}) ({ctor}) := by',
                '  apply Word.from_bits','  intro index bound',
                f'  rw [{read}, Word.pack_bit _ index bound, {tag}_roots ⟨index,bound⟩]',
                f'  rw [{source_views["namespace"]}.atom_read incoming _ ({tag}_bounded ⟨index,bound⟩)]',
                f'  exact (Word.pack_bit (fun bit => ({root} bit).eval ({source_ns}.network.value ({source_ns}.inputValues ({source_input}) ({source_state})))) index bound).symm']
    lines += [f'theorem core_wires {incoming} :',
        f'    ({cv}.readInputs ({values}) : Values {core_rb.INPUT_TYPE}) =',
        f'      (fun {{w}} port => {fns}.observe ({fv}.readInputs ({values})) ({fv}.readState ({values})) (.core port)) := by',
        '  funext width port','  cases port with']
    for field,(_,ctor) in core_rb.INPUTS.items():
        name=ctor[1:];name='«initialize»' if name=='initialize' else name
        lines.append(f'  | {name} => exact core_{field}_wire incoming')
    lines += [f'theorem status_wires {incoming} :',
        f'    (fun {{w}} port => {fv}.readInputs ({values}) (.status port) : Values {core_rb.OUTPUT_TYPE}) =',
        f'      (fun {{w}} port => {cns}.observe ({cv}.readInputs ({values})) ({cv}.readState ({values})) port) := by',
        '  funext width port','  cases port with']
    for field,(_,ctor) in core_rb.OUTPUTS.items():lines.append(f'  | {ctor[1:]} => exact status_status_{field}_wire incoming')
    lines += ['end '+namespace,'']
    return {module:'\n\n'.join(lines)}


def physical_sources(frontend_views, parent_model, *, prefix='PhysicalGRT',
                     namespace='Pinwheel.Artifact.StreamingPhysicalGRT.Join',
                     parent_namespace='Pinwheel.Artifact.StreamingPhysicalGRT.Original',
                     parent_module='PhysicalGRTOriginalNetwork'):
    """Reconstruct the actual TT public input basis and its cold-reset gate."""
    from streaming_tt_certificate import expression_signature
    from streaming_mapped_certificate import substitute
    from streaming_tt_graph import term_source
    expected=tuple([('input','ena',0),('input','rst_n',0)]+
        [('input','ui_in',bit) for bit in range(8)]+[('input','uio_in',bit) for bit in range(8)])
    require(parent_model['labels'][:18]==expected and len(parent_model['labels'])==6057,'Changed TT public/state input basis')
    fv=frontend_views['namespace'];root=frontend_views['port_metadata']['input','initialize']
    require(len(root)==1 and root[0][0]=='wire' and not root[0][2],'Changed physical initialization root')
    wire=root[0][1];index=wire-6057;require(0<=index<len(parent_model['nodes']),'Initialization is not a connected actual cell')
    node=parent_model['nodes'][index];formula=substitute(node['expression'],{'p'+str(at):('variable','w'+str(source))
        for at,source in enumerate(node['sources'])})
    nand=('not',('*',('variable','w0'),('variable','w1')))
    require(expression_signature(formula)==expression_signature(nand),'Changed cold-reset NAND semantics')
    module=prefix+'PhysicalInputs';args='(input : Fin 18 → Bool) (bits : Fin 6039 → Bool)'
    values=f'{parent_namespace}.network.value (Device.environment input bits)'
    lines=[header([frontend_views['views_module'],parent_module,'Pinwheel.Hardware.StreamingPhysical.Device',
        'Pinwheel.Hardware.StreamingPhysical.Local','Pinwheel.Hardware.StreamingReady.TinyWiring'],namespace),
        'open Pinwheel.Hardware',
        'def pins (input : Fin 18 → Bool) : StreamingReady.TinyWiring.Pins :=',
        '  ⟨Word.pack (fun bit => input ⟨2+bit.val,by have h:=bit.isLt; omega⟩),',
        '   Word.pack (fun bit => input ⟨10+bit.val,by have h:=bit.isLt; omega⟩),',
        '   Word.pack (fun _ => input ⟨0,by decide⟩), Word.pack (fun _ => input ⟨1,by decide⟩)⟩',
        'def enginePins (input : Fin 18 → Bool) : StreamingReady.Package.Pins :=',
        '  StreamingReady.TinyWiring.Description.enginePins (StreamingReady.TinyWiring.canonical 1) (pins input)',
        f'theorem primary_atom {args} (index : Fin 18) :',
        f'    (Atom.wire index.val false).eval ({values}) = input index := by',
        f'  change {parent_namespace}.network.value (Device.environment input bits) index.val = input index',
        '  have indexBound := index.isLt',
        '  rw [Network.value_input _ _ _ (by change index.val < 6057; omega)]',
        '  exact dif_pos index.isLt',
        f'def initializeTerm : Term := {term_source(nand)}',
        f'theorem initialize_connected : ({parent_namespace}.network.node ⟨{index},by decide⟩).term (fun wire => .wire wire false) = initializeTerm := by decide +kernel',
        f'theorem initialize_value {args} : ({values}) {wire} = !(input ⟨0,by decide⟩ && input ⟨1,by decide⟩) := by',
        f'  have interpreted := Node.eval_term ({parent_namespace}.network.node ⟨{index},by decide⟩) (fun wire => .wire wire false) ({values})',
        '  rw [initialize_connected] at interpreted',
        f'  have actual := (Network.value_node {parent_namespace}.network (Device.environment input bits) ⟨{index},by decide⟩).trans interpreted.symm',
        f'  change ({values}) {wire} = _ at actual',
        '  apply actual.trans',
        f'  change (!(({values}) 0 && ({values}) 1)) = _',
        '  rw [show ('+values+') 0 = input ⟨0,by decide⟩ from primary_atom input bits ⟨0,by decide⟩,',
        '    show ('+values+') 1 = input ⟨1,by decide⟩ from primary_atom input bits ⟨1,by decide⟩]',
        f'theorem initialize_wire {args} : {fv}.read_input_initialize ({values}) = (enginePins input).initialize := by',
        '  apply Word.from_bits','  intro bit within','  have zero : bit = 0 := by omega','  subst bit',
        f'  rw [{fv}.read_input_initialize,Word.pack_bit _ 0 within]',
        f'  change ({values}) {wire} = _','  rw [initialize_value]',
        '  change _ = (~~~((pins input).ena &&& (pins input).rstN)).getLsbD 0',
        '  rw [BitVec.getLsbD_not, BitVec.getLsbD_and]',
        '  simp only [pins, Word.pack_bit (width := 1) _ 0 (by decide), decide_true, Bool.true_and] <;> rfl']
    for field,width,ctor,start in [('sck',1,'.sck',3),('csn',1,'.csn',2),('mosi',4,'.mosi',None),('raw_inputs',2,'.rawInputs',5)]:
        positions=[4,7,8,9] if field=='mosi' else list(range(start,start+width))
        rootfn=f'{fv}.read_input_{field}Root';read=f'{fv}.read_input_{field}'
        branches=' '.join('| '+str(bit)+' => ⟨'+str(position)+',by decide⟩' for bit,position in enumerate(positions[:-1]))+' | _ => ⟨'+str(positions[-1])+',by decide⟩'
        lines += [f'def physical_index_{field} (bit : Fin {width}) : Fin 18 :=',
            f'  match bit.val with {branches}',
            f'theorem physical_root_{field} : ∀ bit : Fin {width}, {rootfn} bit.val = .wire (physical_index_{field} bit).val false := by decide +kernel']
        points=[]
        point_expression="((pins input).ui.extractLsb' 5 3 ++ (pins input).ui.extractLsb' 2 1)" if field=='mosi' else "((pins input).ui.extractLsb' "+str(start-2)+" "+str(width)+")"
        for bit,position in enumerate(positions):
            name=f'physical_point_{field}_{bit}';points.append(name)
            lines += [f'theorem {name} (input : Fin 18 → Bool) : input (physical_index_{field} ⟨{bit},by decide⟩) =',
                f'    ((enginePins input).{ctor[1:]}).getLsbD {bit} := by',
                f'  change input ⟨{position},by decide⟩ = _',
                f'  change _ = ((enginePins input).{ctor[1:]}).getLsbD {bit}',
                f'  change _ = ({point_expression}).getLsbD {bit}',
                "  rw [BitVec.getLsbD_extractLsb']" if field!='mosi' else "  rw [BitVec.getLsbD_append]; simp only [BitVec.getLsbD_extractLsb']",
                f'  change _ = ((pins input).ui).getLsbD {position-2}',
                f'  exact (Word.pack_bit (width := 8) (fun index : Fin 8 => input ⟨2+index.val,by have h:=index.isLt; omega⟩) {position-2} (by decide)).symm']
        term='(fun index => Fin.elim0 index)'
        for point in reversed(points):term=f'(Fin.cases ({point} input) {term})'
        lines += [f'theorem physical_wire_{field} {args} : {read} ({values}) = (enginePins input).{ctor[1:]} := by']
        lines += ['  apply Word.from_bits','  intro bit within',
            f'  rw [{read}, Word.pack_bit _ bit within, physical_root_{field} ⟨bit,within⟩, primary_atom]',
            f'  have all : ∀ index : Fin {width}, input (physical_index_{field} index) = ((enginePins input).{ctor[1:]}).getLsbD index.val := {term}',
            '  exact all ⟨bit,within⟩']
    lines += [f'theorem physical_wires {args} :',
        f'    ({fv}.readInputs ({values}) : Values Streaming.Frontend.Input) =',
        f'      (fun {{w}} port => (enginePins input).inputs (fun {{w}} field => {fv}.readInputs ({values}) (.status field)) port) := by',
        '  funext width field','  cases field with',
        '  | «initialize» => exact initialize_wire input bits',
        '  | sck => exact physical_wire_sck input bits',
        '  | csn => exact physical_wire_csn input bits',
        '  | mosi => exact physical_wire_mosi input bits',
        '  | rawInputs => exact physical_wire_raw_inputs input bits',
        '  | status field => rfl']
    lines += ['end '+namespace,'']
    return {module:'\n\n'.join(lines)}


def next_sources(rb, views, child, *, component, prefix,
                 parent_device_module='PhysicalGRTOriginalDevice',
                 parent_device_namespace='Pinwheel.Artifact.StreamingPhysicalGRT.OriginalState',
                 parent_network_namespace='Pinwheel.Artifact.StreamingPhysicalGRT.Original',
                 packing_module='PhysicalStateCodec',packing_namespace='Pinwheel.Artifact.StreamingPhysicalState',
                 child_module=None,inputs_module=None):
    """Connect every actual D endpoint, including all bank and queue storage."""
    require(component in ('frontend','core'),'Unknown actual D component')
    cn=child['namespace'];ns=views['namespace'];packing=packing_namespace+'.packing'
    child_module=child_module or ('Physical'+component.title()+'Proof')
    inputs_module=inputs_module or ('PhysicalGRT'+component.title()+'Inputs')
    lines=[header([parent_device_module,packing_module,child_module,inputs_module],ns),'open Pinwheel.Hardware']
    incoming='(input : Fin 18 → Bool) (bits : Fin 6039 → Bool)';env='Device.environment input bits'
    values=f'{parent_network_namespace}.network.value ({env})'
    for field,(width,ctor) in rb.REGISTERS.items():
        source=f'{cn}.roots_next_{field}'
        lines += [f'theorem next_roots_{field} : ∀ bit : Fin {width},',
            f'    {parent_device_namespace}.device.next ({packing}.index ⟨{width},.{component} ({ctor}),bit⟩) =',
            f'      ({source} bit).rename embedding.image := by decide +kernel',
            f'theorem next_bounded_{field} : ∀ bit : Fin {width}, ({source} bit).Bounded ({cn}.network.inputs + {cn}.network.nodes) := by decide +kernel',
            f'theorem next_field_{field} {incoming} :',
            f'    {packing}.decode ({parent_device_namespace}.device.step input bits) (.{component} ({ctor})) =',
            f'      {cn}.step (readInputs ({values})) (readState ({values})) ({ctor}) := by',
            '  apply Word.from_bits','  intro bit within',
            '  rw [Packing.decode_bit _ _ _ ⟨bit,within⟩]',
            f'  change ({parent_device_namespace}.device.next ({packing}.index ⟨{width},.{component} ({ctor}),⟨bit,within⟩⟩)).eval ({values}) = _',
            f'  rw [next_roots_{field} ⟨bit,within⟩, atom_read ({env}) _ (next_bounded_{field} ⟨bit,within⟩)]',
            f'  exact (Word.pack_bit (fun bit => ({source} bit).eval ({cn}.network.value ({cn}.inputValues (readInputs ({values})) (readState ({values}))))) bit within).symm']
    lines += [f'theorem next_component {incoming} :',
        f'    (fun {{w}} field => {packing}.decode ({parent_device_namespace}.device.step input bits) (.{component} field) : Values {rb.REGISTER_TYPE}) =',
        f'      (fun {{w}} field => {cn}.step (readInputs ({values})) (readState ({values})) field) := by',
        '  funext width field','  cases field with']
    consumed=set()
    for family,ctor,count,_ in rb.FAMILIES:
        term='(fun index => Fin.elim0 index)'
        for index in reversed(range(count)):term=f'(Fin.cases (next_field_r_{family}{index} input bits) {term})'
        lines += [f'  | {ctor} address =>',
            f'    have all : ∀ index : Fin {count}, {packing}.decode ({parent_device_namespace}.device.step input bits) (.{component} (.{ctor} (BitVec.ofFin index))) =',
            f'        {cn}.step (readInputs ({values})) (readState ({values})) (.{ctor} (BitVec.ofFin index)) := {term}',
            '    exact all address.toFin']
        consumed.update('r_'+family+str(index) for index in range(count))
    for field,(_,ctor) in rb.REGISTERS.items():
        if field in consumed:continue
        name=ctor[1:];name='«initialize»' if name=='initialize' else name
        lines.append(f'  | {name} => exact next_field_{field} input bits')
    lines += ['end '+ns,'']
    return {prefix+'NextJoin':'\n\n'.join(lines)}


def output_sources(parent_model, frontend, core, frontend_embedding, core_embedding,
                   *, prefix='PhysicalGRT',namespace='Pinwheel.Artifact.StreamingPhysicalGRT.Join'):
    """Check all 24 public endpoints and all actual wrapper mask cells."""
    from streaming_tt_certificate import rename_atom,atom_expression,expression_signature
    from streaming_mapped_certificate import substitute
    from streaming_tt_graph import atom_source,term_source
    from streaming_tt_public import local_sources
    helpers=local_sources(prefix=prefix,namespace=namespace)
    helper_module=next(iter(helpers))
    parent='Pinwheel.Artifact.StreamingPhysicalGRT.Original';device='Pinwheel.Artifact.StreamingPhysicalGRT.OriginalState.device'
    fn=frontend['namespace'];cn=core['namespace'];fv=frontend_embedding['embedding']['namespace'];cv=core_embedding['embedding']['namespace']
    old='Pinwheel.Artifact.StreamingOptimizedTinyD2';env='Device.environment input bits';values=f'{parent}.network.value ({env})'
    args='(input : Fin 18 → Bool) (bits : Fin 6039 → Bool)'
    models={'frontend':(frontend,frontend_embedding,fn,fv),'core':(core,core_embedding,cn,cv)}
    logical={'miso':('frontend','miso','.miso'),'ready':('frontend','ready','.ready'),
        'busy':('core','busy','.busy'),'levels':('core','levels','.levels'),'enabled':('core','enabled','.enabled')}
    pad_fields={'uio_oe':('oe',[(0,'enabled',0),(1,'enabled',1),(2,'enabled',2)]),
        'uio_out':('uio',[(0,'levels',0),(1,'levels',1),(2,'levels',2)]),
        'uo_out':('uo',[(0,'miso',0),(1,'miso',1),(2,'miso',2),(3,'miso',3),(4,'ready',0),(5,'busy',0)])}
    require(tuple(parent_model['outputs'])==tuple(pad_fields),'Changed final public output ordering')
    require(all(len(parent_model['outputs'][port]) == 8 for port in pad_fields),
        'Missing or extra actual public output endpoints')
    module=prefix+'PublicOutputs';lines=[header(['PhysicalGRTPhysicalInputs','PhysicalFrontendProof','PhysicalCoreProof',
        'PhysicalGRTFrontendInputs','PhysicalGRTCoreInputs','PhysicalGRTOriginalDevice','StreamingOptimizedTinyD2',helper_module],namespace),'open Pinwheel.Hardware',
        f'def logicalOutputs {args} : Values StreamingReady.Package.Output']
    for logical_field,(component,field,ctor) in logical.items():
        _,_,child,view=models[component]
        lines.append(f'  | _, .{logical_field} => {child}.observe ({view}.readInputs ({values})) ({view}.readState ({values})) ({ctor})')
    lines += [f'def originalPads {args} (pad : StreamingReady.TinyWiring.Pad) : BitVec 8 :=',
        '  match pad with',
        f'  | .oe => Word.pack (fun bit => {device}.observe input bits ⟨0+bit.val,by have h:=bit.isLt; omega⟩)',
        f'  | .uio => Word.pack (fun bit => {device}.observe input bits ⟨8+bit.val,by have h:=bit.isLt; omega⟩)',
        f'  | .uo => Word.pack (fun bit => {device}.observe input bits ⟨16+bit.val,by have h:=bit.isLt; omega⟩)']
    for ordinal,(port,(pad,fields)) in enumerate(pad_fields.items()):
        fields={bit:(field,index) for bit,field,index in fields};word_points=[]
        for bit,actual_root in enumerate(parent_model['outputs'][port]):
            number=ordinal*8+bit;tag='public_'+port+'_'+str(bit);word_points.append(tag+'_word')
            lines += [f'theorem {tag}_root : {device}.output ⟨{number},by decide⟩ = {atom_source(actual_root)} := by decide +kernel']
            if bit not in fields:
                require(actual_root==('constant',False),'Unused TT output is not actual literal zero')
                lines += [f'theorem {tag}_graph {args} : {device}.observe input bits ⟨{number},by decide⟩ = false := by',
                    f'  exact public_observe_constant {device} input bits ⟨{number},by decide⟩ false {tag}_root']
            else:
                field,outbit=fields[bit];component,child_field,ctor=logical[field];child,embedding,child_ns,view=models[component]
                child_root=child['model']['outputs'][child_field][outbit];source_root=rename_atom(child_root,embedding['plan']['image'])
                require(actual_root[0]=='wire' and not actual_root[2],'Public active mask lacks an actual gate')
                gate=actual_root[1]-len(parent_model['labels']);require(0<=gate<len(parent_model['nodes']),'Public output gate is outside actual model')
                node=parent_model['nodes'][gate];formula=substitute(node['expression'],{'p'+str(at):('variable','w'+str(source)) for at,source in enumerate(node['sources'])})
                expected=('*',('*',('variable','w0'),('variable','w1')),atom_expression(source_root))
                require(expression_signature(formula)==expression_signature(expected),'Public mask does not match its actual connected engine bit')
                root=f'{child_ns}.roots_output_{child_field} ⟨{outbit},by decide⟩'
                lines += [f'def {tag}_term : Term := {term_source(expected)}',
                    f'theorem {tag}_connected : ({parent}.network.node ⟨{gate},by decide⟩).term (fun wire => .wire wire false) = {tag}_term := by decide +kernel',
                    f'theorem {tag}_source_root : ({root}).rename {view}.embedding.image = {atom_source(source_root)} := by decide +kernel',
                    f'theorem {tag}_bounded : ({root}).Bounded ({child_ns}.network.inputs + {child_ns}.network.nodes) := by decide +kernel',
                    f'theorem {tag}_source {args} : ({atom_source(source_root)} : Atom).eval ({values}) = (logicalOutputs input bits .{field}).getLsbD {outbit} := by',
                    f'  rw [← {tag}_source_root, {view}.atom_read ({env}) _ {tag}_bounded]',
                    f'  exact (Word.pack_bit (fun bit => ({child_ns}.roots_output_{child_field} bit).eval ({child_ns}.network.value ({child_ns}.inputValues ({view}.readInputs ({values})) ({view}.readState ({values}))))) {outbit} (by decide)).symm',
                    f'theorem {tag}_raw_graph {args} : {device}.observe input bits ⟨{number},by decide⟩ =',
                    f'    ((input ⟨0,by decide⟩ && input ⟨1,by decide⟩) && ({atom_source(source_root)} : Atom).eval ({values})) := by',
                    f'  exact public_observe_mask {device} {parent}.network rfl input bits',
                    f'    ⟨{number},by decide⟩ ⟨{gate},by decide⟩ ({atom_source(source_root)} : Atom)',
                    f'    {tag}_root {tag}_connected (input ⟨0,by decide⟩) (input ⟨1,by decide⟩)',
                    '    (primary_atom input bits ⟨0,by decide⟩) (primary_atom input bits ⟨1,by decide⟩)',
                    f'theorem {tag}_graph {args} : {device}.observe input bits ⟨{number},by decide⟩ =',
                    f'    ((input ⟨0,by decide⟩ && input ⟨1,by decide⟩) && (logicalOutputs input bits .{field}).getLsbD {outbit}) :=',
                    f'  ({tag}_raw_graph input bits).trans (congrArg (fun value => (input ⟨0,by decide⟩ && input ⟨1,by decide⟩) && value) ({tag}_source input bits))']
            lines += [f'theorem {tag}_word {args} : {device}.observe input bits ⟨{number},by decide⟩ =',
                f'    ({old}.{port} (pins input) (logicalOutputs input bits)).getLsbD {bit} := by',
                f'  rw [{tag}_graph, {old}.{port}, Word.pack_bit (width := 8) _ {bit} (by decide)]']
            if bit in fields:
                field,outbit=fields[bit]
                lines += [f'  change _ = (((pins input).ena.getLsbD 0 && (pins input).rstN.getLsbD 0) && (logicalOutputs input bits .{field}).getLsbD {outbit})',
                    '  simp only [pins, Word.pack_bit (width := 1) _ 0 (by decide)]']
            else:lines.append('  rfl')
        term='(fun index => Fin.elim0 index)'
        for point in reversed(word_points):term=f'(Fin.cases ({point} input bits) {term})'
        lines += [f'theorem original_pad_{port} {args} : originalPads input bits .{pad} = {old}.{port} (pins input) (logicalOutputs input bits) := by',
            '  apply Word.from_bits','  intro bit within','  rw [originalPads, Word.pack_bit _ bit within]',
            f'  have all : ∀ index : Fin 8, {device}.observe input bits ⟨{ordinal*8}+index.val,by have h:=index.isLt; omega⟩ =',
            f'      ({old}.{port} (pins input) (logicalOutputs input bits)).getLsbD index.val := {term}',
            '  exact all ⟨bit,within⟩']
    lines += ['end '+namespace,'']
    return {**helpers,module:'\n\n'.join(lines)}
