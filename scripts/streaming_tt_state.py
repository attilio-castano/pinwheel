"""Checked full-register codec from selected backend constructor metadata."""
from streaming_mapped_liberty import require
from streaming_tt_graph import header,lookup_source


def generate(codec, *, module='PhysicalStateCodec', namespace='Pinwheel.Artifact.StreamingPhysicalState'):
    require(codec.get('total_bits')==6039 and codec.get('queue_address_bits')==1,
        'Expected exact depth-two full-state codec')
    fields=[];groups=[]
    for component,constructor in [('frontend','frontend'),('core-d2','core')]:
        data=codec['components'][component];remaining={field['register']:field for field in data['fields']}
        for family,ctor,count,address_width in data['families']:
            members=[remaining.pop('r_'+family+str(index)) for index in range(count)]
            width=members[0]['width'];offset=members[0]['first_bit']
            require(all(field['width']==width and field['first_bit']==offset+index*width
                for index,field in enumerate(members)),'Noncontiguous actual register family')
            groups.append(dict(component=constructor,ctor=ctor,width=width,offset=offset,
                count=count,address_width=address_width))
        for field in remaining.values():
            require(field['ctor'].startswith('.') and ' ' not in field['ctor'], 'Unexpected scalar constructor')
            groups.append(dict(component=constructor,ctor=field['ctor'][1:],width=field['width'],
                offset=field['first_bit'],count=1,address_width=None))
        fields.extend((constructor,field) for field in data['fields'])
    positions={}
    for component,field in fields:
        for index in range(field['width']):
            bit=field['first_bit']+index
            require(bit not in positions,'Overlapping semantic-register codec')
            positions[bit]=f'⟨{field["width"]},.{component} ({field["ctor"]}),⟨{index},by decide⟩⟩'
    require(set(positions)==set(range(6039)),'Incomplete semantic-register codec')
    lines=[header(['Pinwheel.Hardware.StreamingPhysical.State'],namespace),
        'open Pinwheel.Hardware',
        lookup_source('fieldTable',[positions[index] for index in range(6039)],
            result_type='BitField Register',default=positions[0]),
        'def layoutField (index : Fin 6039) : BitField Register := fieldTable index.val',
        'def layoutIndex : BitField Register → Fin 6039']
    for group in groups:
        part,ctor,width,offset=group['component'],group['ctor'],group['width'],group['offset']
        operand=f'(.{ctor} address)' if group['address_width'] is not None else f'.{ctor}'
        value=f'{offset} + address.toNat * {width} + bit.val' if group['address_width'] is not None else f'{offset} + bit.val'
        bound='have addressBound := address.isLt; have bitBound := bit.isLt; omega' if group['address_width'] is not None else 'have bitBound := bit.isLt; omega'
        lines.append(f'  | ⟨_,.{part} {operand},bit⟩ => ⟨{value},by {bound}⟩')
    lines.append('theorem index_field : ∀ index, layoutIndex (layoutField index) = index := by decide +kernel')
    for group in groups:
        part,ctor,width=group['component'],group['ctor'],group['width'];name=part+'_'+ctor
        if group['address_width'] is not None:
            params=f'(address : BitVec {group["address_width"]}) (bit : Fin {width})'
            field=f'⟨{width},.{part} (.{ctor} address),bit⟩'
        else:params=f'(bit : Fin {width})';field=f'⟨{width},.{part} .{ctor},bit⟩'
        lines.append(f'theorem {name} : ∀ {params}, layoutField (layoutIndex {field}) = {field} := by decide +kernel')
    lines += ['theorem field_index (bit : BitField Register) : layoutField (layoutIndex bit) = bit := by',
        '  cases bit with','  | mk width field bit =>','    cases field with']
    for part in ('frontend','core'):
        lines += [f'    | {part} field =>','      cases field with']
        for group in groups:
            if group['component']!=part:continue
            ctor=group['ctor'];arg=' address' if group['address_width'] is not None else ''
            lines.append(f'      | {ctor}{arg} => exact {part}_{ctor}'+arg+' bit')
    lines += ['def packing : Packing Register 6039 := ⟨layoutIndex,layoutField,index_field,field_index⟩',
        'theorem arbitrary_state (bits : Fin 6039 → Bool) :',
        '    packing.encode (packing.decode bits) = bits := packing.encode_decode bits',
        'theorem arbitrary_package (state : StreamingReady.Package.State 1) :',
        '    packageState (packing.decode (packing.encode (stateValues state))) = state := by',
        '  rw [packing.decode_encode]','  exact packageState_stateValues state','end '+namespace,'']
    return {module:'\n\n'.join(lines)}
