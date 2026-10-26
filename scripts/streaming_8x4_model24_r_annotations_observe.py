"""Complete pre/post Native terminal-annotation witness; no ignored opcodes.

The post-order BTERM sequence is a source prediction until the actual new
Native snapshot supplies all endpoint/name/net/direction/use records.
"""
import streaming_8x4_model24_r_decoder_observe as PREVIOUS
G=PREVIOUS.G
P=G.P

ANNOTATED=PREVIOUS.DECODE.replace('        $decoder begin $wire',
    '        $decoder begin $wire\n        set decoder_point {UNBOUND UNBOUND UNBOUND}')
ANNOTATED=ANNOTATED.replace('                set xyz [$decoder getPoint_ext]',
    '                set xyz [$decoder getPoint_ext]\n                set decoder_point $xyz')
ANNOTATED=ANNOTATED.replace('            } elseif {$op == $odb::dbWireDecoder_END_DECODE} {',
'''            } elseif {$op == $odb::dbWireDecoder_BTERM} {
                set terminal [$decoder getBTerm]
                puts $f [join [list DECODE $netname $index BTERM [$terminal getName] [[$terminal getNet] getName] [$terminal getIoType] [$terminal getSigType] [lindex $decoder_point 0] [lindex $decoder_point 1]] "\\t"]
            } elseif {$op == $odb::dbWireDecoder_END_DECODE} {''')


def tcl(original):
    P.need(original.count(PREVIOUS.DECODE)==1 and original.count('    set f [open $path w]')==1,'Exact previous decoder observer changed')
    result=original.replace(PREVIOUS.DECODE,ANNOTATED).replace('    set f [open $path w]',
        '    set f [open $path w]\n    fconfigure $f -buffering line')
    P.need(result.replace(ANNOTATED,PREVIOUS.DECODE).replace('    fconfigure $f -buffering line\n','')==original,'Annotation/line-buffer-only Tcl delta differs')
    return result


def native_pair(before_text,after_text,sheets):
    before=PREVIOUS.native_geometry(before_text,sheets)
    rows=[line.split('\t') for line in after_text.splitlines()];decoded={}
    for row in rows:
        P.need(row and row[0] in ('BLOCK','LAYER','NDR','NET','BTERM','BPIN','DECODE'),'Unknown post-order inventory row')
        if row[0]=='DECODE':
            P.need(len(row)>=4,'Truncated actual post-order decoder event');decoded.setdefault(row[1],[]).append(row)
    P.need(set(decoded)=={r['name'] for r in G.cases()},'Missing/foreign post-order net membership')
    annotations=[]
    for case in G.cases():
        name=case['name'];wanted=[['PATH',case['layer'],'ROUTED']]
        if case['ndr']:wanted.append(['RULE',case['ndr'],case['layer'],str(case['width_dbu']),str(case['width_dbu'])])
        for suffix,direction,point in (('A','INPUT',case['start']),('B','OUTPUT',case['end'])):
            wanted.append(['POINT_EXT',*map(str,point),'0'])
            wanted.append(['BTERM',name+'_'+suffix,name,direction,'SIGNAL',*map(str,point)])
        wanted.append(['END_DECODE'])
        expected=[['DECODE',name,str(i),*event] for i,event in enumerate(wanted)]
        events=decoded[name];P.need(events==expected,'Actual terminal name/net/direction/use/endpoint/order or complete geometry differs: '+name)
        # Only after validating the exact complete BTERM records may their
        # geometric projection be compared to the previously bound decoder.
        for event in events:
            if event[3]=='BTERM':annotations.append(dict(net=name,actual_BTerm=event[4],actual_BTerm_net=event[5],actual_direction=event[6],actual_use=event[7],attached_observed_point_dbu=list(map(int,event[8:10]))))
    projected=[];indices={}
    for row in rows:
        if row[0]!='DECODE':projected.append(row)
        elif row[3]!='BTERM':
            index=indices.get(row[1],0);projected.append(['DECODE',row[1],str(index),*row[3:]]);indices[row[1]]=index+1
    after=PREVIOUS.native_geometry('\n'.join('\t'.join(row) for row in projected)+'\n',sheets)
    P.need(after==before,'Post-order complete geometric/default/NDR/global-port projection changed')
    P.need(len(annotations)==60 and len({r['actual_BTerm'] for r in annotations})==60,'Actual terminal annotation membership differs')
    return dict(complete_before_snapshot=before,complete_after_native_rows=rows,
        complete_after_geometry_projection=after,actual_terminal_annotations=annotations,
        terminal_annotation_delta_checked=True,exactly_two_actual_BTERM_annotations_per_net=True,
        complete_pre_post_geometric_and_global_inventory_equal=True,
        predicted_annotation_scope_confirmed_by_complete_actual_observation=True,
        dbWire_getLength_numeric_measurement_claimed=False,
        complete_public_decoder_geometry_terminal_stream_observed=True,
        internal_RC_property_operands_observed=False,raw_wire_encoding_byte_identity_claimed=False)
