"""Complete actual decoder witness replacing opaque uint64_t Tcl pointers.

No Native launch here. Coordinates/rules/extensions are observed; shape and
length quantities are explicitly derived from those observations and the
pinned dbShape construction, never labelled as a getLength API result.
"""
from decimal import Decimal as D
import streaming_8x4_model24_r_endpoint_geometry as G
P=G.P

OLD_LINE='        puts $f [join [list NET [$net getName] [$wire getLength] $name [llength [$net getITerms]] [llength [$net getBTerms]] [llength [$net getSWires]] [$net isSpecial] [$net getSigType]] "\\t"]'
OLD_LINE=OLD_LINE.replace(chr(92)+'t',chr(9))
DECODE='''        set netname [$net getName]
        puts $f [join [list NET $netname $name [llength [$net getITerms]] [llength [$net getBTerms]] [llength [$net getSWires]] [$net isSpecial] [$net getSigType]] "\\t"]
        set decoder [odb::dbWireDecoder]
        $decoder begin $wire
        for {set index 0} {$index < 16} {incr index} {
            set op [$decoder next]
            if {$op == $odb::dbWireDecoder_PATH} {
                puts $f [join [list DECODE $netname $index PATH [[$decoder getLayer] getName] [$decoder getWireType]] "\\t"]
            } elseif {$op == $odb::dbWireDecoder_RULE} {
                set lr [$decoder getRule]
                puts $f [join [list DECODE $netname $index RULE [[$lr getNonDefaultRule] getName] [[$lr getLayer] getName] [$lr getWidth] [$lr getSpacing]] "\\t"]
            } elseif {$op == $odb::dbWireDecoder_POINT_EXT} {
                set xyz [$decoder getPoint_ext]
                if {[llength $xyz] != 3} {error "Decoder numeric POINT_EXT triplet missing"}
                foreach value $xyz {if {![string is integer -strict $value]} {error "Decoder coordinate/extension is not an integer"}}
                puts $f [join [concat [list DECODE $netname $index POINT_EXT] $xyz] "\\t"]
            } elseif {$op == $odb::dbWireDecoder_END_DECODE} {
                puts $f [join [list DECODE $netname $index END_DECODE] "\\t"]
                break
            } else {
                error "Undeclared actual decoder opcode $op"
            }
        }
        if {$index >= 16} {error "Decoder did not terminate within fixed fixture bound"}'''


def tcl(original):
    P.need(original.count(OLD_LINE)==1,'Exact original opaque length observer changed')
    result=original.replace(OLD_LINE,DECODE)
    P.need('[$wire getLength]' not in result and result.replace(DECODE,OLD_LINE)==original,'Observer-only Tcl delta differs')
    return result


def native_geometry(text,sheets):
    all_rows=[line.split('\t') for line in text.splitlines()];rows=[];decoded={}
    for row in all_rows:
        P.need(row and row[0] in ('BLOCK','LAYER','NDR','NET','BTERM','BPIN','DECODE'),'Unknown Native decoder inventory row')
        if row[0]=='DECODE':
            P.need(len(row)>=4,'Truncated Native decoder event');decoded.setdefault(row[1],[]).append(row)
        else:rows.append(row)
    expected=[['BLOCK','1000','0','0','30','60','1']]
    for m in G.METALS:expected.append(['LAYER',m,str(int(D(G.WIDTHS[m])*1000)),G.DIRECTIONS[m],str(sheets[m])])
    for m in G.METALS:
        width=str(int(D(G.WIDTHS[m])*2000));expected.append(['NDR','WIDE',m,width,width])
    for r in G.cases():expected.append(['NET',r['name'],r['ndr'] or '-','0','2','0','0','SIGNAL'])
    for r in G.cases():
        for i,(suffix,direction,point) in enumerate((('A','INPUT',r['start']),('B','OUTPUT',r['end']))):
            name=r['name']+'_'+suffix;box=r['contact_boxes'][i];glob=[v+point[j%2] for j,v in enumerate(box)]
            expected.extend([['BTERM',name,r['name'],direction,'SIGNAL','1'],['BPIN',name,r['layer'],*map(str,glob),'FIRM']])
    def normal(row):
        value=list(row)
        if value[0]=='LAYER' and len(value)==5:value[4]=str(D(value[4]).normalize())
        return value
    P.need(sorted(map(normal,rows))==sorted(map(normal,expected)),'Actual complete block/port/layer/NDR/endface inventory differs')
    cases=G.cases();P.need(set(decoded)=={r['name'] for r in cases},'Missing/foreign Native decoded net membership')
    derived=[]
    for r in cases:
        events=decoded[r['name']];wanted=[['PATH',r['layer'],'ROUTED']]
        if r['ndr']:wanted.append(['RULE',r['ndr'],r['layer'],str(r['width_dbu']),str(r['width_dbu'])])
        wanted += [['POINT_EXT',*map(str,r['start']),'0'],['POINT_EXT',*map(str,r['end']),'0'],['END_DECODE']]
        complete=[['DECODE',r['name'],str(i),*event] for i,event in enumerate(wanted)]
        P.need(events==complete,'Actual complete Native opcode/order/coordinate/extension/rule differs: '+r['name'])
        # Parse the actual observed data again for derivation, rather than
        # reporting expected fixture values as a Native API measurement.
        actual_points=[list(map(int,event[4:])) for event in events if event[3]=='POINT_EXT']
        start,end=actual_points;P.need(start[2]==end[2]==0,'Actual explicit end extensions are not zero')
        width_rows=[row for row in rows if row[0]=='NDR' and row[1:3]==['WIDE',r['layer']]] if r['ndr'] else []
        if r['ndr']:width=int(width_rows[0][3])
        else:width=int(next(row[2] for row in rows if row[0:2]==['LAYER',r['layer']]))
        P.need(width>0 and width%2==0,'Pinned exact half-width derivation requires positive even DBU width')
        x0,y0,x1,y1=start[0],start[1],end[0],end[1];horizontal=y0==y1
        P.need((x0==x1) != horizontal,'Native single straight orthogonal body missing')
        box=[min(x0,x1),y0-width//2,max(x0,x1),y0+width//2] if horizontal else [x0-width//2,min(y0,y1),x0+width//2,max(y0,y1)]
        length=abs(x1-x0)+abs(y1-y0)
        P.need(box==r['body_dbu'] and length==r['length_um']*1000,'Derived Native body does not reconcile exact DEF/reference')
        derived.append(dict(net=r['name'],observed_points_with_extensions=actual_points,observed_native_width_dbu=width,
            source_derived_body_bbox_dbu=box,source_derived_long_dimension_minus_width_dbu=length-width,
            derived_quantity_not_observed_getLength=True))
    return dict(nets=30,ports=60,layers=5,wide_layer_rules=5,components=0,ITerms=0,special_wires=0,
        complete_actual_decoder_stream_checked=True,all_actual_zero_extensions_checked=True,
        all_global_full_endface_contacts_checked=True,observed_native_rows=all_rows,
        source_derived_shape_witnesses=derived,dbWire_getLength_numeric_measurement_claimed=False)
