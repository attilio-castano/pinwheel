"""Strict public decoder, actual cut boxes and endpoint metadata for 45 nets."""
from decimal import Decimal as D
import streaming_8x4_model24_via_geometry as G
need=G.need


def tcl():
    return '''puts "MODEL24_VIA_VERSION_BEGIN"
puts [ord::openroad_version]
puts "MODEL24_VIA_VERSION_END"
read_lef tech.lef
read_def fixture.def
proc snapshot {path} {
 set f [open $path w]
 fconfigure $f -buffering line
 set b [ord::get_db_block]
 set tech [[ord::get_db] getTech]
 puts $f [join [list BLOCK [$tech getDbUnitsPerMicron] [llength [$b getInsts]] [llength [$b getITerms]] [llength [$b getNets]] [llength [$b getBTerms]] [llength [$b getNonDefaultRules]] [llength [$b getVias]]] "\t"]
 foreach m {Metal1 Metal2 Metal3 Metal4 TopMetal1} {
  set l [$tech findLayer $m]
  puts $f [join [list LAYER $m [$l getWidth] [$l getDirection] [$l getResistance]] "\t"]
 }
 foreach m {Via1 Via2 Via3} {puts $f [join [list CUT $m [[$tech findLayer $m] getResistance]] "\t"]}
 foreach ndr [$b getNonDefaultRules] {
  foreach m {Metal1 Metal2 Metal3 Metal4 TopMetal1} {
   set lr [$ndr getLayerRule [$tech findLayer $m]]
   puts $f [join [list NDR [$ndr getName] $m [$lr getWidth] [$lr getSpacing]] "\t"]
  }
 }
 foreach {name kind} {Via1_XY TECH Via1_YY TECH Via2_YX TECH Via3_XY TECH via1_2_1000_440_1_2_410_410 BLOCK via2_3_1000_2100_4_2_480_480 BLOCK via3_4_2100_2100_4_4_480_480 BLOCK} {
  if {$kind eq "TECH"} {set via [$tech findVia $name]} else {set via [$b findVia $name]}
  if {$via eq "NULL"} {error "Missing exact via family"}
  puts $f [join [list VIADEF $name $kind [[$via getBottomLayer] getName] [[$via getTopLayer] getName]] "\t"]
  foreach box [$via getBoxes] {puts $f [join [list VIABOX $name [[$box getTechLayer] getName] [$box xMin] [$box yMin] [$box xMax] [$box yMax]] "\t"]}
 }
 foreach net [$b getNets] {
  set rule [$net getNonDefaultRule];set name -
  if {$rule ne "NULL"} {set name [$rule getName]}
  set wire [$net getWire]
  if {$wire eq "NULL"} {error "Missing actual wire"}
  set netname [$net getName]
  puts $f [join [list NET $netname $name [llength [$net getITerms]] [llength [$net getBTerms]] [llength [$net getSWires]] [$net isSpecial] [$net getSigType]] "\t"]
  set decoder [odb::dbWireDecoder];$decoder begin $wire;set point {UNBOUND UNBOUND UNBOUND}
  for {set index 0} {$index < 32} {incr index} {
   set op [$decoder next]
   if {$op == $odb::dbWireDecoder_PATH} {
    puts $f [join [list DECODE $netname $index PATH [[$decoder getLayer] getName] [$decoder getWireType]] "\t"]
   } elseif {$op == $odb::dbWireDecoder_RULE} {
    set lr [$decoder getRule]
    puts $f [join [list DECODE $netname $index RULE [[$lr getNonDefaultRule] getName] [[$lr getLayer] getName] [$lr getWidth] [$lr getSpacing]] "\t"]
   } elseif {$op == $odb::dbWireDecoder_POINT_EXT} {
    set point [$decoder getPoint_ext]
    if {[llength $point] != 3} {error "Missing numeric point triplet"}
    foreach value $point {if {![string is integer -strict $value]} {error "Noninteger point"}}
    puts $f [join [concat [list DECODE $netname $index POINT_EXT] $point] "\t"]
   } elseif {$op == $odb::dbWireDecoder_VIA} {
    puts $f [join [list DECODE $netname $index VIA [[$decoder getVia] getName] [[$decoder getLayer] getName]] "\t"]
   } elseif {$op == $odb::dbWireDecoder_TECH_VIA} {
    puts $f [join [list DECODE $netname $index TECH_VIA [[$decoder getTechVia] getName] [[$decoder getLayer] getName]] "\t"]
   } elseif {$op == $odb::dbWireDecoder_BTERM} {
    set t [$decoder getBTerm]
    puts $f [join [list DECODE $netname $index BTERM [$t getName] [[$t getNet] getName] [$t getIoType] [$t getSigType] [lindex $point 0] [lindex $point 1]] "\t"]
   } elseif {$op == $odb::dbWireDecoder_END_DECODE} {
    puts $f [join [list DECODE $netname $index END_DECODE] "\t"];break
   } else {error "Undeclared actual decoder opcode $op"}
  }
  if {$index >= 32} {error "Unterminated decoder"}
 }
 foreach t [$b getBTerms] {
  puts $f [join [list BTERM [$t getName] [[$t getNet] getName] [$t getIoType] [$t getSigType] [llength [$t getBPins]]] "\t"]
  foreach pin [$t getBPins] {foreach box [$pin getBoxes] {puts $f [join [list BPIN [$t getName] [[$box getTechLayer] getName] [$box xMin] [$box yMin] [$box xMax] [$box yMax] [$pin getPlacementStatus]] "\t"]}}
 }
 close $f
}
snapshot before.tsv
write_def before.def
define_process_corner -ext_model_index 0 via_arithmetic
extract_parasitics -lef_res -ext_model_file rules.txt -no_merge_via_res -version 1.0
write_spef result.spef
write_def after.def
snapshot after.tsv
puts "MODEL24_VIA_TERMINAL"
exit
'''


def globals_expected(defs,sheets,cuts):
    rows=[['BLOCK','1000','0','0','45','90','1','3']]
    for m in G.METALS:rows.append(['LAYER',m,str(G.DEFAULT[m]),G.OLD.DIRECTIONS[m],str(sheets[m])])
    for m in ('Via1','Via2','Via3'):rows.append(['CUT',m,str(cuts[m])])
    for m in G.METALS:rows.append(['NDR','ACTUAL_PG',m,str(G.PG[m]),str(G.PG[m])])
    for name in G.FAMILIES:
        row=defs[name];rows.append(['VIADEF',name,'BLOCK'if name in G.GENERATED else'TECH',row['layers'][0],row['layers'][2]])
        for layer,boxes in G.boxes(row).items():
            for box in boxes:rows.append(['VIABOX',name,layer,*map(str,box)])
    for r in G.cases(defs):
        rows.append(['NET',r['name'],'ACTUAL_PG'if r['pg']else'-','0','2','0','0','SIGNAL'])
        for p in G.ports(r):
            rows += [['BTERM',p['name'],r['name'],p['direction'],'SIGNAL','1'],['BPIN',p['name'],p['layer'],*map(str,p['global_box']),'FIRM']]
    return rows


def events(row,post):
    name=row['name'];m=row['layers'][0];result=[['PATH',m,'ROUTED']]
    if row['pg']:result.append(['RULE','ACTUAL_PG',m,str(G.PG[m]),str(G.PG[m])])
    for i,p in enumerate(row['points']):
        result.append(['POINT_EXT',*map(str,p),'0'])
        if post and i in (0,len(row['points'])-1):
            suffix,direction=('A','INPUT')if i==0 else('B','OUTPUT')
            result.append(['BTERM',name+'_'+suffix,name,direction,'SIGNAL',*map(str,p)])
        if row['family']and i==1:result.append(['VIA'if row['pg']else'TECH_VIA',row['family'],row['layers'][1]])
    result.append(['END_DECODE']);return [['DECODE',name,str(i),*v]for i,v in enumerate(result)]


def snapshot(text,defs,sheets,cuts,post):
    rows=[x.split('\t')for x in text.splitlines()];global_rows=[];decoded={}
    for r in rows:
        need(r and r[0]in {'BLOCK','LAYER','CUT','NDR','NET','VIADEF','VIABOX','BTERM','BPIN','DECODE'},'Foreign native snapshot record')
        if r[0]=='DECODE':need(len(r)>=4,'Truncated decoder');decoded.setdefault(r[1],[]).append(r)
        else:global_rows.append(r)
    def normal(row):
        r=list(row)
        if r[0]=='LAYER':need(len(r)==5,'Layer record arity');r[4]=str(D(r[4]).normalize())
        if r[0]=='CUT':need(len(r)==3,'Cut record arity');r[2]=str(D(r[2]).normalize())
        return r
    need(sorted(map(normal,global_rows))==sorted(map(normal,globals_expected(defs,sheets,cuts))),'Complete actual native global/via-box/port inventory differs')
    cases=G.cases(defs);need(set(decoded)=={r['name']for r in cases},'Decoder net membership differs')
    derived=[]
    for row in cases:
        actual=decoded[row['name']];need(actual==events(row,post),'Complete public decoder point/rule/via/terminal stream differs: '+row['name'])
        points=[list(map(int,r[4:]))for r in actual if r[3]=='POINT_EXT']
        widths=[]
        for layer in row['layers']:
            native=next(r for r in global_rows if r[:3]==['NDR','ACTUAL_PG',layer])if row['pg']else next(r for r in global_rows if r[:2]==['LAYER',layer])
            widths.append(int(native[3]if row['pg']else native[2]))
        lengths=[abs(b[0]-a[0])+abs(b[1]-a[1])for a,b in zip(points,points[1:])if a[:2]!=b[:2]]
        need(len(lengths)==len(widths)and all(v==row['length_um']*1000 for v in lengths),'Observed exact zero-extension legs differ')
        derived.append(dict(net=row['name'],observed_points_with_extensions=points,observed_widths_dbu=widths,
            source_derived_leg_lengths_dbu=lengths,derived_not_getLength_API=True))
    return dict(observed_global_rows=global_rows,observed_complete_decoder_rows=decoded,
        source_derived_body_witnesses=derived,
        complete_public_stream_checked=True,internal_RC_property_operands_observed=False,raw_wire_bytes_unchanged_claimed=False)


def pair(before,after,defs,sheets,cuts):
    a=snapshot(before,defs,sheets,cuts,False);b=snapshot(after,defs,sheets,cuts,True)
    need(a['observed_global_rows']==b['observed_global_rows'],'Extraction reordered/changed complete global inventory')
    return dict(before=a,after=b,exactly_two_observed_endpoint_BTERMs_per_net=True,
        complete_geometric_projection_and_def_unchanged=True,all_via_boxes_and_zero_extensions_observed=True)
