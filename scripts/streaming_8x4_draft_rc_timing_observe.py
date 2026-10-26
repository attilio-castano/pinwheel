"""Pure HOST observation contracts for the unqualified draft-RC diagnostic."""
import re
from streaming_8x4_geometry import require
from streaming_tt_quality import inventory_context


def literal(value):
    require(type(value) is str and value and not any(c in value for c in '{}\\\n\r'),
        'Unsupported literal in exact STA observer; no guessed name translation')
    return '{'+value+'}'


def observer(inventory,odb_sha256,inventory_sha256):
    inventory_context(inventory)
    all_cells={};signals={};passives={}
    for name,row in sorted(inventory['instances'].items()):
        all_cells[name]=row['master']
        terms={pin:term for pin,term in row['terminals'].items() if term['signal_type'] in ('SIGNAL','CLOCK')}
        if terms:signals[name]=row['master']
        if terms and not any(term['direction']=='OUTPUT' for term in terms.values()):
            require(all(term['direction']=='INPUT' and term['net'] is not None for term in terms.values()),
                'Unsupported passive signal terminal')
            passives[name]=dict(master=row['master'],pins={pin:term['net'] for pin,term in sorted(terms.items())})
    require(signals and passives,'Nonempty actual signal and passive load inventory required')
    lines=['# Read-only queries and local bookkeeping only. No graph/model/constraint changes.',
        'puts "PINWHEEL_DRAFT_QUERY_BEGIN '+odb_sha256+' '+inventory_sha256+' $::env(_CURRENT_CORNER_NAME)"',
        'set expected_all [dict create]','set required_signal [dict create]']
    for name,master in all_cells.items():lines.append('dict set expected_all '+literal(name)+' '+literal(master))
    for name in signals:lines.append('dict set required_signal '+literal(name)+' 1')
    lines += ['set observed [dict create]','set observed_signal 0',
        'foreach cell [get_cells -hierarchical *] {',
        '  set name [get_full_name $cell]',
        '  if {[dict exists $observed $name] || ![dict exists $expected_all $name]} {error "Unknown/duplicate actual timing instance"}',
        '  dict set observed $name $cell',
        '  if {[get_property $cell ref_name] ne [dict get $expected_all $name]} {error "Actual timing master differs"}',
        '  if {[dict exists $required_signal $name]} {dict unset required_signal $name; incr observed_signal}',
        '}', 'if {[dict size $required_signal] != 0} {error "Actual signal-bearing instances omitted from timing NL"}']
    for index,(name,row) in enumerate(passives.items()):
        lines += ['if {![dict exists $observed '+literal(name)+']} {error "Actual passive load cell missing"}',
            'set selected [dict get $observed '+literal(name)+']',
            'set pin_index [dict create]',
            'foreach pin [get_pins -of_objects $selected] {dict set pin_index [get_full_name $pin] $pin}']
        for pin,net in row['pins'].items():
            full=literal(name+'/'+pin)
            lines += ['if {![dict exists $pin_index '+full+']} {error "Actual passive signal pin missing"}',
                'set nets [get_nets -of_objects [dict get $pin_index '+full+']]',
                'if {[llength $nets] != 1 || [get_full_name [lindex $nets 0]] ne '+literal(net)+'} {error "Actual passive signal net differs"}']
        lines.append(f'puts "PINWHEEL_DRAFT_PASSIVE {index} {len(row["pins"])}"')
    lines += ['set clocks [all_clocks]',
        'if {[llength $clocks] != 1} {error "Wrong actual clock inventory"}',
        'set clock [lindex $clocks 0]',
        'if {[get_property $clock name] ne "clk" || abs([get_property $clock period]-20.0)>1e-9 || ![get_property $clock is_propagated]} {error "Actual clock/period/propagation differs"}',
        'puts "PINWHEEL_DRAFT_CLOCK clk [get_property $clock period] [get_property $clock is_propagated]"',
        'puts "PINWHEEL_DRAFT_QUERY_COMPLETE '+odb_sha256+' '+inventory_sha256+' $observed_signal '+str(len(passives))+'"']
    expectation=dict(source_odb_sha256=odb_sha256,inventory_sha256=inventory_sha256,signal_instances=len(signals),
        passive_instances=len(passives),passive_pin_counts=[len(row['pins']) for row in passives.values()])
    return '\n'.join(lines)+'\n',expectation


def check_observer(log,expected,corner,clock_report,unpropagated):
    begin=f'PINWHEEL_DRAFT_QUERY_BEGIN {expected["source_odb_sha256"]} {expected["inventory_sha256"]} {corner}'
    complete=f'PINWHEEL_DRAFT_QUERY_COMPLETE {expected["source_odb_sha256"]} {expected["inventory_sha256"]} {expected["signal_instances"]} {expected["passive_instances"]}'
    require(log.splitlines().count(begin)==log.splitlines().count(complete)==1,'Missing/duplicate actual observer execution')
    rows=re.findall(r'^PINWHEEL_DRAFT_PASSIVE (\d+) (\d+)$',log,re.M)
    require([(int(a),int(b)) for a,b in rows]==list(enumerate(expected['passive_pin_counts'])),
        'Missing/extra actual passive load queries')
    clocks=re.findall(r'^PINWHEEL_DRAFT_CLOCK clk (\S+) (\S+)$',log,re.M)
    require(len(clocks)==1 and float(clocks[0][0])==20 and clocks[0][1] in ('1','true') and
        not unpropagated.strip() and re.findall(r'^Clock: (\S+)$',clock_report,re.M)==['clk'] and
        len(re.findall(r'^Period: 20(?:\.0*)?$',clock_report,re.M))==1,
        'Actual propagated clk/20ns or canonical raw clock reports differ')
    return dict(actual_graph_membership_checked=True,actual_passive_pin_net_bindings_checked=True,
        actual_signal_instances=expected['signal_instances'],actual_passive_instances=expected['passive_instances'],
        propagated_clock=True,clock_period_ns=20,canonical_unpropagated_report_empty=True,
        canonical_Propagated_label_ignored_due_to_pinned_source_typo=True)


def spef_coverage(text,inventory):
    """Decode only explicit standard NAME_MAP/CONN spelling; fail unsupported."""
    context,_=inventory_context(inventory)
    delimiters=re.findall(r'^\*DELIMITER\s+(\S+)\s*$',text,re.M)
    require(len(delimiters)==1 and len(delimiters[0])==1,'Missing/ambiguous SPEF delimiter')
    delimiter=delimiters[0];names={}
    matches=re.findall(r'^\*NAME_MAP\s*\n(.*?)(?=^\*[A-Z_]+(?:\s|$))',text,re.M|re.S)
    require(len(matches)==1,'Missing/ambiguous SPEF NAME_MAP')
    for line in matches[0].splitlines():
        if not line.strip():continue
        match=re.fullmatch(r'\*(\d+)\s+(\S+)',line)
        require(match is not None and match[1] not in names,'Unsupported/duplicate SPEF name map')
        names[match[1]]=match[2]
    def expand(value):
        match=re.fullmatch(r'\*(\d+)(.*)',value)
        if match:
            require(match[1] in names,'Unresolved SPEF name map reference');value=names[match[1]]+match[2]
        require('\\' not in value and '"' not in value,'Unsupported escaped SPEF name; preserve raw coverage failure')
        return value
    blocks=re.findall(r'^\*D_NET\s+(\S+)\s+(\S+)\s*\n(.*?)^\*END\s*$',text,re.M|re.S)
    require(blocks and len(blocks)==len(re.findall(r'^\*D_NET\s+',text,re.M)),'Incomplete SPEF net blocks')
    actual={};unknown=[];pin_count=0
    for token,cap,body in blocks:
        net=expand(token);require(net not in actual,'Duplicate SPEF net')
        sections=re.findall(r'^\*CONN\s*\n(.*?)(?=^\*(?:CAP|RES)\s*$|\Z)',body,re.M|re.S)
        require(len(sections)==1,'Missing/ambiguous SPEF CONN')
        points=set()
        for line in sections[0].splitlines():
            if not line.strip():continue
            match=re.fullmatch(r'\*(P|I)\s+(\S+)\s+[IOB](?:\s+.*)?',line)
            require(match is not None,'Unsupported SPEF connection row')
            name=expand(match[2])
            if match[1]=='P':point=('P',name)
            else:
                require(delimiter in name,'SPEF instance connection lacks pin delimiter');instance,pin=name.rsplit(delimiter,1);point=('I',instance,pin)
            require(point not in points,'Duplicate SPEF connection');points.add(point);pin_count+=1
        actual[net]=points
        if net not in context['nets']:unknown.append(net)
    missing_nets=[];missing_pins=[];extra_pins=[];consumed=0
    directions={name:row['direction'] for name,row in inventory['public_bterms'].items()}
    for net,row in context['nets'].items():
        if row['type'] in ('POWER','GROUND'):continue
        is_consumed=any(t['direction']=='INPUT' for t in row['terminals']) or any(directions[p]=='output' for p in row['ports'])
        expected={('P',name) for name in row['ports']}|{('I',t['instance'],t['pin']) for t in row['terminals']}
        if net in actual:
            missing_pins.extend([net,*point] for point in sorted(expected-actual[net]));extra_pins.extend([net,*point] for point in sorted(actual[net]-expected))
        if is_consumed:
            consumed+=1
            if net not in actual:missing_nets.append(net)
    require(consumed>0,'Vacuous consumed-net SPEF coverage')
    return dict(spef_nets=len(actual),spef_connections=pin_count,consumed_actual_nets=consumed,
        missing_consumed_nets=sorted(missing_nets),missing_connections=missing_pins,extra_connections=extra_pins,
        unknown_spef_nets=sorted(unknown),complete=not(missing_nets or missing_pins or extra_pins or unknown),
        model_qualified=False,qualified_timing=False,
        scope='Explicit SPEF net/CONN identity only; electrical completeness and model accuracy remain separate')
