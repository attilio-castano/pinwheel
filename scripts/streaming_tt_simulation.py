"""Actual OpenDB connectivity to a zero-delay public-pin simulator.

Every exported signal instance and every physical FF clock pin is retained.
The three pinned Liberty corners must agree on digital functions. Timing arcs,
parasitics and power-only masters are separate evidence, never simulated here.
"""
from collections import Counter
from copy import deepcopy
from dataclasses import asdict
from hashlib import sha256
import json
from pathlib import Path
import re

from streaming_mapped_liberty import require
from streaming_mapped_simulation import verilog_boolean
from streaming_tt_certificate import read_json, read_library, parse_graph, clock_cones
from streaming_tt_ties import CORNERS_SHA256

TOP='tt_um_pinwheel_streaming_ready_d2'
PORTS=dict(ui_in=('input',8),uo_out=('output',8),uio_in=('input',8),
    uio_out=('output',8),uio_oe=('output',8),ena=('input',1),clk=('input',1),rst_n=('input',1))
IDENTIFIER=re.compile(r'[A-Za-z_][A-Za-z0-9_$]*\Z')


def regular(path):
    path=Path(path).absolute()
    require(path.is_file() and not path.is_symlink(),'Expected a regular physical simulation input: '+str(path))
    return path


def digest(path):return sha256(regular(path).read_bytes()).hexdigest()


def functional_signature(cell):
    """No timing/area fields are used to establish digital corner agreement."""
    return dict(directions=cell.directions,output=cell.output,function=cell.function,
        sequential=cell.sequential,state_names=cell.state_names,clocked_on=cell.clocked_on,
        next_state=cell.next_state,clear=cell.clear)


def libraries(corners,used):
    require(type(corners) is dict and len(corners)==3 and all(type(name) is str for name in corners),
        'Exactly three explicitly pinned physical Liberty corners are required')
    require(all(type(item) is dict and set(item)=={'path','sha256'} for item in corners.values()) and
        {item['sha256'] for item in corners.values()}==CORNERS_SHA256,
        'Physical simulation requires the exact three retained Liberty pins')
    used=set(used);require(used,'Empty physical cell inventory')
    parsed={}
    for name,item in sorted(corners.items()):
        parsed[name]=read_library(regular(item['path']),used,expected_sha256=item['sha256'])
    selected=next(iter(parsed.values()))
    signature={name:functional_signature(cell) for name,cell in selected.cells.items()}
    require(all({name:functional_signature(cell) for name,cell in library.cells.items()}==signature
        for library in parsed.values()),'Physical Liberty corners disagree on actual digital behavior')
    return selected,dict(corners={name:dict(path=str(regular(corners[name]['path'])),sha256=library.sha256)
        for name,library in parsed.items()},used_cells=sorted(used),digital_functions_agree=True,
        actual_functions={name:asdict(cell) for name,cell in selected.cells.items()},
        boundary='Actual pinned three-corner Boolean/sequential functions; all timing arcs and electrical tables excluded.')


def validate_ports(document,top=TOP):
    require(type(document) is dict and set(document.get('modules',{}))=={top},
        'Physical simulator requires one actual flat OpenDB top')
    body=document['modules'][top]
    require(set(body.get('ports',{}))==set(PORTS),'Physical public interface differs')
    for name,(direction,width) in PORTS.items():
        port=body['ports'][name]
        require(port.get('direction')==direction and len(port.get('bits',[]))==width and
            port.get('offset',0)==0 and port.get('upto',0)==0,'Physical public port shape differs: '+name)
    return body


def verify_export(directory,*,receipt_sha256,database,reference,exporter_sha256):
    """Bind native-exported connectivity and its complete OpenDB inventory.

    Host paths may relocate the database/reference from the native container;
    their exact bytes must match the externally pinned native export receipt.
    """
    directory=Path(directory).absolute();receipt_path=regular(directory/'receipt.json')
    require(digest(receipt_path)==receipt_sha256,'Physical export receipt differs from pre-use pin')
    receipt=read_json(receipt_path)
    require(receipt.get('schema')=='pinwheel.streaming-tt-odb-export.v1' and
        receipt.get('read_only_database') is True and receipt.get('top')==TOP and
        set(receipt.get('artifacts_sha256',{}))=={'connectivity.json','inventory.json'},
        'Incomplete actual OpenDB export receipt')
    require(receipt.get('source_sha256')==exporter_sha256 and
        type(exporter_sha256) is str and re.fullmatch('[0-9a-f]{64}',exporter_sha256),
        'Native OpenDB exporter differs from the selected source')
    require(digest(database)==receipt.get('database_sha256') and digest(reference)==receipt.get('reference_sha256'),
        'Actual ODB/reference bytes do not match the native export')
    for name,value in receipt['artifacts_sha256'].items():
        require(digest(directory/name)==value,'Native OpenDB export artifact changed: '+name)
    document=read_json(directory/'connectivity.json');inventory=read_json(directory/'inventory.json')
    body=validate_ports(document)
    require(inventory.get('schema')=='pinwheel.streaming-tt-odb-inventory.v1' and inventory.get('top')==TOP,
        'Missing actual physical instance inventory')
    instances=inventory.get('instances',{});physical_only=inventory.get('physical_only_instances',{})
    require(type(instances) is dict and type(physical_only) is dict and
        set(instances)==set(body.get('cells',{}))|set(physical_only) and
        not (set(body['cells'])&set(physical_only)) and inventory.get('signal_model_instances')==len(body['cells']),
        'OpenDB functional/power-only instance partition differs')
    require(inventory.get('instance_counts')==dict(sorted(Counter(value['master'] for value in instances.values()).items())),
        'Actual OpenDB instance-count inventory differs')
    nets=inventory.get('nets',{});floating=inventory.get('unconnected_signal_outputs',{})
    expected_terms={}
    for name,port in body['ports'].items():
        for index,wire in enumerate(port['bits']):
            key=name if len(port['bits'])==1 else name+'['+str(index)+']'
            expected_terms[key]=(name,index,port['direction'],wire)
    terms=inventory.get('public_bterms',{})
    require(set(terms)==set(expected_terms),'Actual OpenDB public terminal set differs')
    for name,(port,index,direction,wire) in expected_terms.items():
        value=terms[name]
        require(value.get('port')==port and value.get('index')==index and value.get('direction')==direction and
            value.get('net') in nets and nets[value['net']].get('wire')==wire and
            nets[value['net']].get('signal_type') in ('SIGNAL','CLOCK'),
            'Actual OpenDB public pin/net differs')
    signal_nets={name:[value['wire']] for name,value in nets.items() if value.get('signal_type') in ('SIGNAL','CLOCK')}
    require({name:value.get('bits') for name,value in body.get('netnames',{}).items()}==signal_nets,
        'Actual OpenDB signal-net inventory differs')
    for name,cell in body['cells'].items():
        instance=instances[name]
        require(cell.get('type')==instance.get('master') and cell.get('parameters')=={},
            'Actual functional instance master/parameters differ')
        terminals={pin:value for pin,value in instance.get('terminals',{}).items()
            if value.get('signal_type') not in ('POWER','GROUND')}
        require(set(terminals)==set(cell.get('connections',{}))==set(cell.get('port_directions',{})),
            'Actual functional terminal inventory differs')
        for pin,terminal in terminals.items():
            require(terminal.get('signal_type') in ('SIGNAL','CLOCK') and
                terminal.get('direction','').lower()==cell['port_directions'][pin],
                'Actual signal terminal kind/direction differs')
            net=terminal.get('net')
            if net is None:
                require(terminal['direction']=='OUTPUT' and name+'/'+pin in floating,
                    'Disconnected functional input or untracked output')
                expected=floating[name+'/'+pin]
            else:
                require(net in nets and nets[net].get('signal_type') not in ('POWER','GROUND'),
                    'Functional pin is missing or connected to a power net')
                expected=nets[net]['wire']
            require(cell['connections'][pin]==[expected],'Actual OpenDB cell-pin wire differs')
    for name,master in physical_only.items():
        instance=instances[name]
        require(instance.get('master')==master and all(value.get('signal_type') in ('POWER','GROUND')
            for value in instance.get('terminals',{}).values()),'Excluded physical master has a functional terminal')
    require(digest(receipt_path)==receipt_sha256,'Export receipt changed while reading')
    return document,inventory,dict(receipt=str(receipt_path),receipt_sha256=receipt_sha256,
        database=str(regular(database)),database_sha256=digest(database),reference=str(regular(reference)),
        reference_sha256=digest(reference),artifacts_sha256=receipt['artifacts_sha256'],
        functional_instances=len(body['cells']),power_only_instances=len(physical_only),
        power_connectivity_signed_off=False)


def cell_models(library,used):
    """Emit the actual cell truth functions; every FF uses its connected CLK."""
    require(library.pinned and set(used)==set(library.cells),'Every actual used cell must be interpreted')
    lines=['`timescale 1ns/1ps','// Zero-delay digital functions from the exact pinned Liberty bodies.']
    for name in sorted(used):
        cell=library.cells[name]
        require(IDENTIFIER.fullmatch(name) and all(IDENTIFIER.fullmatch(pin) for pin in cell.directions),
            'Unsupported model identifier')
        lines.append('module '+name+'('+','.join(cell.directions)+');')
        for pin,direction in cell.directions.items():
            require(direction in ('input','output'),'Unsupported actual cell pin direction')
            lines.append(direction+(' reg ' if cell.sequential and direction=='output' else ' wire ')+pin+';')
        if cell.sequential:
            require(cell.output=='Q' and cell.directions==dict(Q='output',CLK='input',D='input',RESET_B='input') and
                cell.clocked_on==('variable','CLK') and cell.next_state==('variable','D') and
                cell.clear==('not',('variable','RESET_B')) and cell.function==('variable','IQ'),
                'Unsupported actual sequential behavior')
            lines.append("always @(posedge CLK or negedge RESET_B) if (!RESET_B) Q <= 1'b0; else Q <= D;")
        elif cell.output:lines.append('assign '+cell.output+' = '+verilog_boolean(cell.function)+';')
        else:require(all(direction=='input' for direction in cell.directions.values()),'Passive cell has an output')
        lines.append('endmodule')
    return '\n'.join(lines)+'\n'


def structural_verilog(document,library,*,top=TOP,expected_ff=6039):
    """Direct actual-pin emission, without Yosys optimization or clock cuts."""
    require(type(expected_ff) is int and expected_ff>0,'Explicit physical FF inventory required')
    body=validate_ports(document,top);graph=parse_graph(document,top,library)
    require(len(graph.flipflops)==expected_ff,'Actual physical FF inventory changed')
    clock=clock_cones(graph)  # Checks only; no graph rewrite or clock contraction.
    cells=body['cells'];require(not any(cell['type']=='$scopeinfo' for cell in cells.values()),
        'OpenDB signal export unexpectedly contains importer metadata')
    wires={wire for port in body['ports'].values() for wire in port['bits']}
    wires.update(wire for cell in cells.values() for bits in cell['connections'].values() for wire in bits)
    require(all(type(wire) is int and wire>=0 or wire in ('0','1') for wire in wires),
        'Functional unknown/unsupported physical literal')
    def atom(wire):return 'w'+str(wire) if type(wire) is int else "1'b"+wire
    def escaped(name):
        require(type(name) is str and name and not any(c.isspace() or c in '\\\x00' for c in name),
            'Unsafe actual Verilog instance identifier')
        return name if IDENTIFIER.fullmatch(name) else '\\'+name+' '
    lines=['`timescale 1ns/1ps','`default_nettype none',
        '// Actual ODB signal connectivity. Every FF CLK/reset remains connected to its physical net.',
        'module '+top+'('+','.join(body['ports'])+');']
    for name,port in body['ports'].items():
        width=len(port['bits']);shape='' if width==1 else '['+str(width-1)+':0] '
        lines.append(port['direction']+' wire '+shape+name+';')
    lines += ['wire w'+str(wire)+';' for wire in sorted(wire for wire in wires if type(wire) is int)]
    for name,port in body['ports'].items():
        for index,wire in enumerate(port['bits']):
            port_bit=name if len(port['bits'])==1 else name+'['+str(index)+']'
            lines.append('assign '+(atom(wire)+' = '+port_bit if port['direction']=='input' else port_bit+' = '+atom(wire))+';')
    records=[]
    for index,(name,cell) in enumerate(cells.items()):
        model=library.cells[cell['type']]
        ports=','.join('.'+pin+'('+atom(cell['connections'][pin][0])+')' for pin in model.directions)
        lines.append(cell['type']+' '+escaped(name)+'('+ports+');')
        records.append(dict(instance=name,cell=cell['type'],connections=cell['connections'],
            sequential=model.sequential,emitted_ordinal=index))
    lines += ['endmodule','`default_nettype wire','']
    return '\n'.join(lines),dict(top=top,physical_ff_bits=expected_ff,all_functional_instances_retained=True,
        instances=records,cell_counts=graph.counts,passive_loads=len(graph.passive_loads),
        actual_ff_clock_pins={ff.name:dict(cell=ff.cell,clk=ff.clock,reset_b=ff.reset_b,d=ff.d,q=ff.q)
            for ff in graph.flipflops},positive_clock_roots_checked=len(clock),clock_contraction=False)


def sampler_mutation(document,library,binding,*,top=TOP):
    """Mutate actual stage2[0] FF D, retaining its real clock/reset and all cells.

    The external semantic mapping is separately proof-bound by the caller.
    Actual Q/D/CLK/reset pin checks below prevent a name-only substitution.
    """
    require(type(binding) is dict and set(binding)=={'stage1','stage2'},'Both semantic sampler FF bindings required')
    graph=parse_graph(document,top,library);flops={ff.name:ff for ff in graph.flipflops}
    body=document['modules'][top]
    selected={}
    for stage in ('stage1','stage2'):
        item=binding[stage]
        require(type(item) is dict and item.get('component')=='core-d2' and item.get('register')=='r_'+stage and
            item.get('index')==0 and type(item.get('index')) is int and item.get('cell') in body['cells'],
            'Invalid semantic physical sampler binding')
        name=item['cell'];cell=body['cells'][name];model=library.cells.get(cell['type'])
        require(model is not None and model.sequential and
            all(cell['connections'].get(pin)==[item[key]] for pin,key in [('Q','q'),('D','d'),('CLK','clock'),('RESET_B','reset_b')]),
            'Sampler binding differs from actual physical FF pins')
        actual=[ff for ff in graph.flipflops if ff.q==item['q']]
        require(len(actual)==1 and actual[0].cell==cell['type'] and actual[0].d==item['d'] and
            actual[0].clock==item['clock'] and actual[0].reset_b==item['reset_b'],
            'Sampler Q is not the actual unique physical state bit')
        selected[stage]=(name,cell,item)
    first,second=selected['stage1'],selected['stage2']
    require(first[0]!=second[0] and first[1]['connections']['D']!=second[1]['connections']['D'],
        'Actual physical sampler mutation is vacuous')
    changed=deepcopy(document)
    changed['modules'][top]['cells'][second[0]]['connections']['D']=deepcopy(first[1]['connections']['D'])
    # Parse again: the mutant must remain a complete actual all-state circuit.
    after=parse_graph(changed,top,library)
    require(len(after.flipflops)==len(graph.flipflops) and after.counts==graph.counts,'Mutation changed the state/cell inventory')
    return changed,dict(operation='Replace actual physical stage2[0] FF D pin by stage1[0] actual D root',
        changed_cell=second[0],source_cell=first[0],pin='D',before=second[1]['connections']['D'],
        after=first[1]['connections']['D'],changed_ff_pins=1,semantic_binding=binding,
        actual_clock_pin=second[2]['clock'],actual_reset_b_pin=second[2]['reset_b'],
        boundary='One physical FF D-pin mutation. Actual clock tree is unchanged; public first-BUSY timing must distinguish it.')
