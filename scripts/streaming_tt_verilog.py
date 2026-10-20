"""A separately bound structural-Verilog grammar adapter for pinned OpenSTA.

Internal ``wire signed`` modifiers are removed, then hierarchy is flattened
without optimization to materialize constant child outputs. Native pre/post
imports must retain every actual cell/pin, semantic FF, D and output.
This is an importer binding, not post-PNR equivalence or timing acceptance.
"""
from collections import Counter
import re
import subprocess
import time
from pathlib import Path

from streaming_mapped_flow import quoted, state_inventory
from streaming_mapped_netlist import expand_hierarchy, parse_mapped
from streaming_tt_physical import read, regular, require, sha, write


def normalize(text):
    # A structural emitter has no behavioral blocks. Refuse broader syntax
    # rather than silently changing the signedness of arithmetic expressions.
    def code_only(value):
        return re.sub(r'/\*.*?\*/|//[^\n]*',
            lambda match:''.join('\n' if c == '\n' else ' ' for c in match.group()),value,flags=re.S)
    code = code_only(text)
    require(not re.search(r'\b(always|initial|function|task|generate|integer|reg|logic)\b', code),
        'Physical Verilog adapter requires structural cell/alias syntax')
    matches = list(re.finditer(r'(?m)^([ \t]*wire[ \t]+)signed[ \t]+(?=\[)',code))
    lines = [text.count('\n',0,m.start())+1 for m in matches]
    result = text
    for match in reversed(matches): result = result[:match.start(1)+len(match.group(1))]+result[match.end():]
    stripped = code_only(result)
    require(not re.search(r'\bsigned\b', stripped), 'Unsupported signed Verilog syntax')
    return result, dict(removed_internal_wire_signed=len(lines), declaration_lines=lines)


def structure(graph, state_labels, pool):
    """Compare full tuples with one shared interner; no digest-only equality."""
    require(set(state_labels) == graph.state_bits and len(set(state_labels.values())) == len(state_labels),
        'Incomplete or aliased physical Verilog state binding')
    def intern(key):
        if key not in pool: pool[key] = len(pool)
        return pool[key]
    values = {bit:intern(('input', name, index)) for name,bits in graph.inputs.items()
        for index,bit in enumerate(bits)}
    values.update({bit:intern(('state', *label)) for bit,label in state_labels.items()})
    def wire(bit):
        if type(bit) is str:
            require(bit in ('0','1'), 'Unknown structural literal')
            return intern(('literal',bit))
        require(bit in values, 'Missing topological structural driver')
        return values[bit]
    cells = Counter()
    for gate in graph.gates:
        model = graph.library.cells[gate.cell]
        value = intern(('cell',gate.cell,model.output,tuple((pin,wire(gate.connections[pin]))
            for pin in sorted(model.directions) if model.directions[pin] == 'input')))
        values[gate.output] = value; cells[value] += 1
    return dict(inputs={name:len(bits) for name,bits in graph.inputs.items()}, cells=cells,
        flops={state_labels[ff.q]:dict(cell=ff.cell,d=wire(ff.d),clock=wire(ff.clock),reset=ff.reset_b)
            for ff in graph.flipflops},
        outputs={name:tuple(wire(bit) for bit in bits) for name,bits in graph.outputs.items()})


def port_shapes(data, top):
    result = {}
    for name,port in data['modules'][top]['ports'].items():
        require(port['direction'] in ('input','output'), 'Unsupported physical port direction')
        result[name] = dict(direction=port['direction'],width=len(port['bits']),
            offset=port.get('offset',0),upto=port.get('upto',0),signed=port.get('signed',0))
    return result


def flat_labels(candidate, data, graph, library):
    """Names propose semantic state pairs; actual Q membership checks all bits."""
    source = read(candidate['netlist']); top = candidate['top']
    engines = [(name,value) for name,value in source['modules'][top]['cells'].items()
        if value['type'] in source['modules'] and all(any(child['type'] == component_top
            for child in source['modules'][value['type']]['cells'].values())
            for component_top in candidate['component_tops'].values())]
    require(len(engines) == 1, 'Ambiguous source semantic component hierarchy')
    engine, package = engines[0][0], source['modules'][engines[0][1]['type']]
    aliases = expand_hierarchy(data,top,library)['modules'][top]['netnames']
    labels = {}; rows = []; groups = {}
    for row in candidate['semantic_q_map']['rows']:
        groups.setdefault((row['component'],row['register']),[]).append(row['index'])
    by_q = {ff.q:ff for ff in graph.flipflops}
    for (component,register),indices in sorted(groups.items()):
        require(component in candidate['component_tops'], 'Unknown source semantic component')
        component_top = candidate['component_tops'][component]
        children = [name for name,value in package['cells'].items() if value['type'] == component_top]
        require(len(children) == 1, 'Ambiguous source semantic component')
        width = len(source['modules'][component_top]['netnames'][register]['bits'])
        require(sorted(indices) == list(range(width)), 'Missing source semantic register bit')
        name = '.'.join((engine,children[0],register))
        require(name in aliases and len(aliases[name]['bits']) == width, 'Missing or resized flat semantic register alias')
        for index,bit in enumerate(aliases[name]['bits']):
            require(type(bit) is int and bit in by_q and bit not in labels,
                'Flat semantic register alias is not a unique actual FF Q')
            labels[bit] = (component,register,index); ff = by_q[bit]
            rows.append(dict(component=component,register=register,index=index,q=bit,d=ff.d,
                clock=ff.clock,cell=ff.cell,ff=ff.name,alias=name))
    require(set(labels) == graph.state_bits and len(labels) == 6039,
        'Flat physical Verilog lost or added declared state')
    return labels,rows


def derive(candidate, destination, library, actual_qmap):
    """Create a fresh derivative and independently import original/normalized SV.

    ``actual_qmap`` is the caller's existing checked semantic-Q reconstruction;
    it receives the imported JSON, its strict graph and new state inventories.
    """
    destination = Path(destination); destination.mkdir(parents=True, exist_ok=False)
    original = regular(candidate['verilog']); yosys = regular(candidate['yosys'])
    text, modifiers = normalize(original.read_text())
    normalized = destination/'normalized.v'; normalized.write_text(text)
    output = destination/'physical.v'; emitted_flat = destination/'emitted-flat.v'
    source = read(candidate['netlist']); top = candidate['top']
    script = destination/'reimport.ys'; commands = []
    for label, path in [('original',original),('normalized',normalized)]:
        if label != 'original': commands.append('design -reset')
        commands.extend(('read_liberty -lib '+quoted(candidate['library']),
            'read_verilog -sv '+quoted(path), 'hierarchy -check -top '+top,
            'check -assert', 'write_json '+quoted(destination/(label+'.json'))))
    # Flatten hierarchy only. In particular no opt/clean/FF/FSM/technology pass
    # is allowed. This materializes constant child outputs before OpenROAD.
    commands.extend(('flatten','check -assert','write_json '+quoted(destination/'flat.json'),
        'write_verilog -noattr -noexpr '+quoted(emitted_flat)))
    script.write_text('\n'.join(commands)+'\n')
    frozen = {str(path):sha(path) for path in (original,yosys,normalized,script,
        regular(candidate['netlist']),regular(candidate['library']))}
    frozen.update({str(regular(path)):sha(path) for path in candidate['component_sources'].values()})
    report = dict(schema='pinwheel.streaming-tt-physical-verilog.v1', passed=False, qualified=False,
        physical_acceptance_claim=False, transform='internal_wire_signed_modifier_then_native_flatten_only',
        source_verilog=str(original), source_verilog_sha256=sha(original),
        physical_verilog=str(output), **modifiers,
        input_sha256_before=dict(frozen), command=dict(argv=[str(yosys),'-Q','-T','-s',str(script)],
            status='intent',timeout_seconds=180))
    receipt = destination/'report.json'; write(receipt,report); started = time.monotonic()
    try:
        log_path = destination/'reimport.log'
        with log_path.open('w') as log:
            process = subprocess.run(report['command']['argv'],stdout=log,stderr=subprocess.STDOUT,timeout=180)
        report['command'].update(status='completed',exit_code=process.returncode,log_sha256=sha(log_path))
        require(process.returncode == 0, 'Physical structural Verilog reimport failed')
        flat_text,flat_modifiers = normalize(regular(emitted_flat).read_text())
        output.write_text(flat_text)
        second = destination/'flat-reimport.ys'
        second.write_text('\n'.join(('read_liberty -lib '+quoted(candidate['library']),
            'read_verilog -sv '+quoted(output),'hierarchy -check -top '+top,'check -assert',
            'write_json '+quoted(destination/'flat-reimport.json')))+'\n')
        frozen.update({str(path):sha(path) for path in (output,emitted_flat,second,
            regular(destination/'original.json'),regular(destination/'normalized.json'),regular(destination/'flat.json'))})
        report.update(physical_verilog_sha256=sha(output),flat_signed_modifiers=flat_modifiers,
            flat_reimport=dict(argv=[str(yosys),'-Q','-T','-s',str(second)],status='intent',
                input_sha256_before=dict(frozen),timeout_seconds=180))
        write(receipt,report)
        second_log = destination/'flat-reimport.log'
        with second_log.open('w') as log:
            second_process = subprocess.run(report['flat_reimport']['argv'],stdout=log,stderr=subprocess.STDOUT,timeout=180)
        report['flat_reimport'].update(status='completed',exit_code=second_process.returncode,log_sha256=sha(second_log))
        require(second_process.returncode == 0, 'Flat physical Verilog reimport failed')
        frozen[str(regular(destination/'flat-reimport.json'))] = sha(destination/'flat-reimport.json')
        report['interpreted_input_sha256_before'] = dict(frozen)
        write(receipt,report)
        pool = {}; expected_ports = port_shapes(source,top)
        expected = structure(parse_mapped(source,top,library),
            {r['candidate_q']:(r['component'],r['register'],r['index']) for r in candidate['semantic_q_map']['rows']},pool)
        for label in ('original','normalized'):
            data = read(destination/(label+'.json')); graph = parse_mapped(data,top,library)
            require(port_shapes(data,top) == expected_ports, 'Physical Verilog public port shape changed')
            inventories = {name:state_inventory(read(candidate['component_sources'][name]),data,component_top,library)
                for name,component_top in candidate['component_tops'].items()}
            qmap = actual_qmap(data,graph,inventories,library)
            labels = {r['candidate_q']:(r['component'],r['register'],r['index']) for r in qmap['rows']}
            require(structure(graph,labels,pool) == expected,
                'Physical Verilog differs in actual cell/pin, state, clock, D or public I/O structure')
            write(destination/(label+'-semantic-q-map.json'),qmap)
        for label in ('flat','flat-reimport'):
            data = read(destination/(label+'.json')); graph = parse_mapped(data,top,library)
            require(all(cell['type'] in library.cells or cell['type']=='$scopeinfo'
                for cell in data['modules'][top]['cells'].values()),
                'Physical flat top retains hierarchical instances')
            require(port_shapes(data,top) == expected_ports, 'Flat physical Verilog public port shape changed')
            labels,rows = flat_labels(candidate,data,graph,library)
            require(structure(graph,labels,pool) == expected,
                'Flat physical Verilog differs in actual cell/pin, state, clock, D or public I/O structure')
            write(destination/(label+'-semantic-q-map.json'),dict(semantic_ff_bits=len(rows),rows=rows))
        require(all(sha(regular(path)) == value for path,value in frozen.items()),
            'Physical Verilog derivation input changed')
        report.update(passed=True, semantic_ff_bits=len(expected['flops']), structural_nodes=len(pool),
            exact_tuple_comparison=True, all_actual_cells_and_pins=True, all_ff_d_clock_reset_and_io=True,
            full_public_port_shape=True,
            source_unchanged=True, original_json_sha256=sha(destination/'original.json'),
            normalized_json_sha256=sha(destination/'normalized.json'),
            flat_json_sha256=sha(destination/'flat.json'),flat_reimport_json_sha256=sha(destination/'flat-reimport.json'),
            flatten_only=True,flat_native_reimport=True)
    except BaseException as error:
        report['error'] = type(error).__name__+': '+str(error)
        raise
    finally:
        report['elapsed_seconds'] = round(time.monotonic()-started,3); write(receipt,report)
    return output, report
