"""Matched standard-cell cost metrics for the complete sampled-pin packages.

This measures saved synthesis artifacts. It does not certify ABC equivalence,
physical timing, routing, macro area or electrical behavior. Declared storage
and directly named surviving FFs are kept separate because optimization may
merge state or recode FSMs. Total physical FF and cell-area counts include all
mapped state, including any optimizer state without a source register name.
"""
from collections import Counter, deque
import hashlib
import json
import math
from pathlib import Path
import re
import shlex

LIBRARY_SHA256 = '34163f3e7de9f854afac57332ba06f1739b78e7ac35660a8a5ddd39c570124ad'
MACRO = 'RM_IHPSG13_1P_64x64_c2_bm_bist'
CONSTRAINTS = 'set_driving_cell sg13cmos5l_buf_2\nset_load 10\n'
TIMING_BOUNDARY = ('ABC stime -p combinational Liberty estimate at the pinned typical corner, '
    'with sg13cmos5l_buf_2 input drive, output load10 fF and WireLoad=none. '
    'FF and excluded macro boundaries are cut. No clock-to-Q, setup, clock tree, '
    'placement/routing, parasitics, physical timing/signoff or guaranteed Fmax claim.')
BOUNDARY = ('Matched typical CMOS5L saved synthesis cost with identical Yosys/ABC settings '
    'and the same TT pad envelope. These are distinct host protocols and instruction sets, '
    'not functionally equivalent replacements: the old ISA includes wait/qualification/branch '
    'facilities absent from the new pulse/stream microcore. Area is the sum of Liberty cell areas. Sequential cells include '
    'program, FIFO, shifter, partial RX, current cell, frame, CRC, staging, reply/replay and '
    'export-custody state. The longest combinational cell path is an unweighted graph metric. '
    'ABC stime -p also supplies a separate combinational Liberty delay estimate with '
    'FF/macro boundaries cut and the declared input-drive/output-load constraints; '
    'it excludes clock-to-Q, setup, clocks and parasitics and implies no guaranteed Fmax. '
    'Synthesis functional preservation is trusted here; '
    'no mapped equivalence, placement, routing, parasitics, macro area or electrical claim.')

NUMBER = r'[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?'
ABC_SUMMARY = re.compile(r'ABC:\s+WireLoad\s*=\s*"([^"]+)"\s+Gates\s*=\s*(\d+)\s+'
    r'\([^()\n]*\)\s+Cap\s*=\s*(' + NUMBER + r')\s+ff\s+\([^()\n]*\)\s+'
    r'Area\s*=\s*(' + NUMBER + r')\s+\([^()\n]*\)\s+'
    r'Delay\s*=\s*(' + NUMBER + r')\s+ps\s+\([^()\n]*\)\s*')
ABC_PATH = re.compile(r'ABC:\s+Path\s+(\d+)\s+--\s+(\d+)\s*:\s*(\d+)\s+(\d+)\s+'
    r'(\S+)\s+A\s*=\s*(' + NUMBER + r')\s+Df\s*=\s*(' + NUMBER + r')\s+'
    r'(' + NUMBER + r')\s+ps\s+S\s*=\s*(' + NUMBER + r')\s+ps\s+'
    r'Cin\s*=\s*(' + NUMBER + r')\s+ff\s+Cout\s*=\s*(' + NUMBER + r')\s+ff\s+'
    r'Cmax\s*=\s*(' + NUMBER + r')\s+ff\s+G\s*=\s*(\d+)\s*')
ABC_ENDPOINTS = re.compile(r'ABC:\s+Start-point\s*=\s*(pi\d+)\s+\((.+)\)\.\s+'
    r'End-point\s*=\s*(po\d+)\s+\((.+)\)\.\s*')


def parse_abc_timing(log, *, constraints=CONSTRAINTS):
    """Parse the one actual pinned-ABC stime -p summary and its complete path."""
    if type(log) is not str or constraints != CONSTRAINTS:
        raise ValueError('ABC timing requires the matched buffer/load constraints and native command text')
    lines = log.splitlines()
    drivers = [k for k, line in enumerate(lines) if line.startswith('ABC: Setting driving cell')]
    loads = [k for k, line in enumerate(lines) if line.startswith('ABC: Setting output load')]
    stime = [k for k, line in enumerate(lines) if re.match(r'ABC:\s+\+\s+stime\b', line)]
    summaries = [k for k, line in enumerate(lines) if re.match(r'ABC:\s+WireLoad\b', line)]
    path_rows = [k for k, line in enumerate(lines) if re.match(r'ABC:\s+Path\b', line)]
    endpoints = [k for k, line in enumerate(lines) if re.match(r'ABC:\s+Start-point\b', line)]
    if len(summaries) != 1 or len(endpoints) != 1 or len(path_rows) < 2:
        raise ValueError('ABC timing needs one unambiguous summary, endpoint pair and nonempty actual cell path')
    first, last = summaries[0], endpoints[0]
    if (len(drivers) != 1 or len(loads) != 1 or len(stime) != 1 or
            not re.fullmatch(r'ABC: Setting driving cell to be "sg13cmos5l_buf_2"\.\s*', lines[drivers[0]]) or
            not re.fullmatch(r'ABC: Setting output load to be 10\.0+\.\s*', lines[loads[0]]) or
            not re.fullmatch(r'ABC:\s+\+\s+stime\s+-p\s*', lines[stime[0]]) or
            not drivers[0] < loads[0] < stime[0] < first):
        raise ValueError('ABC timing lacks the actual matched drive/load and stime -p command context')
    summary, endpoint = ABC_SUMMARY.fullmatch(lines[first]), ABC_ENDPOINTS.fullmatch(lines[last])
    if not summary or not endpoint or path_rows != list(range(first + 1, last)):
        raise ValueError('Malformed ABC timing units, endpoint pair or discontinuous critical path')
    wire_load, gates, cap, area, delay = summary.groups()
    cap, area, delay = map(float, (cap, area, delay))
    if (wire_load != 'none' or int(gates) <= 0 or
            not all(math.isfinite(value) for value in (cap, area, delay)) or
            cap < 0 or area <= 0 or delay <= 0):
        raise ValueError('ABC delay must be finite and positive with the declared no-wire-load model')
    parsed = []
    for index, row in enumerate(path_rows):
        match = ABC_PATH.fullmatch(lines[row])
        if not match or int(match[1]) != index:
            raise ValueError('Malformed or reordered ABC critical path rows')
        cell, values = match[5], list(map(float, match.group(6, 7, 8, 9, 10, 11, 12)))
        if (not all(math.isfinite(value) for value in values) or
                (cell != 'pi' if index == 0 else
                    not cell.startswith('sg13cmos5l_') or cell.startswith('sg13cmos5l_df')) or
                values[0] < 0 or any(value < 0 for value in values[3:])):
            raise ValueError('Invalid ABC critical path cell or finite Liberty values')
        parsed.append(dict(index=index, node=int(match[2]), cell=cell, arrival_ps=values[1]))
    if (parsed[-1]['arrival_ps'] <= 0 or abs(parsed[-1]['arrival_ps'] - delay) > 0.11 or
            len(parsed) - 1 > int(gates)):
        raise ValueError('ABC critical path does not match its rounded delay summary')
    summary_text, path_text = lines[first] + '\n', '\n'.join(lines[k] for k in [*path_rows, last]) + '\n'
    return dict(engine='ABC stime -p', delay_ps=delay, wire_load=wire_load,
        input_driver='sg13cmos5l_buf_2', output_load_ff=10,
        liberty_sha256=LIBRARY_SHA256, boundary=TIMING_BOUNDARY,
        path_cells=len(parsed) - 1, path=parsed,
        start_point=endpoint[1], start_signal=endpoint[2], end_point=endpoint[3], end_signal=endpoint[4],
        context_text='\n'.join(lines[k] for k in (drivers[0], loads[0], stime[0])) + '\n',
        summary_text=summary_text, path_text=path_text)


def check_abc_timing(timing, artifacts):
    if type(timing) is not dict:
        raise ValueError('Actual ABC combinational Liberty timing estimate is mandatory')
    parsed = parse_abc_timing(timing.get('context_text', '') + timing.get('summary_text', '') + timing.get('path_text', ''))
    if any(timing.get(key) != value for key, value in parsed.items()):
        raise ValueError('ABC timing fields differ from the retained native summary/path text')
    for field, name in [('context_text', 'abc-timing-context.txt'),
            ('summary_text', 'abc-timing-summary.txt'), ('path_text', 'abc-critical-path.txt')]:
        value = hashlib.sha256(timing[field].encode()).hexdigest()
        if artifacts.get(name) != value:
            raise ValueError('ABC timing text artifact hash differs')


NATIVE_SCOPE = ('Generated and consumed inside the one pinned native mapping command, '
    'using a newly created per-row TMPDIR. Retained afterward, not Python pre-use-frozen '
    'external inputs; no global Liberty SCL or ABC cache is consumed.')


def native_mapping_artifacts(log, temporary):
    temporary = Path(temporary)
    references = {}
    for line in log.splitlines():
        script = re.fullmatch(r'Running ABC script:\s+(.+)', line)
        command = re.fullmatch(r'ABC:\s+\+\s+(read_scl|read_blif|write_blif)\s+(.+?)\s*', line)
        if script:
            role, value = 'script', script[1]
        elif command:
            role = dict(read_scl='liberty_scl', read_blif='input_blif', write_blif='output_blif')[command[1]]
            words = shlex.split(command[2])
            if len(words) != 1:
                raise ValueError('Unexpected ABC native internal input syntax')
            value = words[0]
        else:
            continue
        path = Path(value)
        if not path.is_absolute(): path = temporary / path
        if (role in references or not path.is_file() or path.is_symlink() or
                not path.resolve().is_relative_to(temporary.resolve())):
            raise ValueError('ABC consumed an ambiguous or nonisolated native cache/artifact: ' + str(path))
        references[role] = dict(path=str(path.relative_to(temporary)), sha256=sha(path))
    if set(references) != {'script', 'liberty_scl', 'input_blif', 'output_blif'}:
        raise ValueError('Missing retained ABC script, SCL or input/output BLIF')
    artifacts = {}
    for path in sorted(temporary.rglob('*')):
        if path.is_symlink() or not path.resolve().is_relative_to(temporary.resolve()):
            raise ValueError('Retained native mapping artifact escapes its fresh TMPDIR')
        if path.is_file(): artifacts[str(path.relative_to(temporary))] = sha(path)
    return dict(scope=NATIVE_SCOPE, isolated_tmpdir=True, global_cache_consumed=False,
        python_preuse_frozen=False, references=references, artifact_sha256=artifacts)


def check_native_mapping(value, artifacts):
    if (type(value) is not dict or value.get('scope') != NATIVE_SCOPE or
            value.get('isolated_tmpdir') is not True or value.get('global_cache_consumed') is not False or
            value.get('python_preuse_frozen') is not False or
            set(value.get('references', {})) != {'script', 'liberty_scl', 'input_blif', 'output_blif'} or
            not value.get('artifact_sha256')):
        raise ValueError('Fresh isolated native mapping dependencies are mandatory')
    for path, digest in value['artifact_sha256'].items():
        if (Path(path).is_absolute() or '..' in Path(path).parts or
                not re.fullmatch(r'[0-9a-f]{64}', digest) or artifacts.get('native-tmp/' + path) != digest):
            raise ValueError('Native mapping retained artifact path/hash differs')
    for reference in value['references'].values():
        if value['artifact_sha256'].get(reference.get('path')) != reference.get('sha256'):
            raise ValueError('Native mapping reference differs from its retained bytes')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def quoted(path):
    value = str(path)
    if any(char in value for char in ('\n', '\r', '\0')):
        raise ValueError('Yosys path contains a control character')
    return '"' + value.replace('\\', '\\\\').replace('"', '\\"') + '"'


def category(name, component):
    if component == 'streaming-core':
        if re.fullmatch(r'r_word\d+', name): return 'program_words'
        if re.fullmatch(r'r_tx_(word|bits)\d+', name): return 'tx_fifo_words_and_valid_counts'
        if re.fullmatch(r'r_rx_(word|bits)\d+', name): return 'rx_fifo_words_and_valid_counts'
        if name == 'r_written': return 'program_written_mask'
        if name == 'r_current_word': return 'current_cell'
        if name in ('r_tx_shift', 'r_tx_valid', 'r_cell_bit'): return 'tx_shifter'
        if name in ('r_rx_partial', 'r_rx_used'): return 'rx_partial_word'
        if name in ('r_stage1', 'r_stage2'): return 'sampler'
        return 'engine_control_and_counters'
    if component == 'streaming-frontend':
        if name in ('r_last_valid', 'r_last_request', 'r_last_reply', 'r_cache_reply'): return 'replay_cache'
        if name in ('r_tx_staging', 'r_tx_left'): return 'tx_staging'
        if name in ('r_export_data', 'r_export_start', 'r_export_bits', 'r_ack_offset'): return 'exported_rx_custody'
        if name in ('r_response', 'r_reply_logical', 'r_crc_work', 'r_crc', 'r_crc_count'): return 'response_crc_and_wire'
        if name in ('r_request', 'r_request_crc'): return 'request_frame_and_crc'
        return 'frontend_control'
    if component == 'buffered-core':
        if re.fullmatch(r'r_metadata\d+', name): return 'loop_metadata'
        if re.fullmatch(r'r_branch\d+', name): return 'branch_dictionary'
        if name in ('r_written', 'r_branch_written'): return 'upload_written_masks'
        if name in ('r_tx_data', 'r_rx_data'): return 'single_transfer_data'
        return 'engine_control_caches_and_counters'
    if component == 'buffered-frontend':
        return ('request_frame' if name == 'r_request' else
                'response_frame' if name == 'r_response' else 'frontend_control')
    raise ValueError('Unknown complete-package component')


def inventory(description, prefix, component):
    registers, seen = [], set()
    for value in description['registers']:
        name, bits = value.get('name'), value.get('width')
        if (type(name) is not str or not re.fullmatch(r'r_[a-zA-Z0-9_]+', name) or
                name in seen or type(bits) is not int or bits <= 0):
            raise ValueError('Malformed complete source-register inventory')
        seen.add(name)
        registers.append(dict(name=prefix + name, width=bits,
            origin='typed', group=component + '.' + category(name, component)))
    if not registers:
        raise ValueError('Complete component must have a nonempty register inventory')
    return registers


def digital_memory_inventory():
    result = []
    for bank in (0, 1):
        prefix = f'engine.memory.storage{bank}.'
        result += [dict(name=prefix + f'memory[{row}]', width=64,
            origin='explicit-digital-model', group='digital-memory.array_cells') for row in range(64)]
        result.append(dict(name=prefix + 'A_DOUT', width=64,
            origin='explicit-digital-model', group='digital-memory.synchronous_q'))
    return result


def cells(module, data, *, macro_count):
    selected = {name: value for name, value in module['cells'].items() if value['type'] != '$scopeinfo'}
    flops, macros, combinational = {}, {}, {}
    for name, value in selected.items():
        kind = value['type']
        if kind == MACRO:
            macros[name] = value
        elif kind.startswith('sg13cmos5l_df'):
            flops[name] = value
        elif kind.startswith('sg13cmos5l_'):
            combinational[name] = value
        else:
            raise ValueError('Unmapped or unapproved cell in saved artifact: ' + kind)
        if kind != MACRO:
            area = float(data['modules'][kind]['attributes']['area'])
            if not math.isfinite(area) or area <= 0:
                raise ValueError('Invalid standard-cell Liberty area')
    if len(macros) != macro_count:
        raise ValueError('Expected exactly the explicitly excluded SRAM macro count')
    roots = []
    for value in flops.values():
        if (len(value['connections'].get('D', [])) != 1 or
                len(value['connections'].get('Q', [])) != 1 or
                value.get('port_directions', {}).get('Q') != 'output'):
            raise ValueError('Unexpected mapped state cell shape')
        roots += value['connections']['Q']
    if any(type(bit) is not int for bit in roots) or len(roots) != len(set(roots)):
        raise ValueError('Aliased or constant mapped FF roots')
    return selected, flops, macros, combinational, set(roots)


def longest_path(module, flops, macros, combinational):
    """Cut all state and excluded macros; count gates, without Liberty delays."""
    known, drivers, successors, missing = {'0', '1'}, {}, {}, {}
    for port in module['ports'].values():
        if port['direction'] == 'input': known.update(port['bits'])
    for cell in [*flops.values(), *macros.values()]:
        for pin, bits in cell['connections'].items():
            if cell['port_directions'][pin] == 'output': known.update(bits)
    for name, cell in combinational.items():
        successors[name] = set()
        for pin, bits in cell['connections'].items():
            if cell['port_directions'][pin] == 'output':
                for bit in bits:
                    if type(bit) is not int or bit in drivers or bit in known:
                        raise ValueError('Multiple, constant or state-alias combinational driver')
                    drivers[bit] = name
    for name, cell in combinational.items():
        parents = set()
        for pin, bits in cell['connections'].items():
            if cell['port_directions'][pin] == 'input':
                for bit in bits:
                    if bit in drivers: parents.add(drivers[bit])
                    elif bit not in known: raise ValueError('Undriven or unknown combinational input')
        missing[name] = len(parents)
        for parent in parents: successors[parent].add(name)
    ready, depth, visited = deque(name for name in combinational if not missing[name]), {}, 0
    while ready:
        name = ready.popleft()
        cell = combinational[name]
        level = max((depth.get(bit, 0) for pin, bits in cell['connections'].items()
            if cell['port_directions'][pin] == 'input' for bit in bits), default=0) + 1
        for pin, bits in cell['connections'].items():
            if cell['port_directions'][pin] == 'output':
                depth.update((bit, level) for bit in bits)
        visited += 1
        for child in successors[name]:
            missing[child] -= 1
            if not missing[child]: ready.append(child)
    if visited != len(combinational):
        raise ValueError('Combinational cycle in saved mapped artifact')
    output = max((depth.get(bit, 0) for port in module['ports'].values()
        if port['direction'] == 'output' for bit in port['bits']), default=0)
    state = max((depth.get(bit, 0) for cell in flops.values()
        for bit in cell['connections']['D']), default=0)
    macro = max((depth.get(bit, 0) for cell in macros.values() for pin, bits in cell['connections'].items()
        if cell['port_directions'][pin] == 'input' for bit in bits), default=0)
    return dict(maximum_combinational_cells=max(depth.values(), default=0),
        maximum_to_public_output=output, maximum_to_ff_data=state, maximum_to_macro_input=macro,
        metric='unweighted pin-conservative cell DAG; FFs and SRAM macro arcs cut; no delay or slack')


def metrics(data, top, registers, *, macro_count=0):
    if not registers:
        raise ValueError('Complete package requires a nonempty declared state inventory')
    module = data['modules'][top]
    selected, flops, macros, combinational, roots = cells(module, data, macro_count=macro_count)
    groups, all_names, named = {}, set(), set()
    for register in registers:
        name, bits, group = register['name'], register['width'], register['group']
        if name in all_names:
            raise ValueError('Source inventory contains a register twice')
        all_names.add(name)
        netname = module['netnames'].get(name, {})
        actual = netname.get('bits')
        onehot = netname.get('attributes', {}).get('onehot') == '00000000000000000000000000000001'
        pruned = actual is None
        if pruned:
            actual = []
        elif type(actual) is not list or (len(actual) != bits and not onehot):
            raise ValueError('Missing or resized source-register netname: ' + name)
        record = groups.setdefault(group, dict(declared_bits=0, directly_named_ff_bits=set(), registers=[]))
        record['declared_bits'] += bits
        record['directly_named_ff_bits'].update(set(actual) & roots)
        record['registers'].append(dict(name=name, width=bits, mapped_named_width=len(actual),
            fsm_onehot_reencoded=onehot, source_netname_pruned=pruned))
        named.update(set(actual) & roots)
    for record in groups.values():
        record['directly_named_ff_bits'] = len(record['directly_named_ff_bits'])
    area = lambda values: sum(float(data['modules'][value['type']]['attributes']['area']) for value in values)
    sequential, logic = area(flops.values()), area(combinational.values())
    return dict(standard_cell_area_um2=round(sequential + logic, 4),
        sequential_area_um2=round(sequential, 4), combinational_area_um2=round(logic, 4),
        physical_ff_bits=len(roots), sequential_cells=len(flops), combinational_cells=len(combinational),
        standard_cells=len(flops) + len(combinational), excluded_macro_cells=len(macros),
        excluded_macro_storage_bits=macro_count * 4096, excluded_macro_output_bits=macro_count * 64,
        declared_register_bits=sum(value['width'] for value in registers),
        declared_typed_bits=sum(value['width'] for value in registers if value.get('origin') != 'explicit-digital-model'),
        declared_groups=groups,
        physical_ff_bits_directly_named=len(named),
        physical_ff_bits_not_directly_named=len(roots - named),
        attribution='Named FF counts are subsets and may overlap after alias optimization. '
            'Total FF/cell area includes recoded FSMs, digital memory and all unnamed state.',
        cell_types=dict(sorted(Counter(value['type'] for value in selected.values()).items())),
        path=longest_path(module, flops, macros, combinational))


def map_target(run, out, *, label, top, sources, registers, library, yosys, abc, macro_model=None):
    """Caller owns fresh source/producer/tool provenance and input freezing."""
    if sha(library) != LIBRARY_SHA256:
        raise ValueError('Matched cost requires the exact pinned typical Liberty')
    if type(top) is not str or not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', top):
        raise ValueError('Expected a canonical synthesis top module identifier')
    out = Path(out).resolve()
    out.mkdir(parents=True, exist_ok=False)
    temporary = out / 'native-tmp'
    temporary.mkdir()
    sources = [Path(source).resolve() for source in sources]
    library = Path(library).resolve()
    if macro_model is not None: macro_model = Path(macro_model).resolve()
    constraints = out / 'abc.constr'
    constraints.write_text(CONSTRAINTS)
    macro_count = 2 if macro_model is not None else 0
    lines = ([] if macro_model is None else ['read_verilog -lib ' + quoted(macro_model)])
    lines += ['read_verilog -sv ' + quoted(source) for source in sources]
    lines += ['hierarchy -check -top ' + top, 'synth -top ' + top + ' -flatten -noabc',
        'dffunmap', 'write_json ' + quoted(out / 'generic.json'),
        'dfflibmap -liberty ' + quoted(library),
        'abc -exe ' + quoted(abc) + ' -liberty ' + quoted(library) +
            ' -constr ' + quoted(constraints) + ' -D 10000 -nocleanup -showtmp',
        'read_liberty -lib ' + quoted(library), 'clean', 'check -assert',
        'stat -liberty ' + quoted(library), 'write_json ' + quoted(out / 'mapped.json'),
        'write_verilog -noattr -noexpr ' + quoted(out / 'mapped.v')]
    script = out / 'map.ys'
    script.write_text('\n'.join(lines) + '\n')
    inputs = {str(path): sha(path) for path in [*sources, library, constraints, script,
        *([] if macro_model is None else [macro_model])]}
    log = run(['env', '-C', temporary, 'TMPDIR=' + str(temporary),
        yosys, '-Q', '-T', '-s', script], label, timeout=900)
    if any(sha(path) != value for path, value in inputs.items()):
        raise RuntimeError('Matched synthesis input changed during use')
    result = metrics(json.loads((out / 'mapped.json').read_text()), top, registers, macro_count=macro_count)
    timing = parse_abc_timing(log)
    native = native_mapping_artifacts(log, temporary)
    for field, name in [('context_text', 'abc-timing-context.txt'),
            ('summary_text', 'abc-timing-summary.txt'), ('path_text', 'abc-critical-path.txt')]:
        (out / name).write_text(timing[field])
    result.update(label=label, top=top, boundary=BOUNDARY, input_sha256=inputs,
        abc_liberty_estimate=timing, native_mapping=native,
        artifact_sha256={**{name: sha(out / name) for name in ('generic.json', 'mapped.json', 'mapped.v',
            'abc-timing-context.txt', 'abc-timing-summary.txt', 'abc-critical-path.txt')},
            **{'native-tmp/' + path: value for path, value in native['artifact_sha256'].items()}},
        settings=dict(synth='-flatten -noabc', retiming=False, abc_delay_target_ps=10000,
            abc_constraints=CONSTRAINTS, liberty_sha256=LIBRARY_SHA256))
    return result


def emit_sources(run, out, *, root, circt, lake):
    """Fresh emission for all four rows; no historical artifacts or receipts.

    The caller must run inside its selected source archive, provide the exact
    selected native tool environment and freeze inputs before command use.
    """
    from streaming_wrapper import package_source, tt_source
    root, out = Path(root), Path(out)
    out.mkdir(parents=True, exist_ok=False)
    targets, frozen = [], {}

    def freeze(paths):
        for path in paths:
            path = Path(path)
            if path.is_symlink() or not path.is_file():
                raise ValueError('Expected a regular emitted synthesis input')
            value = sha(path)
            if str(path) in frozen and frozen[str(path)] != value:
                raise RuntimeError('Emitted input changed before use')
            frozen[str(path)] = value

    def lower(directory, component, mlir):
        freeze([mlir])
        text = run([circt, mlir, '--canonicalize', '--lower-seq-to-sv', '--lower-hw-to-sv',
            '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'],
            'cost-lower-' + directory.name + '-' + component)
        source = directory / (component + '.sv')
        source.write_text(text)
        freeze([source])
        return source

    for depth in (2, 4):
        directory = out / ('d' + str(depth))
        run([lake, 'env', 'lean', '-DwarningAsError=true', '--run',
            'test/StreamingArtifactEmit.lean', directory, '1' if depth == 2 else '2'],
            'cost-emit-d' + str(depth))
        freeze([directory / name for name in ('core.mlir', 'frontend.mlir',
            'assembly.json', 'frontend-assembly.json')])
        core = json.loads((directory / 'assembly.json').read_text())
        front = json.loads((directory / 'frontend-assembly.json').read_text())
        sources = [lower(directory, 'core', directory / 'core.mlir'),
            lower(directory, 'frontend', directory / 'frontend.mlir')]
        for name, text in [('package', package_source(core, front)), ('tt', tt_source(depth))]:
            source = directory / (name + '.sv')
            source.write_text(text)
            freeze([source])
            sources.append(source)
        registers = (inventory(core, 'engine.core.', 'streaming-core') +
            inventory(front, 'engine.frontend.', 'streaming-frontend'))
        targets.append(dict(label='streaming-d' + str(depth), top='tt_um_pinwheel_streaming_d' + str(depth),
            sources=sources, registers=registers))
    baseline = out / 'old-v1'
    baseline.mkdir()
    request = baseline / 'input.json'
    request.write_text(json.dumps(dict(schema='pinwheel-buffered-sram-serial-input-v1', cases=[])) + '\n')
    freeze([request])
    # Empty evaluator vectors request emission only, never a validation pass.
    run([lake, 'env', 'lean', '-DwarningAsError=true', '--run',
        'test/BufferedSramSerialExport.lean', request, baseline / 'frontend'], 'cost-emit-old-frontend')
    run([lake, 'env', 'lean', '-DwarningAsError=true', '--run',
        'test/SramArtifactEmit.lean', baseline / 'controller'], 'cost-emit-old-controller')
    freeze([baseline / part / name for part, name in [('frontend', 'frontend.mlir'),
        ('frontend', 'assembly.json'), ('controller', 'core.mlir'), ('controller', 'assembly.json')]])
    sources = [lower(baseline, 'frontend', baseline / 'frontend/frontend.mlir'),
        lower(baseline, 'controller', baseline / 'controller/core.mlir')]
    sources += [root / 'physical' / name for name in ('buffered_sram_serial_wrapper.sv',
        'buffered_sram_memory.sv', 'tt_um_pinwheel_buffered.sv')]
    freeze(sources)
    registers = (inventory(json.loads((baseline / 'controller/assembly.json').read_text()),
        'engine.controller.', 'buffered-core') +
        inventory(json.loads((baseline / 'frontend/assembly.json').read_text()),
        'engine.frontend.', 'buffered-frontend'))
    # This literal specifies the full digital law used for the old storage-cost
    # row. No initialization, macro dimensions, area or timing is presumed.
    model = '''module RM_IHPSG13_1P_64x64_c2_bm_bist(
input A_CLK,A_MEN,A_DLY,A_WEN,A_REN,
input [5:0] A_ADDR, input [63:0] A_DIN,A_BM, output reg [63:0] A_DOUT,
input A_BIST_CLK,A_BIST_EN,A_BIST_MEN,A_BIST_WEN,A_BIST_REN,
input [5:0] A_BIST_ADDR, input [63:0] A_BIST_DIN,A_BIST_BM);
reg [63:0] memory[0:63];
integer k;
always @(posedge A_CLK) if(A_MEN) begin
  if(A_WEN) begin
    for(k=0;k<64;k=k+1) if(A_BM[k]) memory[A_ADDR][k] <= A_DIN[k];
  end else if(A_REN) A_DOUT <= memory[A_ADDR];
end
endmodule
'''
    digital, blackbox = baseline / 'digital-memory.sv', baseline / 'excluded-macro.sv'
    digital.write_text(model)
    blackbox.write_text('(* blackbox *) ' + model.split(');', 1)[0] + ');\nendmodule\n')
    freeze([digital, blackbox])
    targets += [dict(label='buffered-v1-macro-excluded', top='tt_um_pinwheel_buffered',
        sources=sources, registers=registers, macro_model=blackbox),
        dict(label='buffered-v1-full-digital-ff', top='tt_um_pinwheel_buffered',
            sources=[*sources, digital], registers=registers + digital_memory_inventory())]
    return targets, frozen


def compare(run, out, *, root, library, yosys, abc, circt, lake):
    """Integration entry point for a caller's committed-source provenance gate."""
    if sha(library) != LIBRARY_SHA256:
        raise ValueError('Refuse an unmatched technology library before emission')
    out = Path(out)
    out.mkdir(parents=True, exist_ok=False)
    selected = out / 'cells.lib'
    selected.write_bytes(Path(library).read_bytes())
    targets, emitted = emit_sources(run, out / 'emitted', root=root, circt=circt, lake=lake)
    results = []
    for target in targets:
        if any(sha(path) != value for path, value in emitted.items()):
            raise RuntimeError('Fresh emission input changed before mapping')
        results.append(map_target(run, out / target['label'], library=selected,
            yosys=yosys, abc=abc, **target))
    if any(sha(path) != value for path, value in emitted.items()) or sha(library) != LIBRARY_SHA256:
        raise RuntimeError('Fresh emission or library input changed during mapping')
    result = dict(schema='pinwheel.streaming-matched-cost.v1', boundary=BOUNDARY,
        liberty_sha256=LIBRARY_SHA256, emission_input_sha256=emitted, emission_inputs_unchanged=True, rows=results,
        matched_settings=True, mapped_equivalence_proved=False, timing_qualified=False,
        ratios=dict(depth4_over_depth2_area=results[1]['standard_cell_area_um2'] / results[0]['standard_cell_area_um2'],
            depth2_over_old_macro_excluded_area=results[0]['standard_cell_area_um2'] / results[2]['standard_cell_area_um2'],
            depth2_over_old_full_digital_area=results[0]['standard_cell_area_um2'] / results[3]['standard_cell_area_um2']))
    check_comparison(result)
    (out / 'report.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def check_comparison(result):
    rows = result.get('rows', [])
    if ([row.get('label') for row in rows] != ['streaming-d2', 'streaming-d4',
            'buffered-v1-macro-excluded', 'buffered-v1-full-digital-ff'] or
            result.get('liberty_sha256') != LIBRARY_SHA256 or
            result.get('emission_inputs_unchanged') is not True or
            result.get('matched_settings') is not True or
            result.get('mapped_equivalence_proved') is not False or
            result.get('timing_qualified') is not False):
        raise ValueError('Incomplete matched cost matrix or unproved claim upgrade')
    for index, row in enumerate(rows):
        check_abc_timing(row.get('abc_liberty_estimate'), row.get('artifact_sha256', {}))
        check_native_mapping(row.get('native_mapping'), row.get('artifact_sha256', {}))
        if (row.get('physical_ff_bits', 0) <= 0 or row.get('standard_cell_area_um2', 0) <= 0 or
                row.get('physical_ff_bits') != row.get('sequential_cells') or
                abs(row['standard_cell_area_um2'] - row.get('sequential_area_um2', 0) -
                    row.get('combinational_area_um2', 0)) > 0.001 or
                row.get('excluded_macro_cells') != (2 if index == 2 else 0) or
                row.get('settings', {}).get('liberty_sha256') != LIBRARY_SHA256 or
                row['settings'].get('abc_constraints') != CONSTRAINTS or
                row['settings'].get('abc_delay_target_ps') != 10000 or
                row['settings'].get('synth') != '-flatten -noabc' or
                row['settings'].get('retiming') is not False):
            raise ValueError('Unmatched settings, incomplete storage or invalid area arithmetic')
        if index < 2:
            groups = row.get('declared_groups', {})
            expected = dict(program_words=4096, tx_fifo_words_and_valid_counts=76 * (index + 1),
                rx_fifo_words_and_valid_counts=76 * (index + 1), current_cell=64)
            if any(groups.get('streaming-core.' + name, {}).get('declared_bits') != bits
                    for name, bits in expected.items()):
                raise ValueError('Streaming program/FIFO/current-cell storage omitted from cost')
            frontend = sum(value.get('declared_bits', 0) for name, value in groups.items()
                if name.startswith('streaming-frontend.'))
            if frontend != 1403:
                raise ValueError('Complete frontend frame/CRC/cache/staging/export storage omitted')
        if index == 3:
            groups = row.get('declared_groups', {})
            if (groups.get('digital-memory.array_cells', {}).get('directly_named_ff_bits') != 8192 or
                    groups.get('digital-memory.synchronous_q', {}).get('directly_named_ff_bits') != 128):
                raise ValueError('Old full digital memory row omitted physical array or Q storage')
