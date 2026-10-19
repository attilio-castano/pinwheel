"""Interpret and cut the actual TT engine boundary, then restore mapped wiring.

The cut is a producer transformation. Its complete bit/port table is checked
again on restoration; Boolean certificates must prove the interpreted cut.
No module name or synthesized attribute supplies a functional equation.
"""
from copy import deepcopy
import re

from streaming_mapped_liberty import require
from streaming_mapped_certificate import expressions, lean_bool, support, namespace_name

PADS = {'ui_in': ('input', 8), 'uo_out': ('output', 8),
    'uio_in': ('input', 8), 'uio_out': ('output', 8), 'uio_oe': ('output', 8),
    'ena': ('input', 1), 'clk': ('input', 1), 'rst_n': ('input', 1)}
ENGINE = {'clk': ('input', 1), 'initialize': ('input', 1), 'csn': ('input', 1),
    'sck': ('input', 1), 'mosi': ('input', 4), 'raw_inputs': ('input', 2),
    'miso': ('output', 4), 'ready': ('output', 1), 'busy': ('output', 1),
    'levels': ('output', 3), 'enabled': ('output', 3)}
CUT_PREFIX = 'engine_boundary_'


def read_document(path):
    import json
    from pathlib import Path
    def pairs(items):
        result={}
        for key,value in items:
            require(key not in result,'Duplicate actual wrapper JSON key')
            result[key]=value
        return result
    return json.loads(Path(path).read_bytes(),object_pairs_hook=pairs)


def check_ports(ports, expected):
    require(type(ports) is dict and set(ports) == set(expected), 'Changed complete wrapper interface')
    require(all(port.get('direction') == expected[name][0] and
        type(port.get('bits')) is list and len(port['bits']) == expected[name][1]
        for name, port in ports.items()), 'Changed wrapper port direction/width')


def cut_engine(data, top, package):
    require(type(data) is dict and set(data.get('modules', {})) == {top}, 'One actual outer wrapper is required')
    result = deepcopy(data)
    module = result['modules'][top]
    check_ports(module.get('ports'), PADS)
    require(not module.get('processes') and not module.get('memories'), 'Unlowered outer wrapper')
    engines = [(name, cell) for name, cell in module.get('cells', {}).items() if cell.get('type') == package]
    require(len(engines) == 1, 'Expected one actual package instance')
    name, cell = engines[0]
    require(cell.get('parameters') == {} and cell.get('port_directions') ==
        {pin: direction for pin, (direction, _) in ENGINE.items()}, 'Changed actual package instance ABI')
    connections = cell.get('connections')
    require(type(connections) is dict and set(connections) == set(ENGINE) and
        all(type(bits) is list and len(bits) == ENGINE[pin][1] for pin, bits in connections.items()),
        'Changed actual package instance pins')
    require(connections['clk'] == module['ports']['clk']['bits'], 'Package clock is not direct top clk')
    # The event clock is checked separately and never interpreted as Boolean data.
    clock = module['ports'].pop('clk')
    del module['cells'][name]
    for pin, values in connections.items():
        if pin == 'clk': continue
        virtual = CUT_PREFIX + pin
        require(virtual not in module['ports'], 'Cut port collision')
        module['ports'][virtual] = dict(direction='output' if ENGINE[pin][0] == 'input' else 'input', bits=values)
    require(all(cell.get('type', '').startswith('$') for cell in module['cells'].values()),
        'Unexpected child instance in actual outer wrapper')
    return result, dict(top=top, package=package, instance=name, clock=clock,
        expected_cut={pin: (port['direction'], len(port['bits'])) for pin, port in module['ports'].items()})


def restore_engine(mapped, boundary):
    result = deepcopy(mapped)
    top = boundary['top']
    require(top in result.get('modules', {}), 'Mapped cut lost top module')
    module = result['modules'][top]
    check_ports(module.get('ports'), boundary['expected_cut'])
    connections = {}
    for pin in ENGINE:
        if pin != 'clk': connections[pin] = module['ports'].pop(CUT_PREFIX + pin)['bits']
    # Yosys renumbers wires. Allocate a fresh event clock, never copy its old ID.
    used = [bit for port in module['ports'].values() for bit in port['bits'] if type(bit) is int]
    used += [bit for cell in module['cells'].values() for values in cell['connections'].values()
        for bit in values if type(bit) is int]
    used += [bit for values in connections.values() for bit in values if type(bit) is int]
    clock = max(used, default=1) + 1
    module['ports']['clk'] = dict(direction='input', bits=[clock])
    connections['clk'] = [clock]
    require(boundary['instance'] not in module['cells'], 'Restored package instance collision')
    module['cells'][boundary['instance']] = dict(type=boundary['package'], parameters={}, attributes={},
        port_directions={pin: direction for pin, (direction, _) in ENGINE.items()}, connections=connections)
    check_ports(module['ports'], PADS)
    return result


def renamed_modules(data, top, prefix, library_names):
    """Rename actual child definitions and their uses together before merging."""
    require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', prefix) and top in data.get('modules', {}),
        'Invalid hierarchy rename boundary')
    modules = {name: deepcopy(module) for name, module in data['modules'].items() if name not in library_names}
    names = {name: top if name == top else prefix + name for name in modules}
    require(len(set(names.values())) == len(names), 'Renamed hierarchy collision')
    result = {}
    for name, module in modules.items():
        for cell in module.get('cells', {}).values():
            if cell['type'] in names: cell['type'] = names[cell['type']]
            else: require(cell['type'] in library_names or cell['type'] == '$scopeinfo', 'Unknown child during hierarchy merge')
        result[names[name]] = module
    return result


def merge_modules(*groups):
    result = {}
    for group in groups:
        require(not (result.keys() & group.keys()), 'Colliding complete physical module definitions')
        result.update(deepcopy(group))
    return dict(modules=result)


def wrapper_source(graph, addr_bits, *, namespace, netlist_sha256):
    """Emit scalar gate truths and all actual package-input/pad word equations."""
    namespace_name(namespace)
    require(addr_bits in (1, 2) and type(addr_bits) is int and graph.library.pinned and
        re.fullmatch('[0-9a-f]{64}', netlist_sha256), 'Unqualified wrapper identity')
    inputs = {name: shape for name, shape in PADS.items() if shape[0] == 'input' and name != 'clk'}
    inputs.update({CUT_PREFIX + name: ('input', width) for name, (direction, width) in ENGINE.items()
        if direction == 'output'})
    outputs = {name: shape for name, shape in PADS.items() if shape[0] == 'output'}
    outputs.update({CUT_PREFIX + name: ('output', width) for name, (direction, width) in ENGINE.items()
        if direction == 'input' and name != 'clk'})
    require({name: ('input', len(bits)) for name, bits in graph.inputs.items()} == inputs and
        {name: ('output', len(bits)) for name, bits in graph.outputs.items()} == outputs,
        'Mapped cut has incomplete or changed external interface')
    variables, nodes = expressions(graph, tuple(sorted(graph.inputs)))
    def variable(name):
        pin, index = name.split(':')
        if pin.startswith(CUT_PREFIX): value = f'engine .{pin.removeprefix(CUT_PREFIX)}'
        else: value = {'ui_in': 'pins.ui', 'uio_in': 'pins.uio', 'ena': 'pins.ena', 'rst_n': 'pins.rstN'}[pin]
        return f'({value}).getLsbD {index}'
    names = {name: variable(name) for name in variables}
    active = ('*', ('variable', 'ena:0'), ('variable', 'rst_n:0'))
    targets = {}
    for port, physical in nodes.items():
        if port == CUT_PREFIX + 'initialize': target = [('not', active)]
        elif port.startswith(CUT_PREFIX):
            indices = {'csn': [0], 'sck': [1], 'mosi': [2, 5, 6, 7], 'raw_inputs': [3, 4]}[port.removeprefix(CUT_PREFIX)]
            target = [('variable', f'ui_in:{i}') for i in indices]
        else:
            engine_bits = (['miso:0','miso:1','miso:2','miso:3','ready:0','busy:0'] if port == 'uo_out'
                else [f'{"levels" if port == "uio_out" else "enabled"}:{i}' for i in range(3)])
            target = [('*', active, ('variable', CUT_PREFIX + bit)) for bit in engine_bits]
            target += [('constant', False)] * (8-len(target))
        require(len(target) == len(physical), 'Canonical mapped wrapper width changed')
        targets[port] = target
    lines = ['import Pinwheel.Hardware.StreamingMapped.TinyWiring',
        'set_option linter.unusedSimpArgs false', 'set_option linter.unusedVariables false', '', f'namespace {namespace}',
        'open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady Pinwheel.Hardware.StreamingMapped',
        'abbrev Pins := Pinwheel.Hardware.StreamingReady.TinyWiring.Pins',
        f'def netlistSHA256 : String := "{netlist_sha256}"',
        f'def libertySHA256 : String := "{graph.library.sha256}"',
        'theorem one_bit (x : BitVec 1) : decide (x = 1) = x.getLsbD 0 := by decide +kernel +revert']
    canonical = {'uo_out': 'if pins.ena &&& pins.rstN = 1 then (0 : BitVec 2) ++ (engine .busy ++ (engine .ready ++ engine .miso)) else 0',
        'uio_out': 'if pins.ena &&& pins.rstN = 1 then (0 : BitVec 5) ++ engine .levels else 0',
        'uio_oe': 'if pins.ena &&& pins.rstN = 1 then (0 : BitVec 5) ++ engine .enabled else 0',
        CUT_PREFIX + 'initialize': '~~~(pins.ena &&& pins.rstN)',
        CUT_PREFIX + 'csn': "pins.ui.extractLsb' 0 1", CUT_PREFIX + 'sck': "pins.ui.extractLsb' 1 1",
        CUT_PREFIX + 'mosi': "pins.ui.extractLsb' 5 3 ++ pins.ui.extractLsb' 2 1",
        CUT_PREFIX + 'raw_inputs': "pins.ui.extractLsb' 3 2"}
    for port, physical in nodes.items():
        for i, (actual, target) in enumerate(zip(physical, targets[port])):
            local = tuple(sorted(support(actual) | support(target)))
            require(len(local) <= 3, 'Outer wrapper cone exceeds bounded scalar proof scope')
            local_names = {name: f'v{n}' for n, name in enumerate(local)}
            params = ' '.join(f'(v{n} : Bool)' for n in range(len(local)))
            lines.append(f'theorem {port}_bit{i} {params} : {lean_bool(actual,local_names)} = {lean_bool(target,local_names)} := by decide +kernel +revert')
        cases = '\n'.join(f'  | {i} => {lean_bool(node,names)}' for i,node in enumerate(physical[:-1]))
        lines += [f'def {port} (pins : Pins) (engine : Values Package.Output) : BitVec {len(physical)} :=',
            f'  Word.pack (fun bit => match bit.val with\n{cases}\n  | _ => {lean_bool(physical[-1],names)})',
            f'theorem {port}_correct (pins : Pins) (engine : Values Package.Output) :',
            f'    {port} pins engine = ({canonical[port]}) := by',
            '  apply Word.from_bits', '  intro i within', f'  rw [{port},Word.pack_bit _ i within]']
        if len(physical) == 1:
            lines += ['  have index : i = 0 := by omega', '  subst i']
        else:
            lines += ['  have indices : ' + ' ∨ '.join(f'i = {i}' for i in range(len(physical))) + ' := by omega',
                '  rcases indices with ' + ' | '.join('rfl' for _ in physical)]
        for i, (actual,target) in enumerate(zip(physical,targets[port])):
            local = tuple(sorted(support(actual) | support(target)))
            args = ' '.join('(' + names[name] + ')' for name in local)
            prefix = '  · ' if len(physical)>1 else '  '
            indent = '    ' if len(physical)>1 else '  '
            lines += [prefix + f'rw [{port}_bit{i} {args}]']
            if port in ('uo_out','uio_out','uio_oe'):
                lines += [indent + 'by_cases active : pins.ena &&& pins.rstN = 1',
                    indent + '· rw [if_pos active]',
                    indent + '  have activeBits := one_bit (pins.ena &&& pins.rstN)',
                    indent + '  rw [BitVec.getLsbD_and] at activeBits',
                    indent + '  have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=',
                    indent + '    activeBits.symm.trans (by simp only [active,decide_true])',
                    indent + '  simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]',
                    indent + '  simp',
                    indent + '· rw [if_neg active]',
                    indent + '  have activeBits := one_bit (pins.ena &&& pins.rstN)',
                    indent + '  rw [BitVec.getLsbD_and] at activeBits',
                    indent + '  have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=',
                    indent + '    activeBits.symm.trans (by simp only [active,decide_false])',
                    indent + '  simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]',
                    indent + '  rfl']
            else:
                lines += [indent + 'simp only [BitVec.getLsbD_append,BitVec.getLsbD_extractLsb\',BitVec.getLsbD_and,BitVec.getLsbD_not]',
                    indent + 'simp']
    lines += ['def actualEngine (pins : Pins) : Package.Pins :=',
        '  ⟨engine_boundary_initialize pins (fun _ => 0),engine_boundary_csn pins (fun _ => 0),',
        '   engine_boundary_sck pins (fun _ => 0),engine_boundary_mosi pins (fun _ => 0),',
        '   engine_boundary_raw_inputs pins (fun _ => 0)⟩',
        'def actualPads (pins : Pins) (engine : Values Package.Output) : Pinwheel.Hardware.StreamingReady.TinyWiring.Pad → BitVec 8',
        '  | .uo => uo_out pins engine | .uio => uio_out pins engine | .oe => uio_oe pins engine',
        'def actualTiny : Pinwheel.Hardware.StreamingMapped.TinyWiring.Backend := ⟨actualEngine,actualPads⟩',
        f'theorem tiny_correct : actualTiny.Correct {addr_bits} where',
        '  enginePins := by', '    intro pins',
        '    simp only [actualTiny,actualEngine,engine_boundary_initialize_correct,engine_boundary_csn_correct,',
        '      engine_boundary_sck_correct,engine_boundary_mosi_correct,engine_boundary_raw_inputs_correct]',
        '    rfl',
        '  pads := by', '    intro pins engine pad', '    cases pad <;> simp only [actualTiny,actualPads,uo_out_correct,uio_out_correct,uio_oe_correct] <;> rfl',
        f'end {namespace}']
    return '\n'.join(lines) + '\n'


def prepare_wrapper(out, *, addr_bits, tiny, package, liberty, yosys, abc, run):
    """Produce actual mapped outer cut and its certificate in a fresh folder.

    ``run(argv, log_path)`` must execute natively, retain output and refuse
    nonzero exits. Source hashes are checked at both ends of this producer.
    """
    from hashlib import sha256
    import json
    from pathlib import Path
    from streaming_mapped_flow import mapping_script, quoted
    from streaming_mapped_liberty import load_library
    from streaming_mapped_netlist import load_mapped
    require(type(addr_bits) is int and addr_bits in (1, 2), 'Unsupported wrapper queue width')
    out = Path(out).resolve()
    require(not out.exists(), 'Wrapper producer requires a fresh output folder')
    out.mkdir(parents=True)
    files = {name: Path(path).resolve() for name,path in
        dict(tiny=tiny, package=package, liberty=liberty).items()}
    require(all(path.is_file() and not path.is_symlink() for path in files.values()), 'Expected regular wrapper sources')
    hashes = {name: sha256(path.read_bytes()).hexdigest() for name,path in files.items()}
    library = load_library(files['liberty'])
    depth = 2 ** addr_bits
    top, package_name = f'tt_um_pinwheel_streaming_ready_d{depth}', f'pinwheel_streaming_ready_quad_d{depth}'
    source_script = '\n'.join(('read_verilog -lib '+quoted(files['package']),
        'read_verilog '+quoted(files['tiny']), 'hierarchy -check -top '+top,
        'proc', 'write_json '+quoted(out/'actual-outer.json'))) + '\n'
    (out/'read.ys').write_text(source_script)
    run([str(yosys), '-Q', '-s', str(out/'read.ys')], out/'read.log')
    raw = read_document(out/'actual-outer.json')
    require(top in raw.get('modules', {}) and package_name in raw['modules'], 'Actual outer import lost package definition')
    check_ports(raw['modules'][package_name].get('ports'), ENGINE)
    actual = dict(modules={top: raw['modules'][top]})
    cut, boundary = cut_engine(actual, top, package_name)
    (out/'cut.json').write_text(json.dumps(cut, indent=2)+'\n')
    (out/'boundary.json').write_text(json.dumps(boundary, indent=2)+'\n')
    (out/'map.ys').write_text(mapping_script(out/'cut.json',top,out,files['liberty'],abc))
    run([str(yosys), '-Q', '-s', str(out/'map.ys')], out/'map.log')
    graph = load_mapped(out/'mapped.json',top,library,combinational=True)
    stem = f'StreamingMappedTinyD{depth}'
    (out/(stem+'.lean')).write_text(wrapper_source(graph,addr_bits,
        namespace='Pinwheel.Artifact.'+stem,netlist_sha256=sha256((out/'mapped.json').read_bytes()).hexdigest()))
    restored = restore_engine(read_document(out/'mapped.json'),boundary)
    (out/'restored.json').write_text(json.dumps(restored,indent=2)+'\n')
    require(hashes == {name:sha256(path.read_bytes()).hexdigest() for name,path in files.items()},
        'Wrapper producer source changed during interpretation')
    return dict(top=top,package=package_name,source_sha256=hashes,mapped_comb_cells=len(graph.gates),
        mapped_json=str(out/'mapped.json'),restored_json=str(out/'restored.json'),
        proof_source=str(out/(stem+'.lean')),proof_module=stem,proof_checked=False,
        boundary='Actual pad/package-boundary Boolean functions; event clock separately checked direct. Native kernel compilation still required.')


def package_source(data, top, addr_bits, *, namespace, netlist_sha256):
    """Reconstruct actual package wire vectors into a typed wiring certificate.

    There are no assumed named internal signals: complete connected vectors
    resolve to actual primary inputs or actual child output ports. Every
    resulting typed connection is independently checked by the kernel.
    """
    import streaming_ready_readback as interface
    import streaming_ready_wrapper_readback as wrapper
    import artifact_wrapper_readback as syntax
    namespace_name(namespace)
    require(type(addr_bits) is int and addr_bits in (1,2) and re.fullmatch('[0-9a-f]{64}',netlist_sha256),
        'Unqualified package identity')
    require(type(data) is dict and top in data.get('modules',{}), 'Missing actual package module')
    module=data['modules'][top]
    check_ports(module.get('ports'),ENGINE)
    require(not module.get('processes') and not module.get('memories') and
        set(module.get('cells',{}))=={'frontend','core'}, 'Unexpected actual package logic or child inventory')
    front,core=interface.backend('frontend',addr_bits),interface.backend('core',addr_bits)
    models={'frontend':front,'core':core}
    for name,model in models.items():
        child=module['cells'][name]
        expected={'clk':('input',1),**{pin:('input',w) for pin,(w,_) in model.INPUTS.items()},
            **{pin:('output',w) for pin,(w,_) in model.OUTPUTS.items()}}
        require(child.get('type')==model.TOP and child.get('parameters')=={} and
            child.get('port_directions')=={pin:shape[0] for pin,shape in expected.items()},
            'Changed actual package child type/parameters/directions')
        check_ports({pin:dict(direction=child['port_directions'][pin],bits=bits)
            for pin,bits in child['connections'].items()},expected)
        require(child['connections']['clk']==module['ports']['clk']['bits'], 'Changed actual package event clock')
    drivers={}
    def claim(bits,source):
        key=tuple(bits)
        require(key and all(type(bit) is int for bit in key) and len(set(key))==len(key) and key not in drivers,
            'Constant, aliased or duplicate actual package source vector')
        drivers[key]=source
    for name,_,ctor in interface.FRONTEND_INPUTS: claim(module['ports'][name]['bits'],('physical',ctor))
    for child,model,kind in [('frontend',front,'frontend'),('core',core,'status')]:
        for pin,(_,ctor) in model.OUTPUTS.items():
            claim(module['cells'][child]['connections'][pin],(kind,ctor[1:] if kind=='status' else ctor))
    def resolve(bits,allowed):
        key=tuple(bits)
        require(key in drivers and drivers[key][0] in allowed,'Actual package vector is undriven, resized, reordered or unsupported')
        return drivers[key]
    lines=['import Pinwheel.Hardware.StreamingReady.Wiring','',f'namespace {namespace}',
        'open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady Wiring',
        f'def netlistSHA256 : String := "{netlist_sha256}"',
        'def actualFrontend : {w : Nat} → Pinwheel.Hardware.Streaming.Frontend.Input w → FrontSource w']
    for pin,(_,ctor) in front.INPUTS.items():
        lines.append(f'  | _, {ctor} => '+wrapper.selection(resolve(module['cells']['frontend']['connections'][pin],{'physical','status'})))
    lines+=['def actualCore : {w : Nat} → Pinwheel.Hardware.StreamingReady.Core.Input w → Pinwheel.Hardware.Streaming.Frontend.Output w']
    for pin,(_,ctor) in core.INPUTS.items():
        lines.append(f'  | _, {ctor} => '+resolve(module['cells']['core']['connections'][pin],{'frontend'})[1])
    lines+=['def actualOutput : {w : Nat} → Package.Output w → PublicSource w']
    for pin,(direction,_) in ENGINE.items():
        if direction=='output': lines.append(f'  | _, .{pin} => '+wrapper.selection(resolve(module['ports'][pin]['bits'],{'frontend','status'})))
    ports=syntax.lean_list('⟨'+syntax.quoted(pin)+','+str(width)+','+str(direction=='input').lower()+'⟩'
        for pin,(direction,width) in ENGINE.items())
    instances=syntax.lean_list('⟨'+syntax.quoted(name)+','+syntax.quoted(module['cells'][name]['type'])+'⟩'
        for name in ('frontend','core'))
    lines+=['def actualPackage : Wiring.Description :=',
        '  ⟨'+','.join((syntax.quoted(top),ports,instances,'"clk"','"clk"','actualFrontend','actualCore','actualOutput'))+'⟩',
        f'theorem package_correct : Wiring.Certificate {addr_bits} actualPackage where',
        '  name := rfl','  interface := rfl','  instances := rfl','  frontendClock := rfl','  coreClock := rfl',
        '  frontend := by\n    intro w port\n    cases port <;> try rfl\n    case status o => cases o <;> rfl',
        '  core := by intro w port; cases port <;> rfl','  outputs := by intro w port; cases port <;> rfl',
        f'end {namespace}']
    return '\n'.join(lines)+'\n'


def prepare_package(out, *, addr_bits, package, frontend, core, yosys, run):
    from hashlib import sha256
    import json
    from pathlib import Path
    from streaming_mapped_flow import quoted
    require(type(addr_bits) is int and addr_bits in (1,2),'Unsupported package queue width')
    out=Path(out).resolve()
    require(not out.exists(),'Package producer requires a fresh output folder')
    out.mkdir(parents=True)
    files={name:Path(path).resolve() for name,path in dict(package=package,frontend=frontend,core=core).items()}
    require(all(path.is_file() and not path.is_symlink() for path in files.values()),'Expected regular package/child sources')
    hashes={name:sha256(path.read_bytes()).hexdigest() for name,path in files.items()}
    top=f'pinwheel_streaming_ready_quad_d{2**addr_bits}'
    script='\n'.join(('read_verilog -sv -lib '+quoted(files['frontend']),
        'read_verilog -sv -lib '+quoted(files['core']),'read_verilog -sv '+quoted(files['package']),
        'hierarchy -check -top '+top,'proc','write_json '+quoted(out/'package-import.json'))) + '\n'
    (out/'read.ys').write_text(script)
    run([str(yosys),'-Q','-s',str(out/'read.ys')],out/'read.log')
    imported=read_document(out/'package-import.json')
    require(top in imported.get('modules',{}),'Native import lost actual package')
    actual=dict(modules={top:imported['modules'][top]})
    (out/'package.json').write_text(json.dumps(actual,indent=2)+'\n')
    stem=f'StreamingMappedPackageD{2**addr_bits}'
    (out/(stem+'.lean')).write_text(package_source(actual,top,addr_bits,namespace='Pinwheel.Artifact.'+stem,
        netlist_sha256=sha256((out/'package.json').read_bytes()).hexdigest()))
    require(hashes=={name:sha256(path.read_bytes()).hexdigest() for name,path in files.items()},
        'Actual package/child source changed during native interpretation')
    return dict(top=top,source_sha256=hashes,package_json=str(out/'package.json'),
        proof_source=str(out/(stem+'.lean')),proof_module=stem,proof_checked=False)


def complete_hierarchy(outer, package, core, frontend, *, addr_bits, library):
    depth=2**addr_bits
    require(type(addr_bits) is int and addr_bits in (1,2) and library.pinned,'Unqualified complete mapped hierarchy')
    package_name=f'pinwheel_streaming_ready_quad_d{depth}'
    require(set(package.get('modules',{}))=={package_name},'Expected exactly the interpreted package module')
    return merge_modules(renamed_modules(outer,f'tt_um_pinwheel_streaming_ready_d{depth}','outer_',set(library.cells)|{package_name}),
        package['modules'],renamed_modules(core,f'pinwheel_streaming_ready_core_d{depth}','core_',set(library.cells)),
        renamed_modules(frontend,'pinwheel_streaming_quad_frontend','front_',set(library.cells)))
