"""Restricted, explicit-trust SV wrapper decoder and Lean wiring certificates.

This is deliberately not a general Verilog frontend. It accepts one stateless
module, explicit/wildcard named instances, wires, continuous assignments, typed
constants, slices, concatenation, Boolean logic and muxes. Unsupported syntax,
state, duplicate declarations/ports/drivers and unresolved sources fail closed.
The generated Lean describes the parsed connections/expressions; kernel proofs
check those descriptions against the separately defined typed evaluator.
"""
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re


CORE = dict(initialize=(1, 'initialize'), command=(3, 'command'), address=(6, 'address'),
    word=(64, 'word'), branch=(56, 'branch'), control=(24, 'control'),
    virtual_span=(11, 'virtualSpan'), count=(7, 'count'), idle_levels=(3, 'idleLevels'),
    idle_enabled=(3, 'idleEnabled'), tx_data=(32, 'txData'), tx_length=(6, 'txLength'),
    rx_capacity=(6, 'rxCapacity'), expected_generation=(16, 'expectedGeneration'),
    expected_transfer=(16, 'expectedTransfer'), read_index=(5, 'readIndex'), raw_inputs=(2, 'rawInputs'))
STATUS = dict(valid=(1, 'valid'), busy=(1, 'busy'), retained=(1, 'retained'), pending=(1, 'pending'),
    rejected=(1, 'rejected'), mode=(2, 'mode'), pc=(8, 'pc'), remaining=(8, 'remaining'),
    levels=(3, 'levels'), enabled=(3, 'enabled'), tx_consumed=(6, 'txConsumed'),
    rx_length=(6, 'rxLength'), rx_data=(32, 'rxData'), read_valid=(1, 'readValid'),
    read_bit=(1, 'readBit'), generation=(16, 'generation'), transfer=(16, 'transfer'),
    exhausted=(1, 'exhausted'), stage1=(2, 'stage1'), stage2=(2, 'stage2'),
    virtual_pc=(10, 'virtualPC'), env0=(3, 'env0'), env1=(3, 'env1'), phase=(3, 'phase'),
    wait_left=(8, 'waitLeft'), scratch=(16, 'scratch'))
PHYSICAL = dict(initialize=(1, 'initialize'), csn=(1, 'csn'), sck=(1, 'sck'),
    mosi=(1, 'mosi'), raw_inputs=(2, 'rawInputs'))
MEMORY = dict(mem_addr0=6, mem_addr1=6, mem_data=64, mem_write=1, mem_read=1, mem_q0=64, mem_q1=64)
MACRO = dict(A_CLK=1, A_MEN=1, A_DLY=1, A_WEN=1, A_REN=1, A_ADDR=6, A_DIN=64, A_DOUT=64,
    A_BM=64, A_BIST_CLK=1, A_BIST_EN=1, A_BIST_MEN=1, A_BIST_WEN=1, A_BIST_REN=1,
    A_BIST_ADDR=6, A_BIST_DIN=64, A_BIST_BM=64)
MEMORY_PORTS = {'mem_addr0': '(Sram.Port.address false)', 'mem_addr1': '(Sram.Port.address true)',
    'mem_data': 'Sram.Port.data', 'mem_write': 'Sram.Port.write', 'mem_read': 'Sram.Port.read'}


def require(value, message):
    if not value:
        raise ValueError(message)


TOKEN = re.compile(r"[0-9]+'[bBdDhH][0-9a-fA-F_]+|[0-9]+|[A-Za-z_][A-Za-z_0-9]*|&&|[()\[\]{}:;,.?=!~&*]")
IDENT = re.compile(r'[A-Za-z_][A-Za-z_0-9]*\Z')


@dataclass
class Module:
    name: str
    ports: list
    widths: dict
    wires: set
    assignments: dict
    instances: list
    source: str
    sha256: str


class Parser:
    def __init__(self, text):
        require(text.count('/*') == text.count('*/'), 'Unclosed wrapper comment')
        text = re.sub(r'/\*.*?\*/|//[^\n]*', '', text, flags=re.S)
        lines = []
        for line in text.splitlines():
            if line.strip().startswith('`'):
                require(line.strip() in ('`default_nettype none', '`default_nettype wire'),
                    'Unsupported wrapper directive')
            else:
                lines.append(line)
        text = '\n'.join(lines)
        self.tokens, position = [], 0
        for match in TOKEN.finditer(text):
            require(not text[position:match.start()].strip(), 'Unsupported wrapper token')
            self.tokens.append(match.group())
            position = match.end()
        require(not text[position:].strip(), 'Unsupported wrapper token')
        self.position = 0

    def peek(self):
        return self.tokens[self.position] if self.position < len(self.tokens) else None

    def pop(self, expected=None):
        value = self.peek()
        require(value is not None and (expected is None or value == expected),
            'Expected wrapper token: ' + str(expected))
        self.position += 1
        return value

    def identifier(self):
        value = self.pop()
        require(IDENT.fullmatch(value) is not None, 'Expected wrapper identifier')
        return value

    def width(self):
        if self.peek() != '[':
            return 1
        self.pop('[')
        high = self.pop()
        self.pop(':')
        low = self.pop()
        self.pop(']')
        require(high.isdecimal() and low == '0' and int(high) < 65536,
            'Unsupported wrapper declaration range')
        return int(high) + 1

    def expression(self):
        value = self.boolean()
        if self.peek() == '?':
            self.pop('?')
            yes = self.expression()
            self.pop(':')
            value = ('mux', value, yes, self.expression())
        return value

    def boolean(self):
        value = self.unary()
        while self.peek() == '&&':
            self.pop()
            value = ('and', value, self.unary())
        return value

    def unary(self):
        if self.peek() in ('!', '~', '&'):
            operation = {'!': 'not', '~': 'inv', '&': 'reduce_and'}[self.pop()]
            return (operation, self.unary())
        token = self.pop()
        if token == '(':
            value = self.expression()
            self.pop(')')
            return value
        if token == '{':
            parts = [self.expression()]
            while self.peek() == ',':
                self.pop(',')
                parts.append(self.expression())
            self.pop('}')
            require(len(parts) >= 2, 'Unsupported singleton wrapper concatenation')
            return ('concat', tuple(parts))
        literal = re.fullmatch(r"([0-9]+)'([bBdDhH])([0-9a-fA-F_]+)", token)
        if literal:
            width, base, digits = literal.groups()
            number = int(digits.replace('_', ''), {'b': 2, 'd': 10, 'h': 16}[base.lower()])
            require(0 < int(width) <= 65536 and number < 2**int(width), 'Invalid wrapper constant')
            return ('constant', int(width), number)
        require(IDENT.fullmatch(token) is not None, 'Unsupported unsized wrapper literal')
        value = ('wire', token)
        if self.peek() == '[':
            self.pop('[')
            high = self.pop()
            require(high.isdecimal(), 'Nonliteral wrapper slice')
            low = high
            if self.peek() == ':':
                self.pop(':')
                low = self.pop()
            self.pop(']')
            require(low.isdecimal() and int(high) >= int(low), 'Invalid wrapper slice')
            value = ('slice', value, int(low), int(high)-int(low)+1)
        return value

    def module(self, source, digest):
        self.pop('module')
        name = self.identifier()
        self.pop('(')
        ports, widths, direction, width = [], {}, None, None
        while self.peek() != ')':
            if self.peek() in ('input', 'output'):
                direction = self.pop()
                if self.peek() == 'wire':
                    self.pop()
                width = self.width()
            require(direction is not None, 'Missing wrapper port direction')
            port = self.identifier()
            require(port not in widths, 'Duplicate wrapper port')
            widths[port] = width
            ports.append((port, width, direction == 'input'))
            if self.peek() != ')':
                self.pop(',')
        self.pop(')')
        self.pop(';')
        wires, assignments, instances, instance_names = set(), {}, [], set()
        while self.peek() != 'endmodule':
            if self.peek() == 'wire':
                self.pop()
                width = self.width()
                while True:
                    wire = self.identifier()
                    require(wire not in widths, 'Duplicate wrapper wire')
                    widths[wire] = width
                    wires.add(wire)
                    if self.peek() == '=':
                        self.pop()
                        assignments[wire] = self.expression()
                    if self.peek() != ',':
                        break
                    self.pop(',')
                self.pop(';')
            elif self.peek() == 'assign':
                self.pop()
                wire = self.identifier()
                require(wire in widths and wire not in assignments, 'Unknown/multiply driven wrapper assignment')
                self.pop('=')
                assignments[wire] = self.expression()
                self.pop(';')
            else:
                kind, instance = self.identifier(), self.identifier()
                require(instance not in instance_names, 'Duplicate wrapper instance')
                instance_names.add(instance)
                self.pop('(')
                connections, wildcard = {}, False
                while self.peek() != ')':
                    self.pop('.')
                    if self.peek() == '*':
                        self.pop('*')
                        require(not connections and not wildcard, 'Unsupported mixed wildcard wrapper instance')
                        wildcard = True
                    else:
                        require(not wildcard, 'Unsupported mixed wildcard wrapper instance')
                        port = self.identifier()
                        require(port not in connections, 'Duplicate wrapper instance port')
                        self.pop('(')
                        connections[port] = self.expression()
                        self.pop(')')
                    if self.peek() != ')':
                        self.pop(',')
                self.pop(')')
                self.pop(';')
                instances.append(dict(kind=kind, name=instance, connections=connections, wildcard=wildcard))
        self.pop('endmodule')
        require(self.peek() is None, 'Additional module or wrapper syntax')
        result = Module(name, ports, widths, wires, assignments, instances, source, digest)
        for name, expression in assignments.items():
            require(expression_width(expression, widths) == widths[name], 'Wrapper assignment width mismatch')
            require(name not in {n for n, _, i in ports if i}, 'Wrapper drives a public input')
        return result


def expression_width(expr, widths):
    operation = expr[0]
    if operation == 'wire':
        require(expr[1] in widths, 'Undeclared wrapper source: ' + expr[1])
        return widths[expr[1]]
    if operation == 'constant':
        return expr[1]
    if operation == 'slice':
        require(expr[2] + expr[3] <= expression_width(expr[1], widths), 'Wrapper slice exceeds source')
        return expr[3]
    if operation == 'concat':
        return sum(expression_width(e, widths) for e in expr[1])
    if operation == 'and':
        require(expression_width(expr[1], widths) == expression_width(expr[2], widths) == 1,
            'Unsupported non-Boolean wrapper logic')
        return 1
    if operation == 'not':
        require(expression_width(expr[1], widths) == 1, 'Unsupported non-Boolean wrapper negation')
        return 1
    if operation == 'inv':
        return expression_width(expr[1], widths)
    if operation == 'reduce_and':
        expression_width(expr[1], widths)
        return 1
    if operation == 'mux':
        require(expression_width(expr[1], widths) == 1, 'Non-Boolean wrapper select')
        left, right = expression_width(expr[2], widths), expression_width(expr[3], widths)
        require(left == right, 'Wrapper mux width mismatch')
        return left
    raise ValueError('Unsupported wrapper expression')


def read_module(path):
    path = Path(path)
    data = path.read_bytes()
    return Parser(data.decode()).module(str(path), hashlib.sha256(data).hexdigest())


def connections(module, instance, interface):
    result = ({name: ('wire', name) for name in interface} if instance['wildcard'] else instance['connections'])
    require(set(result) == set(interface), 'Incomplete/extra wrapper instance ports: ' + instance['name'])
    for name, width in interface.items():
        require(expression_width(result[name], module.widths) == width, 'Wrapper instance width mismatch: ' + name)
    return result


def wire(expr):
    require(expr[0] == 'wire', 'Wrapper connection is not a transparent wire')
    return expr[1]


def instance(module, name):
    found = [value for value in module.instances if value['name'] == name]
    require(len(found) == 1, 'Missing wrapper instance: ' + name)
    return found[0]


def claim(drivers, name, value):
    require(name not in drivers, 'Multiple wrapper drivers: ' + name)
    drivers[name] = value


def resolve(module, drivers, expr, active=()):
    name = wire(expr)
    require(name not in active, 'Combinational wrapper cycle')
    if name in module.assignments:
        require(name not in drivers, 'Multiple wrapper drivers: ' + name)
        return resolve(module, drivers, module.assignments[name], (*active, name))
    require(name in drivers, 'Unresolved wrapper source: ' + name)
    return drivers[name]


def read_wrappers(package, memory, tiny):
    package, memory, tiny = map(read_module, (package, memory, tiny))
    front = instance(package, 'frontend')
    core = instance(package, 'controller')
    mem = instance(package, 'memory')
    front_ports = {'clk': 1, **{n: w for n, (w, _) in PHYSICAL.items()},
        **{'status_'+n: w for n, (w, _) in STATUS.items()},
        **{'core_'+n: w for n, (w, _) in CORE.items()}, 'miso': 1, 'ready': 1}
    core_ports = {'clk': 1, **{n: w for n, (w, _) in CORE.items()},
        **{n: w for n, (w, _) in STATUS.items()}, **MEMORY}
    f = connections(package, front, front_ports)
    c = connections(package, core, core_ports)
    m = connections(package, mem, {'clk': 1, **MEMORY})
    require(set(package.assignments) == {'busy', 'levels', 'enabled'},
        'Unexpected/missing package wrapper logic')
    require(set(memory.assignments) == set(), 'Unexpected memory wrapper logic')
    require(len(memory.instances) == 2, 'Memory wrapper must contain exactly two macro instances')
    drivers = {}
    for name, (_, tag) in PHYSICAL.items():
        claim(drivers, name, ('physical', tag))
    for name, (_, tag) in CORE.items():
        claim(drivers, wire(f['core_'+name]), ('frontend', '(.core .'+tag+')'))
    for name in ('miso', 'ready'):
        claim(drivers, wire(f[name]), ('frontend', '.'+name))
    for name, (_, tag) in STATUS.items():
        claim(drivers, wire(c[name]), ('status', tag))
    for name, tag in MEMORY_PORTS.items():
        claim(drivers, wire(c[name]), ('port', tag))
    macros = []
    for index, macro in enumerate(memory.instances):
        ports = connections(memory, macro, MACRO)
        q_name = wire(ports['A_DOUT'])
        require(q_name in m, 'Macro Q is not a memory wrapper port')
        claim(drivers, wire(m[q_name]), ('memory', bool(index)))
        macros.append((macro, ports))
    frontend = {}
    for name in PHYSICAL:
        value = resolve(package, drivers, f[name])
        require(value[0] in ('physical', 'status'), 'Unsupported frontend input source')
        frontend[name] = value
    for name in STATUS:
        value = resolve(package, drivers, f['status_'+name])
        require(value[0] in ('physical', 'status'), 'Unsupported frontend status source')
        frontend['status_'+name] = value
    controller = {}
    for name in [*CORE, 'mem_q0', 'mem_q1']:
        value = resolve(package, drivers, c[name])
        require(value[0] in ('frontend', 'memory'), 'Unsupported controller input source')
        controller[name] = value
    macro_records = []
    for macro, ports in macros:
        constants = []
        for name, expr in ports.items():
            if name in ('A_CLK', 'A_WEN', 'A_REN', 'A_ADDR', 'A_DIN', 'A_DOUT'):
                continue
            require(expr[0] == 'constant', 'Unsupported dynamic macro configuration')
            constants.append((name, expr[1], expr[2]))
        record = dict(name=macro['name'], kind=macro['kind'], clock=wire(m[wire(ports['A_CLK'])]),
            constants=constants)
        for key, port in [('address', 'A_ADDR'), ('data', 'A_DIN'), ('write', 'A_WEN'), ('read', 'A_REN')]:
            local = wire(ports[port])
            require(local in m, 'Macro dynamic input is not a wrapper port')
            value = resolve(package, drivers, m[local])
            require(value[0] == 'port', 'Macro input does not come from a controller memory port')
            record[key] = value[1]
        macro_records.append(record)
    public = {}
    for name, _, is_input in package.ports:
        if not is_input:
            value = resolve(package, drivers, ('wire', name))
            require(value[0] in ('frontend', 'status'), 'Unsupported public wrapper output source')
            public[name] = value
    require(set(public) == {'miso', 'ready', 'busy', 'levels', 'enabled'}, 'Unknown public wrapper outputs')
    require(len(tiny.instances) == 1, 'TinyTapeout wrapper contains extra instances')
    engine = tiny.instances[0]
    t = connections(tiny, engine, {'clk': 1, **{n: w for n, (w, _) in PHYSICAL.items()},
        'miso': 1, 'ready': 1, 'busy': 1, 'levels': 3, 'enabled': 3})
    tiny_inputs = {'ui_in': 'Input.ui', 'uio_in': 'Input.uio', 'ena': 'Input.ena', 'rst_n': 'Input.rstN'}
    for name in ('miso', 'ready', 'busy', 'levels', 'enabled'):
        target = wire(t[name])
        require(target not in tiny.assignments and target not in tiny_inputs, 'Multiple TinyTapeout drivers')
        tiny_inputs[target] = '(Input.engine SerialPackage.Output.'+name+')'
    require(set(tiny.assignments) == {'active', 'initialize', 'uo_out', 'uio_out', 'uio_oe', '_unused'},
        'Unexpected/missing TinyTapeout wrapper logic')
    require(set(memory.widths) == {'clk', *MEMORY}, 'Unexpected memory wrapper wire inventory')
    require(set(name for name, _, _ in memory.ports) == {'clk', *MEMORY}, 'Incomplete memory wrapper interface')
    return dict(package=package, memory=memory, tiny=tiny, frontend=frontend, controller=controller,
        macros=macro_records, outputs=public, frontend_clock=wire(f['clk']), controller_clock=wire(c['clk']),
        memory_clock=wire(m['clk']), tiny_engine=engine, tiny_connections=t, tiny_inputs=tiny_inputs)


def quoted(value):
    return json.dumps(value, ensure_ascii=True)


def lean_list(values):
    return '[' + ','.join(values) + ']'


def source(value):
    kind, tag = value
    if kind == 'physical': return '.physical .'+tag
    if kind == 'frontend': return '.frontend '+tag
    if kind == 'status': return '.status .'+tag
    if kind == 'memory': return '.memory '+str(tag).lower()
    raise ValueError('Unknown Lean wrapper source')


def port_list(module):
    return lean_list('⟨'+quoted(n)+','+str(w)+','+str(i).lower()+'⟩' for n, w, i in module.ports)


def expand_expression(module, expr, sources, active=()):
    kind = expr[0]
    if kind == 'wire':
        name = expr[1]
        if name in module.assignments:
            require(name not in active, 'Cyclic TinyTapeout assignment')
            return expand_expression(module, module.assignments[name], sources, (*active, name))
        require(name in sources, 'Unresolved TinyTapeout expression input: ' + name)
        return '(.input '+sources[name]+')'
    if kind == 'constant': return '(.lit (BitVec.ofNat '+str(expr[1])+' '+str(expr[2])+'))'
    if kind == 'slice':
        return '(.slice '+str(expr[2])+' '+str(expr[3])+' (by decide +kernel) '+expand_expression(module, expr[1], sources, active)+')'
    if kind == 'concat':
        parts = [expand_expression(module, value, sources, active) for value in expr[1]]
        result = parts[-1]
        for value in reversed(parts[:-1]): result = '(.concat '+value+' '+result+')'
        return result
    if kind in ('inv', 'not'): return '(.inv '+expand_expression(module, expr[1], sources, active)+')'
    if kind == 'and':
        return '(.band '+expand_expression(module, expr[1], sources, active)+' '+expand_expression(module, expr[2], sources, active)+')'
    if kind == 'mux':
        return '(.mux '+' '.join(expand_expression(module, value, sources, active) for value in expr[1:])+')'
    if kind == 'reduce_and':
        width = expression_width(expr[1], module.widths)
        return '(.equal '+expand_expression(module, expr[1], sources, active)+' (.lit (BitVec.ofNat '+str(width)+' '+str(2**width-1)+')))'
    raise ValueError('Unsupported Lean wrapper expression')


def lean_source(bundle, namespace='Pinwheel.Artifact.Buffered.Wrappers'):
    require(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*', namespace), 'Invalid Lean wrapper namespace')
    package, memory, tiny = (bundle[n] for n in ('package', 'memory', 'tiny'))
    lines = ['import Pinwheel.Hardware.Buffered.ArtifactTinyTapeoutWiring',
        'import Pinwheel.Hardware.Buffered.ArtifactPackageMemory', '',
        'namespace '+namespace, 'open Pinwheel.Hardware Pinwheel.Hardware.Buffered',
        'open ArtifactPackageWiring', '',
        'def sourceHashes : List (String × String) := '+lean_list(
            '⟨'+quoted(m.source)+','+quoted(m.sha256)+'⟩' for m in (package, memory, tiny)), '',
        'def actualFrontend : {w : Nat} → Serial.Input w → FrontSource w']
    for name, (_, tag) in PHYSICAL.items(): lines.append('  | _, .'+tag+' => '+source(bundle['frontend'][name]))
    for name, (_, tag) in STATUS.items(): lines.append('  | _, .status .'+tag+' => '+source(bundle['frontend']['status_'+name]))
    lines += ['', 'def actualController : {w : Nat} → Sram.Input w → CoreSource w']
    for name, (_, tag) in CORE.items(): lines.append('  | _, .base .'+tag+' => '+source(bundle['controller'][name]))
    for index in (0, 1): lines.append('  | _, .q '+str(bool(index)).lower()+' => '+source(bundle['controller']['mem_q'+str(index)]))
    for index, macro in enumerate(bundle['macros']):
        constants = lean_list('⟨'+quoted(n)+','+str(w)+','+str(v)+'⟩' for n, w, v in macro['constants'])
        lines += ['', 'def actualMacro'+str(index)+' : Macro :=', '  ⟨'+','.join([
            quoted(macro['name']), quoted(macro['kind']), quoted(macro['clock']), constants,
            macro['address'], macro['data'], macro['write'], macro['read']])+'⟩']
    lines += ['', 'def actualOutput : {w : Nat} → SerialPackage.Output w → PublicSource w']
    for name in ('miso', 'ready', 'busy', 'levels', 'enabled'): lines.append('  | _, .'+name+' => '+source(bundle['outputs'][name]))
    instances = lean_list('⟨'+quoted(i['name'])+','+quoted(i['kind'])+'⟩' for i in package.instances)
    lines += ['', 'def packageWiring : Wiring :=', '  ⟨'+','.join([quoted(package.name), port_list(package), instances,
        quoted(bundle['frontend_clock']), quoted(bundle['controller_clock']), 'actualFrontend', 'actualController',
        '(fun port => if port then actualMacro1 else actualMacro0)', 'actualOutput'])+'⟩', '',
        'theorem package_correct : Certificate packageWiring where',
        '  name := rfl', '  interface := rfl', '  instances := rfl', '  frontendClock := rfl', '  controllerClock := rfl',
        '  frontend := by', '    intro w port', '    cases port <;> try rfl',
        '    case status output => cases output <;> rfl', '  controller := by',
        '    intro w port', '    cases port', '    case base port => cases port <;> rfl',
        '    case q port => cases port <;> rfl']
    for name in ('macroName', 'macroKind', 'macroClock', 'macroConstants', 'macroAddress', 'macroData', 'macroWrite', 'macroRead'):
        lines.append('  '+name+' := by intro port; cases port <;> rfl')
    lines += ['  outputs := by intro w port; cases port <;> rfl', '',
        'def memoryInventory : ArtifactPackageMemory.Inventory :=', '  ⟨'+','.join([
            quoted(memory.name), port_list(memory), lean_list('⟨'+quoted(i['name'])+','+quoted(i['kind'])+'⟩'
                for i in memory.instances)])+'⟩', '',
        'theorem memory_correct : ArtifactPackageMemory.Certificate memoryInventory := ⟨rfl,rfl,rfl⟩', '',
        'open ArtifactTinyTapeoutWiring', '',
        'def actualEngine : {w : Nat} → Physical w → E w']
    for name, (_, tag) in PHYSICAL.items():
        expression = expand_expression(tiny, bundle['tiny_connections'][name], bundle['tiny_inputs'])
        lines.append('  | _, .'+tag+' => '+expression)
    lines += ['', 'def actualPads : Pad → E 8']
    for name, tag in [('uo_out', 'uo'), ('uio_out', 'uio'), ('uio_oe', 'oe')]:
        lines.append('  | .'+tag+' => '+expand_expression(tiny, tiny.assignments[name], bundle['tiny_inputs']))
    lines += ['', 'def tinyWiring : ArtifactTinyTapeoutWiring.Wiring :=', '  ⟨'+','.join([
        quoted(tiny.name), port_list(tiny), quoted(bundle['tiny_engine']['name']), quoted(bundle['tiny_engine']['kind']),
        quoted(wire(bundle['tiny_connections']['clk'])), 'actualEngine', 'actualPads',
        expand_expression(tiny, tiny.assignments['_unused'], bundle['tiny_inputs'])])+'⟩', '',
        'theorem tiny_correct : ArtifactTinyTapeoutWiring.Certificate tinyWiring where',
        '  name := rfl', '  interface := rfl', '  engineName := rfl', '  engineKind := rfl', '  engineClock := rfl',
        '  engine := by intro w port; cases port <;> rfl', '  outputs := by intro pad; cases pad <;> rfl',
        '  unused := rfl', '', 'end '+namespace, '']
    return '\n'.join(lines)


def corruption_cases():
    """Independent SV edits; every edit must reject the unchanged certificates."""
    return [
        ('package-output', 0, [('assign busy = status_busy;', 'assign busy = status_retained;')]),
        ('controller-clock', 0, [('.clk(clk), .initialize(core_initialize)',
            '.clk(initialize), .initialize(core_initialize)')]),
        ('candidate-q', 0, [('.mem_q0(mem_q0), .mem_q1(mem_q1)',
            '.mem_q0(mem_q1), .mem_q1(mem_q0)')]),
        ('macro-address', 1, [('.A_ADDR(mem_addr0)', '.A_ADDR(mem_addr1)')]),
        ('macro-write', 1, [('.A_WEN(mem_write), .A_REN(mem_read), .A_ADDR(mem_addr0)',
            '.A_WEN(mem_read), .A_REN(mem_read), .A_ADDR(mem_addr0)')]),
        ('macro-mask', 1, [(".A_DOUT(mem_q0), .A_BM(64'hffffffffffffffff)",
            ".A_DOUT(mem_q0), .A_BM(64'hfffffffffffffffe)")]),
        ('macro-enable', 1, [("storage0 (\n    .A_CLK(clk), .A_MEN(1'b1)",
            "storage0 (\n    .A_CLK(clk), .A_MEN(1'b0)")]),
        ('memory-direction', 1, [('output [63:0] mem_q0, mem_q1', 'input [63:0] mem_q0, mem_q1')]),
        ('tt-raw-slice', 2, [('.raw_inputs(ui_in[4:3])', '.raw_inputs(ui_in[5:4])')]),
        ('tt-mask', 2, [('wire active = ena && rst_n;', 'wire active = ena && ena;')]),
        ('tt-receipt-bit', 2, [("{5'b0, busy, ready, miso}", "{5'b0, ready, busy, miso}")]),
        ('tt-clock', 2, [('.clk(clk), .initialize(initialize)', '.clk(rst_n), .initialize(initialize)')]),
    ]
