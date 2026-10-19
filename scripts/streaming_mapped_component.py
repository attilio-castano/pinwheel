"""Actual hierarchy to typed raw-model composition; no synthesis correctness premise.

The source trace mirrors the committed strict word reader and is checked
against it before use. Physical cell/port/FF connections drive the mapped
model. Leaf theorems and per-instance kernel links discharge equivalence.
"""
from collections import defaultdict
from hashlib import sha256
from pathlib import Path
import json
import re

from streaming_mapped_liberty import Library, require
from streaming_mapped_netlist import parse_mapped
from streaming_mapped_certificate import namespace_name

def read_source_trace(rb, path):
    TOP, INPUTS, REGISTERS, OUTPUTS = rb.TOP, rb.INPUTS, rb.REGISTERS, rb.OUTPUTS
    Graph, Node = rb.Graph, rb.Node
    """Interpret actual Yosys word-level JSON, rejecting unsupported semantics."""
    modules = json.loads(path.read_text())["modules"]
    if set(modules) != {TOP}: raise ValueError("Expected exactly the selected backend module")
    m = modules[TOP]
    if m.get("memories") or any(m.get("attributes", {}).get(k, "0").strip("0")
                                for k in ("blackbox", "whitebox")):
        raise ValueError("Unsupported memory or black box")
    expected = {"clk": ("input", 1), **{n: ("input", w) for n, (w, _) in INPUTS.items()},
                **{n: ("output", w) for n, (w, _) in OUTPUTS.items()}}
    ports = m["ports"]
    if {n: (p["direction"], len(p["bits"])) for n, p in ports.items()} != expected:
        raise ValueError("Changed port contract")
    if any("init" in n.get("attributes", {}) for n in m.get("netnames", {}).values()):
        raise ValueError("Implicit register initialization is unsupported")
    graph = Graph()
    graph.cell_trace = {}
    owners = {}
    buses = {}
    interned = {}

    def bind(bits, name):
        if (not bits or len(bits) != graph.nodes[name].width or
                any(type(b) is not int or b < 0 or b in owners for b in bits) or len(set(bits)) != len(bits)):
            raise ValueError("Invalid, aliased or multiply driven bits")
        for k, b in enumerate(bits): owners[b] = (name, k)
        buses[tuple(bits)] = name

    def node(width, op, args=(), value=None):
        n = Node(width, op, args, value)
        if n in interned: return interned[n]
        name = f"n{len(interned)}"
        graph.nodes[name] = n
        interned[n] = name
        return name

    clock = ports["clk"]["bits"][0]
    if type(clock) is not int or clock < 0: raise ValueError("Clock must be a nonconstant input wire")
    owners[clock] = ("clock", 0)
    for name in INPUTS: bind(ports[name]["bits"], name)
    registers, pending = {}, []
    q_names = defaultdict(list)
    for name in REGISTERS:
        bits = m["netnames"].get(name, {}).get("bits")
        if bits is None: raise ValueError("Missing named backend state")
        q_names[tuple(bits)].append(name)
    for name, c in m["cells"].items():
        kind, wires, p = c["type"], c["connections"], c["parameters"]
        if kind != "$dff":
            pending.append((name, c))
            continue
        if (set(p) != {"CLK_POLARITY", "WIDTH"} or int(p["CLK_POLARITY"], 2) != 1
                or set(wires) != {"CLK", "D", "Q"} or wires["CLK"] != ports["clk"]["bits"]
                or c["port_directions"] != {"CLK": "input", "D": "input", "Q": "output"}):
            raise ValueError("Unsupported register clock/parameters")
        matches = q_names[tuple(wires["Q"])]
        if len(matches) != 1 or matches[0] in registers:
            raise ValueError("Changed state mapping")
        n = matches[0]
        if not (len(wires["D"]) == len(wires["Q"]) == int(p["WIDTH"], 2) == REGISTERS[n][0]):
            raise ValueError("Register width mismatch")
        bind(wires["Q"], n)
        registers[n] = wires["D"]
    if set(registers) != set(REGISTERS): raise ValueError("Missing backend registers")

    def signal(bits):
        key = tuple(bits)
        if key in buses: return buses[key]
        if not bits: raise ValueError("Zero-width signal")
        for b in bits:
            if type(b) is str:
                if b not in ("0", "1"): raise ValueError("Unknown/high-impedance bits are unsupported")
            elif type(b) is not int or b < 0:
                raise ValueError("Invalid signal bit")
            elif b == clock: raise ValueError("Clock used as combinational data")
            elif b not in owners: raise KeyError(b)
        parts, pos = [], 0
        while pos < len(bits):
            start = pos
            if type(bits[pos]) is str:
                while pos < len(bits) and type(bits[pos]) is str: pos += 1
                parts.append(node(pos - start, "lit", value=int("".join(reversed(bits[start:pos])), 2)))
            else:
                owner, offset = owners[bits[pos]]
                pos += 1
                while (pos < len(bits) and type(bits[pos]) is int and
                       owners[bits[pos]] == (owner, offset + pos - start)):
                    pos += 1
                width = pos - start
                parts.append(owner if offset == 0 and width == graph.nodes[owner].width
                             else node(width, "slice", (owner,), offset))
        result = parts[-1]
        for part in reversed(parts[:-1]):
            result = node(graph.nodes[result].width + graph.nodes[part].width, "concat", (result, part))
        buses[key] = result
        return result

    while pending:
        progressed = False
        for name, c in pending[:]:
            kind, wires, p = c["type"], c["connections"], c["parameters"]
            binary = {"$and": "and", "$or": "or", "$xor": "xor", "$sub": "sub", "$add": "add"}
            unary = {"$not", "$logic_not", "$reduce_or", "$reduce_and"}
            compare = {"$eq", "$ne", "$lt", "$ge", "$gt"}
            if kind not in binary and kind not in unary and kind not in compare | {"$mux"}:
                raise ValueError(f"Unsupported cell {kind}")
            ins = ["S", "B", "A"] if kind == "$mux" else ["A"] if kind in unary else ["A", "B"]
            if set(wires) != {*ins, "Y"} or c["port_directions"] != {**{n: "input" for n in ins}, "Y": "output"}:
                raise ValueError("Unexpected cell ports")
            width = len(wires["Y"])
            expected_params = {"WIDTH": width} if kind == "$mux" else {
                "A_SIGNED": 0, "A_WIDTH": len(wires["A"]), "Y_WIDTH": width,
                **({"B_SIGNED": 0, "B_WIDTH": len(wires["B"])} if "B" in ins else {})}
            if {k: int(v, 2) for k, v in p.items()} != expected_params:
                raise ValueError("Unsupported signedness/parameters")
            if kind in compare | {"$logic_not", "$reduce_or", "$reduce_and"}:
                if width != 1 or (kind in compare and len(wires["A"]) != len(wires["B"])):
                    raise ValueError("Comparison/reduction width mismatch")
            elif any(len(wires[n]) != width for n in ins if n != "S"):
                raise ValueError("Implicit extension/truncation is unsupported")
            if kind == "$mux" and len(wires["S"]) != 1: raise ValueError("Invalid mux selection")
            try: args = tuple(signal(wires[n]) for n in ins)
            except KeyError: continue
            if kind in binary: value = node(width, binary[kind], args)
            elif kind == "$not": value = node(width, "not", args)
            elif kind in ("$logic_not", "$reduce_or", "$reduce_and"):
                aw = len(wires["A"])
                constant = node(aw, "lit", value=2 ** aw - 1 if kind == "$reduce_and" else 0)
                value = node(1, "eq", (*args, constant))
                if kind == "$reduce_or": value = node(1, "not", (value,))
            elif kind == "$eq": value = node(1, "eq", args)
            elif kind == "$ne": value = node(1, "not", (node(1, "eq", args),))
            elif kind == "$gt": value = node(1, "lt", tuple(reversed(args)))
            elif kind == "$ge": value = node(1, "not", (node(1, "lt", args),))
            elif kind == "$lt": value = node(1, "lt", args)
            else: value = node(width, "mux", args)
            graph.cell_trace[name] = dict(root=value, args=dict(zip(ins,args)), cell=c)
            bind(wires["Y"], value)
            pending.remove((name, c))
            progressed = True
        if not progressed: raise ValueError("Undriven bits or combinational cycle")
    try:
        graph.next = {name: signal(bits) for name, bits in registers.items()}
        graph.outputs = {name: signal(ports[name]["bits"]) for name in OUTPUTS}
    except KeyError as error:
        raise ValueError("Undriven state or output bit") from error
    graph.resolve = signal
    graph.wire_owners = dict(owners)
    return graph


def generate_component(rb, source_json, mapped_json, library, word_modules, *, namespace,
        raw_module, raw_namespace, module_prefix='MappedComponent'):
    """Return (ordered module-text dictionary, complete interpretation metadata).

    `word_modules` maps actual mapped module types to proof module/namespace.
    Every physical instance uses its actual connected input wires and output
    roots. Proposed source pairing never supplies a function; each instance
    must prove the source operation using its interpreted word certificate.
    """
    namespace_name(namespace); namespace_name(raw_namespace); namespace_name(raw_module)
    require(type(module_prefix) is str and re.fullmatch('[A-Za-z_][A-Za-z0-9_]*', module_prefix), 'Invalid component module prefix')
    source_path, mapped_path = Path(source_json), Path(mapped_json)
    require(all(path.is_file() and not path.is_symlink() for path in (source_path,mapped_path)), 'Expected regular component artifacts')
    require(type(library) is Library and library.pinned, 'Expected pinned actual mapped-cell library')
    source_bytes,mapped_bytes=source_path.read_bytes(),mapped_path.read_bytes()
    source,mapped=json.loads(source_bytes),json.loads(mapped_bytes)
    graph = read_source_trace(rb, source_path)
    baseline = rb.read_rtl(source_path)
    require(graph.nodes == baseline.nodes and graph.next == baseline.next and graph.outputs == baseline.outputs,
        'Traced source reader differs from committed strict reader')
    physical = parse_mapped(mapped,rb.TOP,library)
    sm, mm = source['modules'][rb.TOP], mapped['modules'][rb.TOP]
    source_cells = graph.cell_trace
    actual_cells = {name: cell for name,cell in mm['cells'].items() if cell['type'] in word_modules}
    require(source_cells.keys() == actual_cells.keys(), 'Mapped top does not have every original word instance exactly once')
    require(all(cell['type'] in word_modules or library.cells.get(cell['type'],None) is not None and
        library.cells[cell['type']].sequential for cell in mm['cells'].values()),
        'Unexpected primitive logic or unknown module at mapped top boundary')
    require(sm['ports'].keys() == mm['ports'].keys(), 'Changed mapped public interface')
    mapped_fields = {name: mm['netnames'].get(name,{}).get('bits') for name in rb.REGISTERS}
    actual_q = {ff.q:ff for ff in physical.flipflops}
    named_q = [wire for bits in mapped_fields.values() if bits is not None for wire in bits]
    require(set(named_q) == physical.state_bits and len(named_q) == len(set(named_q)), 'Incomplete or aliased physical FF state inventory')
    wire_map, inverse = {'0':'0','1':'1'}, {'0':'0','1':'1'}
    def pair(left,right):
        require(type(left) is type(right) and (type(left) is int or left == right), 'Constant/wire boundary changed')
        require(left not in wire_map or wire_map[left] == right, 'Source wire paired inconsistently')
        require(right not in inverse or inverse[right] == left, 'Mapped wire aliases distinct source wires')
        wire_map[left],inverse[right] = right,left
    for name,port in sm['ports'].items():
        other = mm['ports'][name]
        require(port['direction']==other['direction'] and len(port['bits'])==len(other['bits']), 'Resized or reversed public port')
        if port['direction']=='input':
            for left,right in zip(port['bits'],other['bits']):pair(left,right)
    for name,(width,_) in rb.REGISTERS.items():
        require(mapped_fields[name] is not None and len(mapped_fields[name])==width, 'Mapped register width changed')
        for left,right in zip(sm['netnames'][name]['bits'],mapped_fields[name]):pair(left,right)
    for name,trace in source_cells.items():
        actual = actual_cells[name]
        require(set(actual['connections']) == set(trace['cell']['connections']) and
            actual['port_directions']==trace['cell']['port_directions'] and actual.get('parameters')=={},
            'Mapped word instance interface changed')
        for left,right in zip(trace['cell']['connections']['Y'],actual['connections']['Y']):pair(left,right)
    for name,trace in source_cells.items():
        actual=actual_cells[name]
        for pin,bits in trace['cell']['connections'].items():
            require(len(bits)==len(actual['connections'][pin]) and
                [wire_map.get(wire) for wire in bits]==actual['connections'][pin], 'Actual mapped word wiring differs from source topology')
    for name,port in sm['ports'].items():
        if port['direction']=='output':
            require([wire_map.get(wire) for wire in port['bits']]==mm['ports'][name]['bits'], 'Actual mapped output wiring changed')
    for name,cell in sm['cells'].items():
        if cell['type']!='$dff':continue
        for q,d in zip(cell['connections']['Q'],cell['connections']['D']):
            require(wire_map.get(d)==actual_q[wire_map[q]].d,'Actual FF D differs from complete source topology')
    # The interpreter below resolves actual mapped wires. The source graph is
    # used only as the right side of the independently checked kernel links.
    owners, bodies, links, used_modules = {}, [], [], set()
    def ref(node):
        item=graph.nodes[node]
        if item.op in ('input','reg'):return '('+graph.expression(item,None)+')'
        return f'({raw_namespace}.RTL.{node} i s)'
    for name,(width,_) in rb.INPUTS.items():
        for index,wire in enumerate(mm['ports'][name]['bits']):owners[wire]=(name,index,width,None,ref(name))
    for name,(width,_) in rb.REGISTERS.items():
        for index,wire in enumerate(mapped_fields[name]):owners[wire]=(name,index,width,None,ref(name))
    def bundle(bits):
        parts,used=[],set();at=0
        while at<len(bits):
            start=at;wire=bits[at]
            if type(wire) is str:
                require(wire in ('0','1'),'Functional X/Z at component boundary')
                while at<len(bits) and type(bits[at]) is str:at+=1
                parts.append(f'{int("".join(reversed(bits[start:at])),2)}#{at-start}')
            else:
                require(wire in owners,'Mapped combinational source unavailable or cyclic')
                owner,offset,width,link,value=owners[wire];at+=1
                while at<len(bits) and type(bits[at]) is int and bits[at] in owners and owners[bits[at]][0]==owner and owners[bits[at]][1]==offset+at-start:at+=1
                if link:used.add(link)
                parts.append(value if offset==0 and at-start==width else f'({value}).extractLsb\' {offset} {at-start}')
        result=parts[-1]
        for part in reversed(parts[:-1]):result=f'({result}) ++ ({part})'
        return result,used
    for index,(name,trace) in enumerate(source_cells.items()):
        cell=actual_cells[name];spec=word_modules[cell['type']]
        require(set(spec)>={'module','namespace'},'Missing word proof module/namespace')
        body_hash=sha256(json.dumps(mapped['modules'][cell['type']],sort_keys=True,separators=(',',':')).encode()).hexdigest()
        if 'module_sha256' in spec:require(spec['module_sha256']==body_hash,'Word proof belongs to another actual module body')
        if 'netlist_sha256' in spec:require(spec['netlist_sha256']==sha256(mapped_bytes).hexdigest(),'Word proof belongs to another mapped artifact')
        namespace_name(spec['namespace']);namespace_name(spec['module']);used_modules.add(spec['module'])
        ports=sorted(pin for pin,direction in cell['port_directions'].items() if direction=='input')
        args,dependencies=[],set()
        for pin in ports:
            value,used=bundle(cell['connections'][pin]);args.append('('+value+')');dependencies|=used
        node=f'cell{index}';value=f'{node} i s';width=len(cell['connections']['Y'])
        bodies.append(f'def {node} (i : Values {rb.INPUT_TYPE}) (s : Values {rb.REGISTER_TYPE}) : BitVec {width} := {spec["namespace"]}.actual '+ ' '.join(args))
        proof=[f'theorem link_{node} (i : Values {rb.INPUT_TYPE}) (s : Values {rb.REGISTER_TYPE}) :',
            f'    {value} = {ref(trace["root"])} := by',f'  unfold {node}']
        if dependencies:proof.append('  rw ['+','.join(sorted(dependencies))+']')
        source_args=[ref(trace['args'][pin]) for pin in ports]
        proof.append(f'  exact {spec["namespace"]}.raw_correct '+' '.join(source_args))
        links.append('\n'.join(proof))
        for position,wire in enumerate(cell['connections']['Y']):
            require(type(wire) is int and wire not in owners,'Multiple mapped word output drivers')
            owners[wire]=(node,position,width,'link_'+node,'('+value+')')
    roots={};root_dependencies={}
    for name,bits in mapped_fields.items():
        d=[actual_q[q].d for q in bits];roots['next',name],root_dependencies['next',name]=bundle(d)
    for name in rb.OUTPUTS:roots['output',name],root_dependencies['output',name]=bundle(mm['ports'][name]['bits'])
    header=(f'open Pinwheel.Hardware Pinwheel.Hardware.Streaming\nnamespace {namespace}\n'
        'set_option maxRecDepth 100000\nset_option maxHeartbeats 8000000\nset_option linter.unusedVariables false\n')
    graphs_name=module_prefix+'Graph';proof_name=module_prefix+'Proof'
    # Links are interleaved with definitions so each parent is available before
    # a child is interpreted. This preserves real physical instance identity.
    ordered=[]
    for body,link in zip(bodies,links):ordered += [body,link]
    graph_text='\n'.join('import '+name for name in [raw_module,*sorted(used_modules)])+'\n'+header+'\n'+'\n\n'.join(ordered)+'\nend '+namespace+'\n'
    model=[];endpoint=[]
    for kind,interface,method,result in [('next',rb.REGISTERS,'step',rb.REGISTER_TYPE),('output',rb.OUTPUTS,'observe',rb.OUTPUT_TYPE)]:
        model.append(f'def {method} (i : Values {rb.INPUT_TYPE}) (s : Values {rb.REGISTER_TYPE}) : Values {result}')
        consumed=set()
        if kind=='next':
            for family,ctor,count,idx_width in rb.FAMILIES:
                values=', '.join('('+roots[kind,'r_'+family+str(j)]+')' for j in range(count))
                model.append(f'  | _, .{ctor} k => (#[{values}])[k.toNat]\'(by exact k.isLt)')
                consumed.update('r_'+family+str(j) for j in range(count))
        for name,(_,ctor) in interface.items():
            if name not in consumed:model.append(f'  | _, {ctor} => '+roots[kind,name])
            proof=[f'theorem endpoint_{kind}_{name} (i : Values {rb.INPUT_TYPE}) (s : Values {rb.REGISTER_TYPE}) :',
                f'    {method} i s ({ctor}) = {rb.CIRCUIT}.{method} i s ({ctor}) := by',
                '  change '+roots[kind,name]+' = _']
            if root_dependencies[kind,name]:proof.append('  rw ['+','.join(sorted(root_dependencies[kind,name]))+']')
            original_method='rtlStep' if kind=='next' else 'rtlObserve'
            proof += [f'  change {raw_namespace}.{original_method} i s ({ctor}) = _',
                f'  exact {raw_namespace}.{method}_correct i s ({ctor})']
            endpoint.append('\n'.join(proof))
    universal=[]
    for method,kind,ty,interface in [('step','next',rb.REGISTER_TYPE,rb.REGISTERS),('observe','output',rb.OUTPUT_TYPE,rb.OUTPUTS)]:
        universal += [f'theorem {method}_correct (i : Values {rb.INPUT_TYPE}) (s : Values {rb.REGISTER_TYPE})',
            f'    (field : {ty} w) : {method} i s field = {rb.CIRCUIT}.{method} i s field := by', '  cases field with']
        consumed=set()
        if kind=='next':
            for family,ctor,count,idx_width in rb.FAMILIES:
                term='(fun j => Fin.elim0 j)'
                for j in reversed(range(count)):term=f'(Fin.cases (endpoint_next_r_{family}{j} i s) {term})'
                universal += [f'  | {ctor} k =>',f'    have equal : ∀ j : Fin {count}, step i s (.{ctor} (BitVec.ofFin j)) =',
                    f'        {rb.CIRCUIT}.step i s (.{ctor} (BitVec.ofFin j)) := {term}','    exact equal k.toFin']
                consumed.update('r_'+family+str(j) for j in range(count))
        if rb.KIND=='core':
            from streaming_readback import CORE_REGISTERS, CORE_OUTPUTS
            entries=CORE_REGISTERS if kind=='next' else CORE_OUTPUTS
            for name,_,ctor in entries:universal.append(f'  | {ctor} => exact endpoint_{kind}_'+('r_' if kind=='next' else '')+name+' i s')
        else:
            from streaming_readback import FRONTEND_REGISTERS,CORE_INPUTS
            if kind=='next':
                for name,_,ctor in FRONTEND_REGISTERS:universal.append(f'  | {ctor} => exact endpoint_next_r_{name} i s')
            else:
                universal += ['  | miso => exact endpoint_output_miso i s','  | ready => exact endpoint_output_ready i s','  | core field =>','    cases field with']
                for name,_,ctor in CORE_INPUTS:
                    case='«initialize»' if ctor=='initialize' else ctor
                    universal.append(f'    | {case} => exact endpoint_output_core_{name} i s')
    universal += [f'def behavior : Pinwheel.Hardware.Streaming.Package.Behavior {rb.INPUT_TYPE} {rb.REGISTER_TYPE} {rb.OUTPUT_TYPE} := ⟨step,observe⟩']
    proof_text='import '+graphs_name+'\n'+header+'\n'+'\n\n'.join(model+endpoint+universal)+'\nend '+namespace+'\n'
    metadata=dict(top=rb.TOP,namespace=namespace,modules=[graphs_name,proof_name],source_word_instances=len(source_cells),
        mapped_comb_cells=len(physical.gates),mapped_ff_bits=len(physical.flipflops),register_fields=len(rb.REGISTERS),
        outputs=len(rb.OUTPUTS),word_modules=word_modules,raw_module=raw_module,raw_namespace=raw_namespace,
        source_sha256=sha256(source_bytes).hexdigest(),mapped_sha256=sha256(mapped_bytes).hexdigest(),liberty_sha256=library.sha256,
        module_sha256={name:sha256(json.dumps(mapped['modules'][name],sort_keys=True,separators=(',',':')).encode()).hexdigest()
            for name in sorted({cell['type'] for cell in actual_cells.values()})})
    require(source_path.read_bytes()==source_bytes and mapped_path.read_bytes()==mapped_bytes,'Component artifacts changed during interpretation')
    return {graphs_name:graph_text,proof_name:proof_text},metadata

