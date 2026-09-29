"""Artifact interpretation for the retained paired controller.

Reuse the restricted backend importer in a private module instance: its port
and state contract is replaced, not relaxed. No installed importer is mutated.
MLIR is an untrusted proof hint; only Lean can connect it to the typed graph.
"""
import importlib.util
import json
from pathlib import Path
import sys
from collections import defaultdict

ROOT = Path(__file__).resolve().parents[1]


def read_json(path):
    def unique(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError('Duplicate JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(Path(path).read_text(), object_pairs_hook=unique)


def check_interface(rb, interface):
    for name, expected in [('inputs', rb.INPUTS), ('registers', rb.REGISTERS),
                           ('outputs', rb.OUTPUTS)]:
        entries = interface[name]
        actual = {e['name']: e['width'] for e in entries}
        if len(actual) != len(entries) or any(type(e['width']) is not int for e in entries):
            raise ValueError('Invalid interface entries: ' + name)
        if actual != {n: w for n, (w, _) in expected.items()}:
            raise ValueError('Changed paired interface: ' + name)
        if name == 'registers' and any(e['reference'] != e['name'] for e in entries):
            raise ValueError('Changed register references')


def check_cuts(cuts, source):
    if len(cuts) != 45 or len({c['node'] for c in cuts}) != 45:
        raise ValueError('Expected the 45 distinct typed bindings')
    for cut in cuts:
        if not cut['node'].startswith('Pinwheel.Hardware.Storage.PairedController.Computation.'):
            raise ValueError('Invalid computation label')
        label = cut['label']
        if not label.startswith('%') or label[1:] not in source.nodes:
            raise ValueError('Unknown shared wire hint')
        if source.nodes[label[1:]].width != 64:
            raise ValueError('Shared wire hint has the wrong width')


def backend(kind):
    if kind not in ('core', 'chip'):
        raise ValueError('Unknown paired artifact kind')
    name = '_paired_readback_' + kind
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts/backend_readback.py')
    rb = importlib.util.module_from_spec(spec)
    sys.modules[name] = rb
    spec.loader.exec_module(rb)
    rb.TOP = 'pinwheel_paired_core_controller' if kind == 'core' else 'pinwheel_paired_controller'
    rb.INPUTS = {n: (w, f'.base .{n}') for n, w in
                 [('init', 1), ('reset', 1), ('command', 3), ('data', 64), ('incoming', 2)]}
    rb.INPUTS['mem_q0'] = (64, '.q false')
    rb.REGISTERS = {}
    for b in (0, 1):
        bank = 'true' if b else 'false'
        rb.REGISTERS.update({f'r_parameter_b{b}_w{k}': (20, f'.parameter {bank} {k}') for k in range(32)})
        rb.REGISTERS[f'r_boot_b{b}'] = (32, f'.boot {bank}')
        rb.REGISTERS[f'r_idle_b{b}'] = (6, f'.idle {bank}')
    rb.REGISTERS.update({'r_' + n: (w, '.' + ctor) for n, w, ctor in [
        ('active',1,'active'), ('valid',1,'valid'), ('pending',1,'pending'), ('cursor',9,'cursor'),
        ('current',32,'current'), ('cached',20,'cached'), ('mode',3,'mode'),
        ('remaining',8,'remaining'), ('wait_left',8,'waitLeft'), ('levels',3,'levels'),
        ('enabled',3,'enabled'), ('samples',16,'samples'), ('payload',8,'payload')]})
    rb.OUTPUTS = {'loader_' + n: (w, f'.base (.control (.state .{n}))')
                  for n,w in [('active',1),('valid',1),('pending',1),('cursor',9)]}
    rb.OUTPUTS.update({'loader_' + n: (1, f'.base (.control .{n})') for n in ['push','commit','start','rejected']})
    rb.OUTPUTS.update({n: (w, f'.base (.core (.state .{ctor}))') for n,w,ctor in [
        ('mode',3,'mode'),('pc',8,'pc'),('remaining',8,'remaining'),('wait_left',8,'waitLeft'),
        ('levels',3,'levels'),('enabled',3,'enabled')]})
    rb.OUTPUTS.update({f'sample{k}': (1, f'.base (.core (.state (.sample ⟨{k}, by decide⟩)))') for k in range(16)})
    rb.OUTPUTS.update({n: (w, f'.base (.core .{ctor})') for n,w,ctor in
                       [('read_a',8,'readA'),('read_b',8,'readB'),('busy',1,'busy')]})
    rb.OUTPUTS.update({'mem_addr0': (9, '.port (.address false)'), 'mem_data': (64, '.port .data'),
                       'mem_write': (1, '.port .write'), 'mem_read': (1, '.port .read')})
    if kind == 'chip':
        rb.REGISTERS = {n: (w, f'.inner (.inner (.inner (.inner ({ctor}))))')
                        for n,(w,ctor) in rb.REGISTERS.items()}
        rb.REGISTERS.update({'r_serial_' + n: (w, f'.inner (.inner (.inner (.extra .{ctor})))')
                            for n,w,ctor in [('sck_prev',1,'sckPrev'),('count',7,'count'),
                                             ('shift',64,'shift'),('command',3,'command'),('fire',1,'fire')]})
        for stage in ['first','second']:
            rb.REGISTERS.update({f'r_pin_{stage}_{n}': (w, f'.inner (.inner (.extra (.{stage} .{n})))')
                                for n,w in [('init',1),('sck',1),('mosi',1),('csn',1),('incoming',2)]})
        rb.REGISTERS.update({'r_result_' + n: (w, f'.extra .{ctor}') for n,w,ctor in [
            ('reset_first',1,'resetFirst'),('reset_second',1,'resetSecond'),
            ('page_first',2,'pageFirst'),('page_second',2,'pageSecond'),
            ('control_first',2,'controlFirst'),('control_second',2,'controlSecond'),
            ('consume_prev',1,'consumePrev'),('clear_prev',1,'clearPrev'),('was_active',1,'wasActive'),
            ('samples',16,'samples'),('outcome',3,'outcome'),('valid',1,'valid'),
            ('overrun',1,'overrun'),('rejected',1,'rejected')]})
        rb.INPUTS = {n: (w, f'.base .{ctor}') for n,w,ctor in
                     [('ui_in',8,'uiIn'),('uio_in',8,'uioIn'),('ena',1,'ena'),('rst_n',1,'rstN')]}
        rb.INPUTS['mem_q0'] = (64, '.q false')
        rb.OUTPUTS = {n: entry for n,entry in rb.OUTPUTS.items() if n.startswith('mem_')}
        rb.OUTPUTS.update({n: (8, f'.base .{ctor}') for n,ctor in
                          [('uo_out','uoOut'),('uio_out','uioOut'),('uio_oe','uioOe')]})
    rb.HEADER = '''import Pinwheel.Hardware.Storage.PairedSession
open Pinwheel.Hardware Pinwheel.Hardware.Storage
open PairedController
namespace Pinwheel.Artifact.Paired
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
'''
    return rb


def adapt(text, kind='core'):
    text = text.replace('Values Machine.Input', 'Values Input').replace(
        'namespace Pinwheel.Artifact.Backend', 'namespace Pinwheel.Artifact.Paired').replace(
        'end Pinwheel.Artifact.Backend', 'end Pinwheel.Artifact.Paired')
    if kind == 'chip':
        text = text.replace('Values Input', 'Values (SramController.Reads Chip.Pin)').replace(
            'Values Register', 'Values PairedController.FullRegister')
    return text



def _suggest_partitions(rb, source, rtl, *, oracle):
    """Suggest acyclic proof partitions. Simulation never discharges a theorem."""
    ss, rs = source.signatures(1024), rtl.signatures(1024)
    candidates = defaultdict(list)
    for name, sig in rs.items(): candidates[sig].append(name)
    forced = {source.next[n]: rtl.next[n] for n in rb.REGISTERS}
    forced.update({source.outputs[n]: rtl.outputs[n] for n in rb.OUTPUTS})
    scuts, rcuts, pairs = {}, set(), []
    for sn, node in source.nodes.items():
        if node.op in ("lit", "input", "reg"): continue
        if sn in forced:
            rn = forced[sn]
        else:
            if not (node.op == 'mux' and node.width >= 16 or node.op in ('sub', 'and', 'not')) or len(set(ss[sn][1])) == 1: continue
            choices = candidates.get(ss[sn], [])
            if not choices: continue
            rn = min(choices, key=lambda n: (rtl.nodes[n].op != node.op, rtl.nodes[n].op in ("reg", "input")))
        variables, definitions, dependencies = {}, set(), set()
        allowed = set(rcuts)

        def variable(n):
            item = rtl.nodes[n]
            if item.op in ("input", "reg"):
                key = (item.width, item.op, item.value)
            else:
                used.add(n)
                key = (item.width, "rtl", n)
            if key not in variables: variables[key] = len(variables)
            return (item.width, "var", (), variables[key])

        def view(n, base):
            if n == base: return variable(base)
            item = rtl.nodes[n]
            definitions.add(f"RTL.{n}")
            return (item.width, item.op, tuple(view(a, base) for a in item.args), item.value)

        def expand(g, n, cuts, namespace, root=False):
            key_memo = (namespace, n, root)
            if key_memo in memo: return memo[key_memo]
            item = g.nodes[n]
            if item.op in ("reg", "input"): return variable(n)
            if not root and namespace == "Source" and n in scuts:
                index, matching, base = scuts[n]
                if base in allowed:
                    dependencies.add(index)
                    result = view(matching, base)
                    memo[key_memo] = result
                    return result
            if not root and namespace == "RTL" and n in allowed:
                return variable(n)
            definitions.add(f"{namespace}.{n}")
            result = (item.width, item.op, tuple(expand(g, child, cuts, namespace) for child in item.args), item.value)
            memo[key_memo] = result
            return result

        while True:
            variables, definitions, dependencies = {}, set(), set()
            memo, used = {}, set()
            left = expand(source, sn, scuts, "Source", root=True)
            lcuts = set(used)
            used = set()
            right = expand(rtl, rn, rcuts, "RTL", root=rn not in rcuts)
            rc = set(used)
            remove = lcuts ^ rc
            if not remove: break
            allowed -= remove
        sizes = {}
        def size(t):
            if id(t) not in sizes: sizes[id(t)] = 1 + sum(size(a) for a in t[2])
            return sizes[id(t)]
        pair = {"source": sn, "rtl": rn, "left": left, "right": right,
                "variables": tuple(variables), "definitions": sorted(definitions),
                "dependencies": sorted(dependencies), "size": size(left) + size(right)}
        if pair["size"] > 2000 and sn not in forced:
            continue
        if not oracle(pair):
            if sn in forced:
                print(f"unproved endpoint suggestion {sn}: {pair['size']}", flush=True)
            continue
        idx = len(pairs)
        pairs.append(pair)
        if len(pairs) % 500 == 0: print(f"partitioned {len(pairs)} ({sn})", flush=True)
        base = rtl.views.get(rn, rn)
        if (node.op == 'mux' and node.width >= 16 or node.op in ('sub', 'and', 'not')):
            scuts[sn] = (idx, rn, base)
            rcuts.add(base)
    return pairs


def partitions(rb, source, rtl, solver):
    """Suggest cuts, then expand any RTL equations needed to retain correlation.

    Simulation and SMT only guide decomposition. Every resulting equality is
    proved in Lean for all values. Constraint elimination unfolds actual gates;
    it does not add assumptions to the certificate.
    """
    oracle = rb.cut_oracle(solver)
    pairs = _suggest_partitions(rb, source, rtl, oracle=oracle)
    endpoints = [(source.next[n], rtl.next[n]) for n in rb.REGISTERS]
    endpoints += [(source.outputs[n], rtl.outputs[n]) for n in rb.OUTPUTS]
    matches = {(p['source'], p['rtl']) for p in pairs}
    for sn, rn in endpoints:
        if (sn, rn) in matches:
            continue
        if source.nodes[sn].op in ('input', 'reg', 'lit') and sn == rn:
            continue
        pair = constrained_pair(rb, source, rtl, pairs, sn, rn, oracle)
        pair = expand_constraints(minimize_constraints(rb, pair, solver))
        if not oracle(pair):
            raise ValueError('Expanded endpoint proposal is invalid: ' + sn)
        pairs.append(pair)
        matches.add((sn, rn))
    return pairs


def expand_constraints(pair):
    """Inline a selected acyclic subset of concrete RTL gate equations."""
    substitutions = {a[3]: b for a, b in pair['constraints']}
    variables, memo, visiting = {}, {}, set()
    def expand(t):
        w, op, args, value = t
        if op == 'var':
            if value in substitutions:
                if value in visiting:
                    raise ValueError('Cyclic gate equation')
                if value not in memo:
                    visiting.add(value)
                    memo[value] = expand(substitutions[value])
                    visiting.remove(value)
                return memo[value]
            if value not in variables:
                variables[value] = len(variables)
            return (w, op, (), variables[value])
        return (w, op, tuple(expand(a) for a in args), value)
    left, right = expand(pair['left']), expand(pair['right'])
    result = dict(pair, left=left, right=right,
        variables=tuple(pair['variables'][j] for j in variables),
        definitions=sorted(set(pair['definitions']) |
                           {'RTL.' + pair['variables'][j][2] for j in substitutions}))
    result['expanded_gate_equations'] = len(substitutions)
    del result['constraints']
    return result


def constrained_pair(rb, source, rtl, pairs, sn, rn, oracle):
    source_order = {n:k for k,n in enumerate(source.nodes)}
    cuts = {p['source']: (k,p['rtl']) for k,p in enumerate(pairs)
            if source_order[p['source']] < source_order[sn]}
    variables, definitions, dependencies, memo = {}, set(), set(), {}
    def variable(n):
        node = rtl.nodes[n]
        key = (node.width, node.op if node.op in ('input','reg') else 'rtl', n)
        if key not in variables:
            variables[key] = len(variables)
        return (node.width, 'var', (), variables[key])
    def expand(n):
        if n in memo:
            return memo[n]
        node = source.nodes[n]
        if node.op in ('input','reg'):
            return variable(n)
        if n != sn and n in cuts:
            k,match = cuts[n]
            dependencies.add(k)
            return variable(match)
        definitions.add('Source.'+n)
        result = (node.width,node.op,tuple(expand(a) for a in node.args),node.value)
        memo[n] = result
        return result
    left,right = expand(sn),variable(rn)
    constraints, constrained = [], set()
    def query():
        conditions = (1,'lit',(),1)
        for lhs,rhs in constraints:
            conditions = (1,'and',(conditions,(1,'eq',(lhs,rhs),None)),None)
        bad = (1,'and',(conditions,(1,'not',((1,'eq',(left,right),None),),None)),None)
        return dict(left=bad,right=(1,'lit',(),0),variables=tuple(variables))
    for depth in range(len(rtl.nodes)+1):
        if oracle(query()):
            print(f'constrained endpoint {sn}: {len(constraints)} checked equations',flush=True)
            return dict(source=sn,rtl=rn,left=left,right=right,variables=tuple(variables),
                        definitions=sorted(definitions),dependencies=sorted(dependencies),
                        constraints=constraints,size=len(definitions)+len(constraints))
        frontier = [(w,kind,n) for w,kind,n in variables if kind == 'rtl' and n not in constrained]
        if not frontier:
            raise ValueError('No valid endpoint interpretation: '+sn)
        for w,_,n in frontier:
            node=rtl.nodes[n]
            rhs=(w,node.op,tuple(variable(a) for a in node.args),node.value)
            constraints.append((variable(n),rhs)); constrained.add(n)
    raise ValueError('Unbounded endpoint decomposition')


def helper_source(rb, pairs):
    lines = ['import Lean.Elab.Command\nimport Pinwheel.Hardware.Readback.Boolean\n' + rb.HEADER,
             'set_option linter.unusedSimpArgs false',
             """theorem low_three_high (v : BitVec 32) :
    (v.extractLsb' 0 3).toNat < 4 ↔ v.extractLsb' 2 1 ≠ 1 := by
  simp only [BitVec.toNat_ne, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  change v.toNat / 1 % 8 < 4 ↔ v.toNat / 4 % 2 ≠ 1
  omega

theorem low_eight_sub (v : BitVec 9) :
    (v - 32#9).extractLsb' 0 8 = v.extractLsb' 0 8 - 32#8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  change ((480 + v.toNat) % 512) / 1 % 256 = (224 + v.toNat / 1 % 256) % 256
  omega
"""]
    for n in (288, 289, 290):
        lines.append(f'theorem cursor_eq_{n} (v : BitVec 9) : (v = {n}#9) ↔ v.toNat = {n} := BitVec.toNat_inj.symm')
    for k, p in enumerate(pairs):
        params = ' '.join(f'(x{j} : BitVec {w})' for j, (w, _, _) in enumerate(p['variables']))
        lines.append(f"theorem local_{k} {params} :\n"
                     f"    {rb.render_tree(p['left'])} = {rb.render_tree(p['right'])} := by\n"
                     "  try simp only [low_eight_sub]\n"
                     "  try simp only [BitVec.sub_eq_add_neg, BitVec.extractLsb'_append_eq_right,\n"
                     "    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb', BitVec.extractLsb'_eq_self,\n"
                     "    show (4#3).toNat = 4 from rfl, low_three_high, cursor_eq_288, cursor_eq_289, cursor_eq_290]\n"
                     "  all_goals first\n"
                     "  | (bv_normalize; first | omega | grind (splits := 64))\n"
                     "  | (simp [Pinwheel.Hardware.Readback.eq_bits, Fin.forall_fin_succ,\n"
                     "      BitVec.getElem_append, BitVec.getElem_extractLsb']; all_goals grind (splits := 64))\n")
        if k % 100 == 0:
            lines.append(f'run_cmd IO.eprintln "checked local {k}"')
    return '\n'.join(lines) + '\nend Pinwheel.Artifact.Paired\n'


def links_source(rb, source, rtl, pairs):
    return rb.links_source(source, rtl, pairs, 'LocalProofs', 'Graphs')


def model_source(rb, graph, kind):
    """Total typed interfaces for every declared state and observable port."""
    itype = 'Input' if kind == 'core' else '(SramController.Reads Chip.Pin)'
    rtype = 'Register' if kind == 'core' else 'FullRegister'
    otype = '(SramController.Out Loader.Machine.Output)' if kind == 'core' else '(SramController.Out Chip.Output)'
    lines = ['import Graphs\n' + rb.HEADER]
    def term(node):
        return rb.graph_value(graph, node, 'RTL')
    for operation, interface, roots, result in [('Step',rb.REGISTERS,graph.next,rtype),('Observe',rb.OUTPUTS,graph.outputs,otype)]:
        lines.append(f'def rtl{operation} (i : Values {itype}) (s : Values {rtype}) : Values {result}')
        for name,(_,ctor) in interface.items():
            if name.startswith('r_parameter_') or (kind == 'core' and name.startswith('sample')):
                continue
            if name == 'mem_addr0':
                ctor = '.port (.address _)'
            lines.append(f'  | _, {ctor} => {term(roots[name])}')
        if operation == 'Step':
            pattern = '.parameter b k' if kind == 'core' else '.inner (.inner (.inner (.inner (.parameter b k))))'
            lines.append(f'  | _, {pattern} => if b then')
            for bank in (1,0):
                values = ', '.join('('+term(roots[f'r_parameter_b{bank}_w{k}'])+')' for k in range(32))
                lines.append(f'      (#[{values}])[k.toNat]\''+'(by exact k.isLt)'+(' else' if bank else ''))
            if kind == 'chip':
                lines.append('  | _, .inner (.extra r) => nomatch r')
        elif kind == 'core':
            values = ', '.join('('+term(roots[f'sample{k}'])+')' for k in range(16))
            lines.append(f'  | _, .base (.core (.state (.sample k))) => (#[{values}])[k.val]\''+'(by exact k.isLt)')
    lines.append(f'def rtlComponent : PairedComposition.Component {itype} {rtype} {otype} := ⟨rtlStep, rtlObserve⟩')
    return '\n'.join(lines)+'\nend Pinwheel.Artifact.Paired\n'


def endpoints_source(rb, source, rtl, pairs, kind):
    itype='Input' if kind=='core' else '(SramController.Reads Chip.Pin)'
    rtype='Register' if kind=='core' else 'FullRegister'
    matches={(p['source'],p['rtl']):k for k,p in enumerate(pairs)}
    lines=['import Sources\nimport Links\nimport Model\nimport Design\n'+rb.HEADER]
    for operation,roots,actual,interface in [('next',source.next,rtl.next,rb.REGISTERS),('output',source.outputs,rtl.outputs,rb.OUTPUTS)]:
        method='Step' if operation=='next' else 'Observe'
        action='step' if operation=='next' else 'observe'
        for name,sn in roots.items():
            rn=actual[name];ctor=interface[name][1]
            lines.append(f'theorem rtl_{operation}_{name} (i : Values {itype}) (s : Values {rtype}) :\n'
                         f'    rtl{method} i s ({ctor}) = reference.{action} i s ({ctor}) := by\n'
                         f'  change ({rb.graph_value(rtl,rn,"RTL")}) = _')
            if (sn,rn) in matches:
                lines.append(f'  exact (link_{matches[(sn,rn)]} i s).symm.trans (source_{operation}_{name} i s)')
            else:
                lines.append(f'  exact source_{operation}_{name} i s')
    return '\n'.join(lines)+'\nend Pinwheel.Artifact.Paired\n'


def design_source(rb,kind):
    text=rb.HEADER+'''def validationGraph : PairedComposition.Component Input Register (SramController.Out Loader.Machine.Output) where
  step := fun i s => body.step (PairedSemantics.inputs PairedValidation.bindings i s) s
  observe := fun i s => body.observe (PairedSemantics.inputs PairedValidation.bindings i s) s

theorem validation_graph_eq : validationGraph = PairedComposition.graph := by
  simp only [validationGraph, PairedComposition.graph, PairedSemantics.validation_inputs_eq]
'''
    if kind=='core':
        text+='abbrev reference := validationGraph\n'
        text+='def coreInputs (i : Values Input) (_s : Values Register) : Values Input := i\n'
        text+='def coreState (s : Values Register) : Values Register := s\n'
    else:
        text+='''abbrev reference := PairedComposition.packaged validationGraph

def coreState (s : Values FullRegister) : Values Register :=
  Extended.innerValues (Extended.innerValues (Extended.innerValues (Extended.innerValues s)))

def coreInputs (i : Values (SramController.Reads Chip.Pin)) (s : Values FullRegister) : Values Input :=
  (SramController.bypass Serial.receiver).feed
    ((SramController.bypass Feeder.sampler).feed
      ((SramController.bypass Chip.pinMap).feed i (Extended.extraValues (Extended.innerValues s)))
      (Extended.extraValues (Extended.innerValues (Extended.innerValues s))))
    (Extended.extraValues (Extended.innerValues (Extended.innerValues (Extended.innerValues s))))
'''
    return text+'\nend Pinwheel.Artifact.Paired\n'


def hint_equations_source(rb,source,cuts,kind):
    itype='Input' if kind=='core' else '(SramController.Reads Chip.Pin)'
    rtype='Register' if kind=='core' else 'FullRegister'
    lines=['import Hints\nimport Design\nimport Lean.Elab.Command\n'+rb.HEADER,
           f'def environment (i : Values {itype}) (s : Values {rtype}) : PairedSemantics.Environment']
    for cut in cuts:
        name=cut['node'].split('.')[-1];node=cut['label'][1:]
        lines.append(f'  | .{name} => {rb.graph_value(source,node,"Source")}')
    lines.append(f'def scope (i : Values {itype}) (s : Values {rtype}) : Values GraphInput :=\n'
                 '  PairedSemantics.graphValues (coreInputs i s) (environment i s)')
    for k,cut in enumerate(cuts):
        name=cut['node'].split('.')[-1]
        lines.append(f'theorem hint_{name} (i : Values {itype}) (s : Values {rtype}) :\n'
                     f'    environment i s .{name} = (PairedValidation.bindings[{k}]\'(by decide)).2.eval (scope i s) (coreState s) := by\n  rfl\n')
        lines.append(f'run_cmd IO.eprintln "checked shared equation {name}"')
    return '\n'.join(lines)+'\nend Pinwheel.Artifact.Paired\n'


def equations_source(rb,cuts,kind):
    itype='Input' if kind=='core' else '(SramController.Reads Chip.Pin)'
    rtype='Register' if kind=='core' else 'FullRegister'
    lines=['import HintEquations\n'+rb.HEADER,
           f'theorem equations (i : Values {itype}) (s : Values {rtype}) :\n'
           '    PairedSemantics.Equations PairedValidation.bindings (scope i s) (coreState s) := by\n'
           '  intro name e hn\n'
           '  simp only [PairedValidation.bindings, bindings, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hn\n'
           '  rcases hn with '+' | '.join('h' for _ in cuts)+'\n  all_goals cases h']
    lines.extend('  · exact hint_'+c['node'].split('.')[-1]+' i s' for c in cuts)
    lines.append(f'''theorem scope_correct (i : Values {itype}) (s : Values {rtype}) :
    (PairedSemantics.inputs PairedValidation.bindings (coreInputs i s) (coreState s) : Values GraphInput) =
      (fun {{_}} p => scope i s p) := by
  funext w p
  cases p with
  | base p => rfl
  | q b => rfl
  | node name =>
    exact PairedSemantics.evaluate_solution PairedValidation.bindings [] (coreInputs i s) (coreState s) (fun _ => 0)
      (environment i s) PairedSemantics.validation_bindings_ordered (equations i s)
      (fun _ h => nomatch h) name (PairedSemantics.validation_complete name)
''')
    return '\n'.join(lines)+'\nend Pinwheel.Artifact.Paired\n'


def sources_source(rb,source,kind):
    itype='Input' if kind=='core' else '(SramController.Reads Chip.Pin)'
    rtype='Register' if kind=='core' else 'FullRegister'
    lines=['import Equations\n'+rb.HEADER]
    for operation,roots,interface in [('next',source.next,rb.REGISTERS),('output',source.outputs,rb.OUTPUTS)]:
        action='step' if operation=='next' else 'observe'
        for name,node in roots.items():
            ctor=interface[name][1];lhs=rb.graph_value(source,node,'Source')
            lines.append(f'theorem source_{operation}_{name} (i : Values {itype}) (s : Values {rtype}) :\n'
                         f'    {lhs} = reference.{action} i s ({ctor}) := by')
            if kind=='core':
                lines.append('  change _ = (body.'+operation+' ('+ctor+')).eval (PairedSemantics.inputs PairedValidation.bindings (coreInputs i s) (coreState s)) (coreState s)\n  rw [scope_correct]\n  rfl')
            else:
                lines.append('  simp only [reference, PairedComposition.packaged, PairedComposition.observed, PairedComposition.fed, validationGraph]\n  have h := scope_correct i s\n  dsimp only [coreInputs, coreState] at h\n  try rw [h]\n  rfl')
    return '\n'.join(lines)+'\nend Pinwheel.Artifact.Paired\n'


def proof_source(rb,kind):
    itype='Input' if kind=='core' else '(SramController.Reads Chip.Pin)'
    rtype='Register' if kind=='core' else 'FullRegister'
    otype='(SramController.Out Loader.Machine.Output)' if kind=='core' else '(SramController.Out Chip.Output)'
    lines=['import Endpoints\n'+rb.HEADER]
    def finite(indent,method,operation,ctor,names,bitvec=False):
        term='(fun j => Fin.elim0 j)'
        for name in reversed(names):
            term=f'(Fin.cases (rtl_{operation}_{name} i s) {term})'
        action='step' if operation=='next' else 'observe'
        lines.extend([f'{indent}have h : ∀ j : Fin {len(names)}, rtl{method} i s ({ctor}) =',
                      f'{indent}    reference.{action} i s ({ctor}) := {term}',
                      f'{indent}exact h '+('k.toFin' if bitvec else 'k')])
    def core_cases(indent,prefix):
        def wrap(ctor):
            return ctor if kind=='core' else '.inner (.inner (.inner (.inner ('+ctor+'))))'
        lines.append(indent+'cases r with')
        lines.append(indent+'| parameter b k =>\n'+indent+'  cases b with')
        for b in (0,1):
            bank='true' if b else 'false';lines.append(indent+'  | '+bank+' =>')
            finite(indent+'    ','Step','next',wrap('.parameter '+bank+' (BitVec.ofFin j)'),
                   [f'r_parameter_b{b}_w{k}' for k in range(32)],True)
        for name in ['boot','idle']:
            lines.append(indent+f'| {name} b =>\n'+indent+'  cases b with\n'+indent+f'  | false => exact rtl_next_r_{name}_b0 i s\n'+indent+f'  | true => exact rtl_next_r_{name}_b1 i s')
        for name,ctor in [('active','active'),('valid','valid'),('pending','pending'),('cursor','cursor'),
                          ('current','current'),('cached','cached'),('mode','mode'),('remaining','remaining'),
                          ('wait_left','waitLeft'),('levels','levels'),('enabled','enabled'),('samples','samples'),('payload','payload')]:
            lines.append(indent+f'| {ctor} => exact rtl_next_r_{name} i s')
    def alternatives(indent,names):
        lines.append(indent+'cases r')
        lines.append(indent+'all_goals first | '+' | '.join(f'exact rtl_next_{n} i s' for n in names))
    lines.append(f'theorem model_next (i : Values {itype}) (s : Values {rtype}) (r : {rtype} w) :\n'
                 '    rtlStep i s r = reference.step i s r := by')
    if kind=='core':
        core_cases('  ','')
    else:
        lines.append('  cases r with\n  | extra r =>')
        alternatives('    ',[n for n in rb.REGISTERS if n.startswith('r_result_')])
        lines.append('  | inner r =>\n    cases r with\n    | extra r => nomatch r\n    | inner r =>\n      cases r with\n      | extra r =>\n        cases r with')
        for stage in ['first','second']:
            lines.append(f'        | {stage} r =>')
            alternatives('          ',[n for n in rb.REGISTERS if n.startswith('r_pin_'+stage+'_')])
        lines.append('      | inner r =>\n        cases r with\n        | extra r =>')
        alternatives('          ',[n for n in rb.REGISTERS if n.startswith('r_serial_')])
        lines.append('        | inner r =>')
        core_cases('          ','')
    lines.append(f'theorem model_output (i : Values {itype}) (s : Values {rtype}) (o : {otype} w) :\n'
                 '    rtlObserve i s o = reference.observe i s o := by\n  cases o with\n  | port o =>\n    cases o with\n'
                 '    | address b => exact rtl_output_mem_addr0 i s\n'
                 '    | data => exact rtl_output_mem_data i s\n'
                 '    | write => exact rtl_output_mem_write i s\n'
                 '    | read => exact rtl_output_mem_read i s\n'
                 '  | base o =>\n    cases o with')
    if kind=='chip':
        for name,ctor in [('uo_out','uoOut'),('uio_out','uioOut'),('uio_oe','uioOe')]:
            lines.append(f'    | {ctor} => exact rtl_output_{name} i s')
    else:
        lines.append('    | control o =>\n      cases o with\n      | state r =>\n        cases r')
        lines.append('        all_goals first | '+' | '.join(f'exact rtl_output_loader_{n} i s' for n in ['active','valid','pending','cursor']))
        for n in ['push','commit','start','rejected']:
            lines.append(f'      | {n} => exact rtl_output_loader_{n} i s')
        lines.append('    | core o =>\n      cases o with\n      | state r =>\n        cases r with')
        for n,ctor in [('mode','mode'),('pc','pc'),('remaining','remaining'),('wait_left','waitLeft'),('levels','levels'),('enabled','enabled')]:
            lines.append(f'        | {ctor} => exact rtl_output_{n} i s')
        lines.append('        | sample k =>')
        finite('          ','Observe','output','.base (.core (.state (.sample j)))',[f'sample{k}' for k in range(16)])
        for n,ctor in [('read_a','readA'),('read_b','readB'),('busy','busy')]:
            lines.append(f'      | {ctor} => exact rtl_output_{n} i s')
    lines.append('''theorem component_eq_reference : rtlComponent = reference := by
  apply congr (congrArg Timed.Component.mk ?_) ?_
  · funext i s w r
    exact model_next i s r
  · funext i s w o
    exact model_output i s o
''')
    component='n.component' if kind=='core' else '(PairedComposition.package n).component'
    connection='validation_graph_eq' if kind=='core' else 'congrArg PairedComposition.packaged validation_graph_eq'
    retained='retained_correct' if kind=='core' else 'retained_package_correct'
    lines.append(f'''theorem component_correct
    (n : Netlist Register (SramController.Out Loader.Machine.Output) Input)
    (hn : PairedValidation.core = .ok n) : rtlComponent = {component} :=
  component_eq_reference.trans (({connection}).trans (PairedComposition.{retained} n hn).symm)
''')
    lines.append('#print axioms component_correct\nend Pinwheel.Artifact.Paired\n')
    return '\n'.join(lines)


def session_source(rb):
    return 'import Proof\n' + rb.HEADER + '''open PairedCoverage (Tracked)

/-- The interpreted retained package inherits certified upload and E64 execution.
The external memory law and digital session premises remain explicit. -/
theorem rtl_initialized_session (p : Execution.Image) (image : PairedImage.Image)
    (cert : PairedImage.Corresponds p image)
    (n : Netlist Register (SramController.Out Loader.Machine.Output) Input)
    (hn : PairedValidation.core = .ok n)
    (memory : Memory.SinglePort.Contract S 9 64) (initial : PairedPackage.State S)
    (resetPin idlePin : Chip.Pins) (hr : resetPin.rstN = false)
    (hi : idlePin.rstN = true) (hc : idlePin.uiIn.getLsbD 2 = true)
    (d₀ d₁ : BitVec 64) (uploadPins : List Chip.Pins) (a b : Chip.Pins)
    (hd : Serial.Session (uploadPins.map Chip.wired)
      (Loader.Machine.uploadCommands (PairedImage.upload image) d₀ d₁))
    (pins : List Chip.Pins) :
    let prepared := (PairedPackage.interpreted memory).run initial
      [resetPin, resetPin, resetPin, idlePin, idlePin]
    let uploaded := (PairedPackage.interpreted memory).run prepared (uploadPins ++ [a, b])
    (∀ i ∈ Chip.consumed uploaded.adapters pins, PairedCertified.Rule i.values) →
    ∃ storage : Tracked, PairedTimed.Related p image storage (Engine.Reactive.reset p) ∧
      (PairedPackage.executable rtlComponent memory).trace
        ((PairedPackage.executable rtlComponent memory).run
          ((PairedPackage.executable rtlComponent memory).run initial.physical
            [resetPin, resetPin, resetPin, idlePin, idlePin]) (uploadPins ++ [a, b])) pins =
        (PairedHost.reference p).trace
          ⟨storage, Engine.Reactive.reset p, uploaded.adapters, uploaded.result⟩ pins := by
  rw [component_correct n hn]
  exact PairedSession.retained_initialized_session p image cert n hn memory initial
    resetPin idlePin hr hi hc d₀ d₁ uploadPins a b hd pins

#print axioms rtl_initialized_session
end Pinwheel.Artifact.Paired
'''


def minimize_constraints(rb,pair,solver):
    """Untrusted selection of only the RTL equations needed by a hard root."""
    import subprocess
    import re
    constraints=pair.get('constraints',[])
    if not constraints:
        return pair
    lines=['(set-logic QF_BV)','(set-option :produce-unsat-cores true)',
           '(set-option :smt.core.minimize true)']
    lines += [f'(declare-fun x{j} () (_ BitVec {w}))' for j,(w,_,_) in enumerate(pair['variables'])]
    cache={}
    def emit(t):
        w,op,args,value=t
        if op=='var': return f'x{value}'
        if id(t) in cache: return cache[id(t)]
        a=[emit(x) for x in args]
        if op=='lit': expr=f'(_ bv{value} {w})'
        elif op=='slice': expr=f'((_ extract {value+w-1} {value}) {a[0]})'
        elif op=='concat': expr=f'(concat {a[0]} {a[1]})'
        elif op=='not': expr=f'(bvnot {a[0]})'
        elif op in ('eq','lt'): expr=f'(ite ({"=" if op=="eq" else "bvult"} {a[0]} {a[1]}) #b1 #b0)'
        elif op=='mux': expr=f'(ite (= {a[0]} #b1) {a[1]} {a[2]})'
        else: expr=f'(bv{op} {a[0]} {a[1]})'
        name=f't{len(cache)}';cache[id(t)]=name
        lines.append(f'(define-fun {name} () (_ BitVec {w}) {expr})')
        return name
    for j,(a,b) in enumerate(constraints):
        lhs,rhs=emit(a),emit(b)
        lines.append(f'(assert (! (= {lhs} {rhs}) :named h{j}))')
    lhs,rhs=emit(pair['left']),emit(pair['right'])
    lines+= [f'(assert (not (= {lhs} {rhs})))','(check-sat)','(get-unsat-core)']
    result=subprocess.run([str(solver),'-in','-T:15'],input='\n'.join(lines),text=True,capture_output=True,timeout=20)
    if result.returncode or not result.stdout.startswith('unsat\n'):
        raise ValueError('Constraint selection failed: '+result.stdout)
    selected={int(x) for x in re.findall(r'\bh(\d+)\b',result.stdout)}
    if not selected or any(k>=len(constraints) for k in selected):
        raise ValueError('Invalid constraint selection')
    pair=dict(pair, constraints=[x for k,x in enumerate(constraints) if k in selected])
    print(f'minimized {pair["source"]}: {len(constraints)} -> {len(selected)}',flush=True)
    return pair
