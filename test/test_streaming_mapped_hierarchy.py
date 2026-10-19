"""The proposed hierarchy retains real ripple wires and refuses unknown words."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_mapped_hierarchy import FA, binary, full_adder, hierarchical_source, make_word


def cell(kind, width):
    return dict(type=kind, parameters=dict(A_SIGNED=binary(0), A_WIDTH=binary(width),
        B_SIGNED=binary(0), B_WIDTH=binary(width), Y_WIDTH=binary(width if kind in ('$add', '$sub') else 1)),
        port_directions=dict(A='input', B='input', Y='output'),
        connections=dict(A=list(range(2, 2+width)), B=list(range(2+width, 2+2*width)),
            Y=list(range(2+2*width, 2+3*width if kind in ('$add', '$sub') else 3+2*width))))


def execute(module, values):
    known = {}
    for name, word in values.items():
        for index, bit in enumerate(module['ports'][name]['bits']): known[bit] = bool(word & (1 << index))
    def read(bit): return bit == '1' if type(bit) is str else known[bit]
    pending = list(module['cells'].values())
    while pending:
        ready = []
        for entry in pending:
            ports = entry['connections']
            try: inputs = {name: read(bits[0]) for name, bits in ports.items() if entry['port_directions'][name] == 'input'}
            except KeyError: continue
            kind = entry['type']
            if kind == FA:
                result = execute(full_adder(), {name: int(value) for name, value in inputs.items()})
            elif kind == '$not': result = dict(Y=not inputs['A'])
            elif kind == '$and': result = dict(Y=inputs['A'] and inputs['B'])
            elif kind == '$or': result = dict(Y=inputs['A'] or inputs['B'])
            elif kind == '$xor': result = dict(Y=inputs['A'] != inputs['B'])
            else: raise ValueError('Unknown test graph primitive')
            for name, value in result.items(): known[ports[name][0]] = bool(value)
            ready.append(entry)
        if not ready: raise ValueError('Unresolved generated graph')
        pending = [entry for entry in pending if entry not in ready]
    return {name: sum(int(read(bit)) << n for n, bit in enumerate(port['bits']))
        for name, port in module['ports'].items() if port['direction'] == 'output'}


class HierarchyTests(unittest.TestCase):
    def test_full_adder_all_eight_valuations(self):
        for a in range(2):
            for b in range(2):
                for carry in range(2):
                    result = execute(full_adder(), dict(A=a, B=b, CI=carry))
                    self.assertEqual(result['S'] + 2*result['CO'], a+b+carry)

    def test_actual_generated_ripple_graph_unsigned_add_sub_and_compare(self):
        expected = {'$add': lambda a,b,w:(a+b)%(1<<w), '$sub':lambda a,b,w:(a-b)%(1<<w),
            '$lt':lambda a,b,w:int(a<b), '$le':lambda a,b,w:int(a<=b),
            '$gt':lambda a,b,w:int(a>b), '$ge':lambda a,b,w:int(a>=b)}
        for width in range(1, 5):
            for kind, operation in expected.items():
                module = make_word(cell(kind, width))
                for a in range(1 << width):
                    for b in range(1 << width):
                        with self.subTest(width=width, kind=kind, a=a, b=b):
                            self.assertEqual(execute(module, dict(A=a, B=b))['Y'], operation(a,b,width))

    def test_every_arithmetic_bit_has_real_ordered_full_adder_carry_wires(self):
        module = make_word(cell('$sub', 4))
        carries = module['netnames']['carry']['bits']
        self.assertEqual(carries[0], '1')
        for index in range(4):
            gate = module['cells']['bit_' + str(index)]
            self.assertEqual(gate['type'], FA)
            self.assertEqual((gate['connections']['CI'], gate['connections']['CO']), ([carries[index]], [carries[index+1]]))

    def test_signed_unknown_parameters_and_wrong_interface_refuse(self):
        for mode in ('signed', 'parameter', 'width', 'direction', 'unknown'):
            entry = cell('$add', 4)
            if mode == 'signed': entry['parameters']['A_SIGNED'] = binary(1)
            elif mode == 'parameter': entry['parameters']['SURPRISE'] = binary(1)
            elif mode == 'width': entry['parameters']['A_WIDTH'] = binary(3)
            elif mode == 'direction': entry['port_directions']['Y'] = 'input'
            else: entry['type'] = '$div'
            with self.subTest(mode=mode), self.assertRaises(ValueError): make_word(entry)

    def test_specialization_keeps_original_connectivity_and_never_mutates_source(self):
        entry = cell('$add', 4)
        original = dict(modules=dict(top=dict(ports={},netnames={},cells=dict(addition=entry))))
        before = deepcopy(original)
        result, descriptions = hierarchical_source(original, 'top')
        self.assertEqual(original, before)
        mapped = result['modules']['top']['cells']['addition']
        self.assertEqual(mapped['connections'], entry['connections'])
        self.assertEqual(mapped['port_directions'], entry['port_directions'])
        self.assertEqual(descriptions[mapped['type']]['kind'], '$add')
        self.assertIn(FA, result['modules'])

    def test_external_boundary_is_preserved_only_when_explicitly_allowed(self):
        external = dict(type='FrozenChild',parameters={},port_directions=dict(A='input',Y='output'),
            connections=dict(A=[2,3],Y=[4,5]))
        source = dict(modules=dict(top=dict(ports={},netnames={},cells=dict(child=external))))
        with self.assertRaises(ValueError): hierarchical_source(source,'top')
        mapped,_ = hierarchical_source(source,'top',external_modules=('FrozenChild',))
        child = mapped['modules']['top']['cells']['child']
        self.assertEqual(child['connections'],external['connections'])
        self.assertEqual(child['type'],'FrozenChild')
        self.assertNotIn('FrozenChild',mapped['modules'])

    def test_extra_module_or_memory_cannot_hide_an_uninterpreted_implementation(self):
        for mode in ('module', 'memory'):
            data = dict(modules=dict(top=dict(ports={},netnames={},cells={})))
            if mode == 'module': data['modules']['hidden'] = {}
            else: data['modules']['top']['memories'] = dict(hidden={})
            with self.subTest(mode=mode), self.assertRaises(ValueError): hierarchical_source(data, 'top')


if __name__ == '__main__': unittest.main()
