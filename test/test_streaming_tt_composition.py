"""Independent refusal and contract-shape controls; native replay is separate."""
from copy import deepcopy
from pathlib import Path
import re
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_tt_composition import generate_clock_inventory, generate_required


def fixture():
    names = tuple('clock' + str(index) for index in range(803))
    nodes = tuple(dict(name=name, cell='buffer' if index < 577 else 'inverter',
        sources=(0,), expression=('variable', 'p0') if index < 577 else
        ('not', ('variable', 'p0'))) for index, name in enumerate(names))
    clocks = (('wire', 1, False),) * 6039
    resets = (('constant', True),) * 6039
    actual = dict(labels=(('input', 'clk', 0),), nodes=nodes, next={},
        outputs={'clock': clocks, 'reset': resets})
    metadata = dict(namespace='SyntheticClock', module='SyntheticClockProof',
        actual_cone_cells=names, actual_clock_cells=names,
        ff_order=tuple('ff' + str(index) for index in range(6039)),
        clock_roots=clocks, reset_roots=resets)
    return metadata, actual


def table_rows(source, table):
    rows = {}
    pattern = r'^def ' + table + r'_(\d+)_(\d+)\s.*? :=\n  match index - (\d+) with\n(.*?)(?=^def |\Z)'
    for match in re.finditer(pattern, source, re.M | re.S):
        start = int(match[3])
        for offset, value in re.findall(r'^\s+\| (\d+) => ([^\n]+)', match[4], re.M):
            key = start + int(offset)
            if key in rows:
                raise AssertionError('Duplicate generated table row')
            rows[key] = value
    return rows


def check_contracts(source):
    expected = {
        'Final.decoded_actual_step': ('ActualState.device.step input bits', 'enginePins input'),
        'Final.actual_step_encoded': ('ActualState.device.step input bits', 'packing.encode (stateValues'),
        'Final.decoded_actual_observe': ('pad : StreamingReady.TinyWiring.Pad', 'Description.pads'),
        'Final.decoded_actual_run': ('incoming : List (Fin 18 → Bool)', 'incoming.map enginePins'),
        'Final.decoded_physical_update': ('before after : Bool', 'Rising before after', 'else decodedState bits'),
        'encoded_decoded': ('packing.encode (stateValues (decodedState bits)) = bits',),
        'decoded_encode': ('state : StreamingReady.Package.State 1', '= state'),
        'ActualClockDAG.actual_positive': ('index : Fin 6039', 'clockRoot index', '= raw'),
        'ActualClockDAG.actual_inactive': ('index : Fin 6039', 'resetRoot index', '= true'),
        'ActualClockDAG.Inventory.all_actual_cts_levels':
            ('index : Fin 803', 'ctsRoot index', 'ctsInverted index then !raw else raw'),
    }
    blocks = re.findall(r'^example .*?(?=^example |^#check |\Z)', source, re.M | re.S)
    if len(blocks) != len(expected):
        raise AssertionError('Missing required contract')
    remaining = dict(expected)
    for block in blocks:
        fact = next((name for name in remaining if re.search(r':=\s*' + re.escape(name) + r'\b', block)), None)
        if fact is None:
            raise AssertionError('Missing or duplicated required fact')
        if not all(fragment in block for fragment in remaining.pop(fact)):
            raise AssertionError('Changed independent contract type')
        if 'bits :' in block and '(bits : Fin 6039 → Bool)' not in block:
            raise AssertionError('Changed arbitrary physical state domain')
    if remaining:
        raise AssertionError('Missing required fact')


class CompositionContracts(unittest.TestCase):
    def inventory(self, metadata, actual):
        return generate_clock_inventory(metadata, actual)['ActualGRTClockInventory']

    def test_all803_signed_outputs_match_independent_boolean_execution_and_mapping(self):
        metadata, actual = fixture()
        metadata['actual_clock_cells'] = tuple(reversed(metadata['actual_clock_cells']))
        source = self.inventory(metadata, actual)
        roots, signs = table_rows(source, 'ctsRootTable'), table_rows(source, 'ctsInvertedTable')
        self.assertEqual(set(roots), set(range(803)))
        self.assertEqual(set(signs), set(range(803)))
        self.assertEqual(sum(value == 'true' for value in signs.values()), 226)
        for raw in (False, True):
            # This tiny interpreter knows only the fixture's two physical gates;
            # it does not use canonical_model/projection or generated table code.
            values = [raw]
            for node in actual['nodes']:
                value = values[node['sources'][0]]
                values.append(not value if node['expression'][0] == 'not' else value)
            for index, name in enumerate(metadata['actual_clock_cells']):
                match = re.fullmatch(r'\.wire (\d+) false', roots[index])
                self.assertIsNotNone(match)
                wire = int(match[1])
                self.assertEqual(actual['nodes'][wire - 1]['name'], name)
                self.assertEqual(values[wire], not raw if signs[index] == 'true' else raw)

    def test_unused_branch_sign_mutation_and_paired_inversion_are_retained(self):
        metadata, actual = fixture()
        original = table_rows(self.inventory(metadata, actual), 'ctsInvertedTable')
        changed = deepcopy(actual)
        changed['nodes'][600]['expression'] = ('variable', 'p0')
        buffer_signs = table_rows(self.inventory(metadata, changed), 'ctsInvertedTable')
        self.assertEqual(original[600], 'true')
        self.assertEqual(buffer_signs[600], 'false')
        changed = deepcopy(actual)
        changed['nodes'][600]['sources'] = (578,)
        paired_signs = table_rows(self.inventory(metadata, changed), 'ctsInvertedTable')
        self.assertEqual(paired_signs[600], 'false')
        self.assertEqual(len(paired_signs), 803)

    def test_omitted_duplicate_unknown_and_misordered_actual_inventory_refuse(self):
        metadata, actual = fixture()
        for mode in ('omit', 'duplicate', 'unknown', 'mapping', 'aliased-actual'):
            changed = deepcopy(metadata)
            changed_actual = deepcopy(actual)
            if mode == 'omit':
                changed['actual_clock_cells'] = changed['actual_clock_cells'][:-1]
            elif mode == 'duplicate':
                changed['actual_clock_cells'] = (*changed['actual_clock_cells'][:-1], 'clock0')
            elif mode == 'unknown':
                changed['actual_clock_cells'] = (*changed['actual_clock_cells'][:-1], 'absent')
            elif mode == 'mapping':
                changed['actual_cone_cells'] = tuple(reversed(changed['actual_cone_cells']))
            else:
                changed_actual['nodes'][-1]['name'] = 'clock0'
                changed['actual_cone_cells'] = tuple(node['name'] for node in changed_actual['nodes'])
                changed['actual_clock_cells'] = changed['actual_clock_cells'][:-1]
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                self.inventory(changed, changed_actual)

    def test_every6039_ff_root_and_its_polarity_are_required(self):
        metadata, actual = fixture()
        for mode in ('ff-omission', 'clock-omission', 'reset-omission', 'negative-clock', 'active-reset'):
            changed_meta, changed_actual = deepcopy(metadata), deepcopy(actual)
            if mode == 'ff-omission':
                changed_meta['ff_order'] = changed_meta['ff_order'][:-1]
            else:
                field = 'reset' if 'reset' in mode else 'clock'
                roots = changed_actual['outputs'][field]
                replacement = ('constant', False) if field == 'reset' else ('wire', 578, False)
                changed_actual['outputs'][field] = roots[:-1] if 'omission' in mode else (*roots[:-1], replacement)
                changed_meta[field + '_roots'] = changed_actual['outputs'][field]
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                self.inventory(changed_meta, changed_actual)

    def test_ten_independent_types_detect_contract_omission_and_domain_mutations(self):
        with self.assertRaises(TypeError):
            generate_required()
        source = generate_required(cts_count=803)['PhysicalGRTFinalRequired']
        check_contracts(source)
        first = re.search(r'^example .*?(?=^example )', source, re.M | re.S)[0]
        mutations = [source.replace(first, '', 1),
            source.replace('(bits : Fin 6039 → Bool)', '(bits : Fin 6038 → Bool)', 1),
            source.replace('(index : Fin 803)', '(index : Fin 802)', 1),
            source.replace('else decodedState bits', 'else decodedState (fun _ => false)', 1)]
        for index, changed in enumerate(mutations):
            with self.subTest(index=index), self.assertRaises(AssertionError):
                check_contracts(changed)
        for count in (0, -1, True, None):
            with self.subTest(count=count), self.assertRaises(ValueError):
                generate_required(cts_count=count)


if __name__ == '__main__':
    unittest.main()
