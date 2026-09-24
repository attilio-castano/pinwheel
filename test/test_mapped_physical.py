"""A physical import may materialize constants but cannot alter mapped wiring."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from mapped_physical import compare_connections, selected_mapping, validate_start
from validation_run import sha


def cell(kind, pins, outputs):
    return dict(type=kind, connections=deepcopy(pins),
                port_directions={p: 'output' if p in outputs else 'input' for p in pins})


def fixture():
    return dict(ports={'clk': dict(direction='input', bits=[2]),
                       'data': dict(direction='input', bits=[3, 4]),
                       'out': dict(direction='output', bits=[7])},
                cells={'reg': cell('dff', {'C': [2], 'D': [3], 'Q': [5], 'RN': ['1']}, {'Q'}),
                       'buffer': cell('buf', {'A': [5], 'Y': [7]}, {'Y'}),
                       'memory': cell('sram', {'CLK': [2], 'ADDR': [5, 4], 'BIST': ['0'], 'Q': [8]}, {'Q'})})


class MappedPhysical(unittest.TestCase):
    def test_wire_renaming_and_tie_insertion_preserve_all_connections(self):
        reference = fixture()
        imported = deepcopy(reference)
        for port in imported['ports'].values():
            port['bits'] = [b + 20 for b in port['bits']]
        for c in imported['cells'].values():
            for pin, bits in c['connections'].items():
                c['connections'][pin] = [b + 20 if type(b) is int else {'1': 60, '0': 61}[b] for b in bits]
        imported['cells']['high'] = cell('sg13cmos5l_tiehi', {'L_HI': [60]}, {'L_HI'})
        imported['cells']['low'] = cell('sg13cmos5l_tielo', {'L_LO': [61]}, {'L_LO'})
        result = compare_connections(reference, imported)
        self.assertEqual(result['retained_cells'], 3)
        self.assertEqual(sum(result['added_tie_cells'].values()), 2)

    def test_same_cell_count_does_not_hide_clock_address_or_logic_changes(self):
        for mutate in (lambda m: m['cells']['reg']['connections']['C'].__setitem__(0, 3),
                       lambda m: m['cells']['memory']['connections']['ADDR'].reverse(),
                       lambda m: m['cells']['reg']['connections']['RN'].__setitem__(0, '0'),
                       lambda m: m['cells']['buffer'].__setitem__('type', 'inv'),
                       lambda m: m['ports']['data']['bits'].reverse(),
                       lambda m: m['cells']['buffer']['connections']['A'].__setitem__(0, 4)):
            reference = fixture()
            imported = deepcopy(reference)
            mutate(imported)
            with self.subTest(mutation=mutate), self.assertRaises(ValueError):
                compare_connections(reference, imported)

    def test_extra_cell_unknown_and_tie_driver_conflicts_are_rejected(self):
        for mutate in (lambda m: m['cells'].__setitem__('extra', cell('buf', {'A': [5], 'Y': [9]}, {'Y'})),
                       lambda m: m['cells']['reg']['connections']['D'].__setitem__(0, 'x'),
                       lambda m: m['cells'].__setitem__('tie', cell('sg13cmos5l_tiehi', {'L_HI': [5]}, {'L_HI'})),
                       lambda m: m['cells'].__setitem__('tie', cell('sg13cmos5l_tiehi', {'L_HI': [2]}, {'L_HI'}))):
            reference = fixture()
            imported = deepcopy(reference)
            mutate(imported)
            with self.subTest(mutation=mutate), self.assertRaises(ValueError):
                compare_connections(reference, imported)

    def test_mapped_start_cannot_fall_back_to_synthesis_or_unchecked_continuation(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            inputs = {'mapped_input': {}}
            (root / 'inputs.json').write_text(json.dumps(inputs))
            state = root / 'state.json'
            state.write_text(json.dumps(dict(nl='/work/core/design.sv', json_h='/work/core/mapped.json', metrics={})))
            validate_start(inputs, state, 'OpenROAD.CheckSDCFiles', root)
            for stage in (None, 'Yosys.Synthesis', 'OpenROAD.DumpRCValues'):
                with self.subTest(stage=stage), self.assertRaises(ValueError):
                    validate_start(inputs, state, stage, root)
            (root / 'import-verified.json').write_text(json.dumps(dict(status='passed',
                inputs_sha256=sha(root / 'inputs.json'), state_sha256=sha(state))))
            validate_start(inputs, state, 'OpenROAD.DumpRCValues', root)
            state.write_text('{}')
            with self.assertRaises(ValueError):
                validate_start(inputs, state, 'OpenROAD.DumpRCValues', root)

    def test_changed_selected_report_rejected_before_any_cad_or_staging(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root / 'report.json').write_text('{}')
            (root / 'validation.json').write_text('{}')
            selection = root / 'selected.json'
            selection.write_text(json.dumps(dict(decision='eligible-for-bounded-physical-comparison',
                report='report.json', report_sha256='stale',
                validation=dict(report='validation.json', report_sha256=sha(root / 'validation.json')))))
            with self.assertRaisesRegex(ValueError, 'Changed selected'):
                selected_mapping(selection, 'tiled', root)


if __name__ == '__main__':
    unittest.main()
