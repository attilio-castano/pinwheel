"""Cheap rejection controls for physical target contracts and semantic roles."""
from copy import deepcopy
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import physical_target as target
from tiled_chip import FF
from physical_checkpoint_sta import analysis_tcl
from mapped_physical import validate_start, signal_view


def fixture():
    spec = dict(schema=1, name='fixture', source=dict(kind='paired-controller', selection='selected.json', sha256='missing'),
        macro=dict(master='RM_IHPSG13_1P_512x64_c2_bm_bist',
                   instances={'memory.storage': dict(location=[10, 20], orientation='N')}, power=deepcopy(target.POWER)),
        placement_exclusions=[[10, 15, 30, 20]], entry_state=['r_entry'], upload_state=['r_upload'])
    module = dict(ports={'uo_out': dict(bits=[10]*8)}, netnames={}, cells={})
    for name, bit in [('entry', 10), ('upload', 11)]:
        module['netnames']['controller.r_' + name] = dict(bits=[bit])
        module['cells'][name] = dict(type=FF, connections=dict(Q=[bit], D=[3], CLK=[2], RESET_B=['1']))
    module['cells']['memory.storage'] = dict(type=spec['macro']['master'],
        connections=dict(A_DOUT=[20, 21], A_ADDR=[10, 11], A_DIN=[11, 11]))
    description = dict(registers=[dict(name='r_'+n, width=1) for n in ['entry', 'upload']])
    return spec, module, description


class TargetContracts(unittest.TestCase):
    def test_all_state_owned_and_four_path_roles_resolve(self):
        spec, module, description = fixture()
        saved = deepcopy((spec, module, description))
        owners, paths = target.state_and_paths(module, description, spec)
        self.assertEqual(owners['physical_flip_flops'], 2)
        self.assertEqual(paths['entry_state']['sinks'], ['entry/D'])
        self.assertEqual(paths['upload_hold']['sources'], ['upload/Q'])
        self.assertEqual(paths['rejection_status']['sinks'], ['uo_out[4]'])
        self.assertEqual(paths['sram_address']['sources'], ['memory.storage/A_DOUT[0]', 'memory.storage/A_DOUT[1]'])
        self.assertEqual((spec, module, description), saved)

    def test_missing_or_duplicate_state_cannot_pass_as_complete_ownership(self):
        for mode in ['missing', 'alias', 'extra_ff', 'wrong_width']:
            spec, module, desc = fixture()
            if mode == 'missing':
                del module['netnames']['controller.r_entry']
            elif mode == 'alias':
                module['netnames']['controller.r_entry']['bits'] = [11]
            elif mode == 'extra_ff':
                module['cells']['extra'] = deepcopy(module['cells']['entry'])
                module['cells']['extra']['connections']['Q'] = [99]
            else:
                desc['registers'][0]['width'] = 2
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                target.state_and_paths(module, desc, spec)

    def test_unresolved_semantic_role_fails(self):
        spec, module, desc = fixture()
        spec['entry_state'] = ['r_typo']
        with self.assertRaisesRegex(ValueError, 'Unresolved'):
            target.state_and_paths(module, desc, spec)

    def test_reachability_distinguishes_absence_and_stops_at_state(self):
        spec, module, desc = fixture()
        _, roles = target.state_and_paths(module, desc, spec)
        module['cells']['logic'] = dict(type='sg13cmos5l_buf_1', connections=dict(A=[20], X=[3]),
                                       port_directions=dict(A='input', X='output'))
        reach = target.path_expectations(module, roles)
        self.assertEqual(reach, dict(sram_address=False, entry_state=True, rejection_status=False, upload_hold=True))
        module['ports']['uo_out']['bits'][4] = 3
        self.assertTrue(target.path_expectations(module, roles)['rejection_status'])
        with self.assertRaisesRegex(ValueError, 'reachability'):
            analysis_tcl(dict(path_roles=roles, path_expected={'entry_state': False}))

    def test_older_run_role_bundle_requires_exact_mapping_and_constraints(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder); design, bundle = root/'old', root/'target'
            design.mkdir(); bundle.mkdir()
            for p in [design, bundle]:
                (p/'core.sdc').write_text('clock')
                (p/'tt_block_6x4_pgvdd.def').write_text('package')
            physical = dict(mapped_input=dict(artifacts_sha256={'netlist': 'saved'}, libraries_sha256={'typical': 'lib'}))
            prepared = dict(physical, physical_target={'name': 'fixture'}, files_sha256={'core.sdc': target.sha(bundle/'core.sdc')})
            (design/'inputs.json').write_text(json.dumps(physical))
            (bundle/'inputs.json').write_text(json.dumps(prepared))
            self.assertEqual(target.matching_bundle(design, bundle), bundle)
            (design/'core.sdc').write_text('different clock')
            with self.assertRaisesRegex(ValueError, 'boundary'):
                target.matching_bundle(design, bundle)
            (design/'core.sdc').write_text('clock')
            physical['mapped_input']['artifacts_sha256']['netlist'] = 'different'
            (design/'inputs.json').write_text(json.dumps(physical))
            with self.assertRaisesRegex(ValueError, 'another mapped'):
                target.matching_bundle(design, bundle)
            (bundle/'core.sdc').write_text('modified')
            with self.assertRaisesRegex(ValueError, 'Changed target'):
                target.matching_bundle(design, bundle)

    def test_timing_roles_require_exact_endpoints_and_valid_constraints(self):
        spec, module, desc = fixture()
        _, roles = target.state_and_paths(module, desc, spec)
        script = analysis_tcl(dict(path_roles=roles))
        self.assertIn('get_full_name', script)
        self.assertIn('PINWHEEL_PATH upload_hold', script)
        for mode in ['name', 'empty', 'duplicate', 'injection', 'delay']:
            bad = deepcopy(roles)
            if mode == 'name': bad['unsafe;exit'] = bad.pop('entry_state')
            elif mode == 'empty': bad['entry_state']['sources'] = []
            elif mode == 'duplicate': bad['entry_state']['sources'] *= 2
            elif mode == 'injection': bad['entry_state']['sources'] = ['bad}; exit; {']
            else: bad['entry_state']['delay'] = 'unconstrained'
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                analysis_tcl(dict(path_roles=bad))

    def test_placement_resume_requires_the_verified_macro_checkpoint(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            inputs = dict(mapped_input={}, physical_target={'name': 'fixture'})
            (root/'inputs.json').write_text(json.dumps(inputs))
            state = root/'state.json'; state.write_text('{}')
            with self.assertRaises(ValueError):
                validate_start(inputs, state, 'Odb.RemovePDNObstructions', root)
            (root/'macro-verified.json').write_text(json.dumps(dict(status='passed',
                continuation_step='Odb.RemovePDNObstructions',
                inputs_sha256=target.sha(root/'inputs.json'), state_sha256=target.sha(state))))
            validate_start(inputs, state, 'Odb.RemovePDNObstructions', root)
            state.write_text('{"changed":true}')
            with self.assertRaises(ValueError):
                validate_start(inputs, state, 'Odb.RemovePDNObstructions', root)

    def test_only_isolated_declared_power_ports_can_be_projected(self):
        module = dict(ports={'data': dict(direction='input', bits=[2]),
                            'VPWR': dict(direction='inout', bits=[3]),
                            'VGND': dict(direction='inout', bits=[4])}, cells={})
        saved = deepcopy(module)
        projected, names = signal_view(module, target.POWER)
        self.assertEqual(names, ['VGND', 'VPWR'])
        self.assertEqual(set(projected['ports']), {'data'})
        self.assertEqual(module, saved)
        for mode in ['missing', 'direction', 'short', 'logic', 'package', 'wide']:
            bad = deepcopy(module)
            if mode == 'missing': del bad['ports']['VPWR']
            elif mode == 'direction': bad['ports']['VPWR']['direction'] = 'input'
            elif mode == 'short': bad['ports']['VPWR']['bits'] = [4]
            elif mode == 'logic': bad['cells']['buffer'] = dict(connections=dict(A=[3]))
            elif mode == 'package': bad['ports']['data']['bits'] = [3]
            else: bad['ports']['VPWR']['bits'] = [3, 5]
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                signal_view(bad, target.POWER)

    def test_configuration_changes_only_target_owned_fields(self):
        spec, _, _ = fixture()
        base = dict(DIE_AREA=[0, 0, 100, 100], CLOCK_PERIOD=20, MAX_FANOUT_CONSTRAINT=10,
                    MACROS={'obsolete': {}}, PDN_MACRO_CONNECTIONS=['obsolete'],
                    VERILOG_FILES=['old'], VERILOG_DEFINES=['old'], FP_OBSTRUCTIONS=[[0, 0, 1, 1]])
        saved = deepcopy(base)
        result = target.configuration(base, spec)
        self.assertEqual(base, saved)
        changed = {k for k in base if base[k] != result[k]}
        self.assertEqual(changed, {'MACROS', 'PDN_MACRO_CONNECTIONS', 'VERILOG_FILES', 'VERILOG_DEFINES', 'FP_OBSTRUCTIONS'})
        self.assertEqual(result['VERILOG_FILES'], ['dir::design.sv'])
        for connection in result['PDN_MACRO_CONNECTIONS']:
            pattern = connection.split()[0]
            self.assertIsNotNone(re.fullmatch(pattern, 'memory.storage'))
            self.assertIsNone(re.fullmatch(pattern, 'memoryXstorage'))

    def test_declaration_rejects_missing_power_unknown_fields_and_roles(self):
        with tempfile.TemporaryDirectory() as folder:
            file = Path(folder) / 'target.json'
            for mode in ['power', 'extra', 'empty_role', 'duplicate_role', 'macro']:
                spec, _, _ = fixture()
                if mode == 'power': spec['macro']['power']['VPWR'].pop()
                elif mode == 'extra': spec['skip_checks'] = True
                elif mode == 'empty_role': spec['upload_state'] = []
                elif mode == 'duplicate_role': spec['entry_state'] *= 2
                else: spec['macro']['master'] = 'unknown'
                file.write_text(json.dumps(spec))
                with self.subTest(mode=mode), self.assertRaises(ValueError):
                    target.declaration(file)

    def test_stale_selection_stops_before_artifact_intake(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder); spec, _, _ = fixture()
            (root/'selected.json').write_text('{}')
            (root/'target.json').write_text(json.dumps(spec))
            with self.assertRaisesRegex(ValueError, 'Changed physical target selection'):
                target.resolve(root/'target.json', root)

    def test_wrong_lef_signal_terminal_is_rejected(self):
        _, module, _ = fixture()
        cell = module['cells']['memory.storage']
        cell['port_directions'] = dict(A_DOUT='output', A_ADDR='input', A_DIN='input')
        pins = {f'{p}[{i}]': dict(use='SIGNAL', direction=d.upper())
                for p, d in cell['port_directions'].items() for i in range(2)}
        geometry = dict(master=cell['type'], pins=pins)
        target.validate_terminals(module, geometry)
        del pins['A_ADDR[1]']
        with self.assertRaisesRegex(ValueError, 'LEF signal terminals'):
            target.validate_terminals(module, geometry)

    def test_footprint_power_and_corridor_are_checked_before_staging(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder); spec, _, _ = fixture()
            master = spec['macro']['master']
            text = f'MACRO {master}\n  SIZE 20 BY 10 ;\n'
            for name, use in [('VDD!', 'POWER'), ('VDDARRAY!', 'POWER'), ('VSS!', 'GROUND')]:
                text += f'  PIN {name}\n    DIRECTION INOUT ;\n    USE {use} ;\n  END {name}\n'
            text += f'END {master}\n'
            (folder/(master+'.lef')).write_text(text)
            provenance = dict(macro_views_sha256={})
            base = dict(DIE_AREA=[0, 0, 100, 100])
            self.assertEqual(target.validate_views(spec, folder, provenance, base)['macro_bboxes_um'],
                             {'memory.storage': [10, 20, 30, 30]})
            for mode in ['outside', 'overlap', 'corridor', 'power', 'master']:
                changed = deepcopy(spec)
                if mode == 'outside': changed['macro']['instances']['memory.storage']['location'] = [95, 20]
                elif mode == 'overlap': changed['macro']['instances']['other'] = dict(location=[11, 21], orientation='N')
                elif mode == 'corridor': changed['placement_exclusions'] = [[10, 20, 30, 25]]
                elif mode == 'power': (folder/(master+'.lef')).write_text(text.replace('USE POWER', 'USE SIGNAL', 1))
                else: (folder/(master+'.lef')).write_text(text.replace('MACRO '+master, 'MACRO wrong'))
                with self.subTest(mode=mode), self.assertRaises(ValueError):
                    target.validate_views(changed, folder, provenance, base)
                (folder/(master+'.lef')).write_text(text)


if __name__ == '__main__':
    unittest.main()
