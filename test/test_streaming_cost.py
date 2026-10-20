"""Saved-netlist cost arithmetic and incomplete/ambiguous artifact refusals."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_cost import (CONSTRAINTS, LIBRARY_SHA256, NATIVE_SCOPE,
    check_abc_timing, check_comparison, check_native_mapping, digital_memory_inventory,
    inventory, map_target, metrics, native_mapping_artifacts, parse_abc_timing, quoted, sha)


TIMING_LOG = '''ABC: Setting driving cell to be "sg13cmos5l_buf_2".
ABC: Setting output load to be 10.000000.
ABC: + stime -p
ABC: WireLoad = "none"  Gates =  1 ( 1.0 %)   Cap =  8.1 ff ( 4.7 %)   Area = 2.50 ( 87.5 %)   Delay = 200.05 ps ( 1.7 %)
ABC: Path 0 -- 1 : 0 1 pi A = 0.00 Df = 3.5 -0.5 ps S = 16.9 ps Cin = 0.0 ff Cout = 2.3 ff Cmax = 0.0 ff G = 0
ABC: Path 1 -- 2 : 2 1 sg13cmos5l_nor2_1 A = 7.26 Df = 200.0 -33.6 ps S = 106.1 ps Cin = 3.0 ff Cout = 10.0 ff Cmax = 300.0 ff G = 335
ABC: Start-point = pi0 (\\r_state [0]).  End-point = po3 ($auto$output).
'''


def timing_artifacts(timing):
    return {name: hashlib.sha256(timing[field].encode()).hexdigest() for field, name in (
        ('context_text', 'abc-timing-context.txt'), ('summary_text', 'abc-timing-summary.txt'),
        ('path_text', 'abc-critical-path.txt'))}


def native_fixture():
    paths = dict(script='abc/abc.script', liberty_scl='cache/cells.scl',
        input_blif='abc/input.blif', output_blif='abc/output.blif')
    hashes = {path: str(index + 1) * 64 for index, path in enumerate(paths.values())}
    return dict(scope=NATIVE_SCOPE, isolated_tmpdir=True, global_cache_consumed=False,
        python_preuse_frozen=False, references={role: dict(path=path, sha256=hashes[path])
            for role, path in paths.items()}, artifact_sha256=hashes)


def create_native(temporary):
    temporary = Path(temporary)
    paths = {role: temporary / path for role, path in (
        ('script', 'abc/abc.script'), ('liberty_scl', 'cache/cells.scl'),
        ('input_blif', 'abc/input.blif'), ('output_blif', 'abc/output.blif'))}
    for role, path in paths.items():
        path.parent.mkdir(exist_ok=True, parents=True)
        path.write_text('synthetic ' + role + '\n')
    return ('Running ABC script: abc/abc.script\nABC: + read_blif abc/input.blif\n'
        'ABC: + read_scl ' + str(paths['liberty_scl']) + '\n' + TIMING_LOG +
        'ABC: + write_blif abc/output.blif\n')


def fixture():
    def cell(kind, connections, directions):
        return dict(type=kind, connections=connections, port_directions=directions)
    module = dict(ports=dict(x=dict(direction='input', bits=[1]),
        clk=dict(direction='input', bits=[2]), out=dict(direction='output', bits=[5])),
        netnames=dict(r_q=dict(bits=[3])), cells={
            'ff': cell('sg13cmos5l_df_test', dict(D=[5], Q=[3], CLK=[2]), dict(D='input', Q='output', CLK='input')),
            'a': cell('sg13cmos5l_comb_test', dict(A=[1], B=[3], X=[4]), dict(A='input', B='input', X='output')),
            'b': cell('sg13cmos5l_comb_test', dict(A=[4], B=['0'], X=[5]), dict(A='input', B='input', X='output'))})
    data = dict(modules=dict(top=module, sg13cmos5l_df_test=dict(attributes=dict(area='10.0')),
        sg13cmos5l_comb_test=dict(attributes=dict(area='2.5'))))
    registers = [dict(name='r_q', width=1, origin='typed', group='state')]
    return data, registers


class CostTests(unittest.TestCase):
    def test_native_abc_estimate_preserves_delay_path_and_constraints(self):
        timing = parse_abc_timing(TIMING_LOG)
        self.assertEqual(timing['delay_ps'], 200.05)
        self.assertEqual(timing['path_cells'], 1)
        self.assertEqual(timing['start_signal'], '\\r_state [0]')
        self.assertEqual(timing['path'][-1]['arrival_ps'], 200.0)
        self.assertIn('No clock-to-Q', timing['boundary'])
        self.assertIn('no', timing['wire_load'])
        check_abc_timing(timing, timing_artifacts(timing))

    def test_abc_summary_absence_duplicates_bad_units_and_nonfinite_delay_refuse(self):
        summary = next(line for line in TIMING_LOG.splitlines() if 'WireLoad' in line)
        for changed in (TIMING_LOG.replace(summary, ''), TIMING_LOG + summary + '\n',
                TIMING_LOG.replace('200.05 ps', '200.05 ns'),
                TIMING_LOG.replace('200.05 ps', '0.0 ps'),
                TIMING_LOG.replace('200.05 ps', '-1.0 ps'),
                TIMING_LOG.replace('200.05 ps', 'nan ps'),
                TIMING_LOG.replace('200.05 ps', '1e309 ps'),
                TIMING_LOG.replace('"none"', '"wireload_10"')):
            with self.subTest(changed=changed), self.assertRaises(ValueError): parse_abc_timing(changed)

    def test_abc_requires_actual_contiguous_path_and_matching_endpoint_delay(self):
        path = next(line for line in TIMING_LOG.splitlines() if 'Path 1 ' in line)
        endpoint = next(line for line in TIMING_LOG.splitlines() if 'Start-point' in line)
        for changed in (TIMING_LOG.replace(path, ''), TIMING_LOG.replace(endpoint, ''),
                TIMING_LOG + endpoint + '\n', TIMING_LOG.replace('Path 1 --', 'Path 2 --'),
                TIMING_LOG.replace('Df = 200.0', 'Df = 100.0'),
                TIMING_LOG.replace(path, 'ABC: unrelated output\n' + path),
                TIMING_LOG.replace('sg13cmos5l_nor2_1', 'sg13cmos5l_df_fake'),
                TIMING_LOG.replace('Cin = 3.0 ff', 'Cin = 3.0 pf')):
            with self.subTest(changed=changed), self.assertRaises(ValueError): parse_abc_timing(changed)

    def test_abc_context_and_text_hashes_cannot_be_silently_relabelled(self):
        for changed in (TIMING_LOG.replace('buf_2', 'buf_1'),
                TIMING_LOG.replace('10.000000.', '20.000000.'),
                TIMING_LOG.replace('ABC: + stime -p\n', ''),
                TIMING_LOG.replace('stime -p', 'stime -a')):
            with self.subTest(changed=changed), self.assertRaises(ValueError): parse_abc_timing(changed)
        with self.assertRaises(ValueError): parse_abc_timing(TIMING_LOG, constraints='set_load 2\n')
        timing = parse_abc_timing(TIMING_LOG)
        artifacts = timing_artifacts(timing)
        changed = deepcopy(timing)
        changed['delay_ps'] = 100.0
        with self.assertRaises(ValueError): check_abc_timing(changed, artifacts)
        artifacts['abc-critical-path.txt'] = '0' * 64
        with self.assertRaises(ValueError): check_abc_timing(timing, artifacts)

    def test_map_target_consumes_native_returned_log_and_saves_timing_artifacts(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder, calls = Path(temporary).resolve(), []
            library = folder / 'test.lib'
            library.write_text('synthetic test library; no physical qualification')
            out = folder / 'result'
            data, registers = fixture()
            def run(argv, label, **options):
                calls.append((argv, label, options))
                self.assertEqual(argv[:4], ['env', '-C', out / 'native-tmp', 'TMPDIR=' + str(out / 'native-tmp')])
                for name in ('generic.json', 'mapped.json'):
                    (out / name).write_text(json.dumps(data))
                (out / 'mapped.v').write_text('// synthetic saved netlist\n')
                return create_native(out / 'native-tmp')
            def pinned(path): return LIBRARY_SHA256 if Path(path) == library else sha(path)
            with patch('streaming_cost.sha', side_effect=pinned):
                result = map_target(run, out, label='fixture', top='top', sources=[], registers=registers,
                    library=library, yosys='unused', abc='unused')
            self.assertEqual(len(calls), 1)
            self.assertEqual(result['abc_liberty_estimate']['delay_ps'], 200.05)
            for name, expected in timing_artifacts(result['abc_liberty_estimate']).items():
                self.assertEqual(sha(out / name), expected)
                self.assertEqual(result['artifact_sha256'][name], expected)
            check_native_mapping(result['native_mapping'], result['artifact_sha256'])
            for reference in result['native_mapping']['references'].values():
                self.assertEqual(sha(out / 'native-tmp' / reference['path']), reference['sha256'])

    def test_native_mapping_retains_generated_script_scl_and_both_blif_files(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            log = create_native(root)
            native = native_mapping_artifacts(log, root)
            self.assertEqual(len(native['artifact_sha256']), 4)
            self.assertFalse(native['python_preuse_frozen'])
            artifacts = {'native-tmp/' + path: value for path, value in native['artifact_sha256'].items()}
            check_native_mapping(native, artifacts)
            for mutation in ('outside', 'duplicate', 'absent', 'redirected'):
                candidate = log
                if mutation == 'outside': candidate = log.replace(str(root / 'cache/cells.scl'), str(root.parent / 'outside.scl'))
                elif mutation == 'duplicate': candidate += 'ABC: + read_blif abc/input.blif\n'
                elif mutation == 'absent': candidate = candidate.replace('ABC: + write_blif abc/output.blif\n', '')
                else:
                    (root / 'abc/input.blif').unlink()
                    (root / 'abc/input.blif').symlink_to(root / 'abc/output.blif')
                with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                    native_mapping_artifacts(candidate, root)

    def test_native_mapping_refuses_claim_upgrade_omitted_inputs_or_wrong_hash(self):
        native = native_fixture()
        artifacts = {'native-tmp/' + path: value for path, value in native['artifact_sha256'].items()}
        check_native_mapping(native, artifacts)
        for mutation in ('cache', 'preuse', 'omitted', 'hash', 'escape'):
            value = deepcopy(native)
            if mutation == 'cache': value['global_cache_consumed'] = True
            elif mutation == 'preuse': value['python_preuse_frozen'] = True
            elif mutation == 'omitted': value['references'].pop('liberty_scl')
            elif mutation == 'hash': value['references']['script']['sha256'] = '0' * 64
            else: value['artifact_sha256']['../outside.scl'] = '1' * 64
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                check_native_mapping(value, artifacts)

    def test_all_cells_state_and_two_gate_path_counted(self):
        data, registers = fixture()
        result = metrics(data, 'top', registers)
        self.assertEqual(result['standard_cell_area_um2'], 15.0)
        self.assertEqual(result['sequential_area_um2'], 10.0)
        self.assertEqual(result['combinational_area_um2'], 5.0)
        self.assertEqual(result['physical_ff_bits'], 1)
        self.assertEqual(result['path']['maximum_to_ff_data'], 2)
        self.assertEqual(result['path']['maximum_to_public_output'], 2)
        self.assertEqual(result['physical_ff_bits_not_directly_named'], 0)

    def test_unapproved_cell_macro_count_and_area_refused(self):
        data, registers = fixture()
        for mutation in ('unmapped', 'macro_count', 'zero_area', 'infinite_area'):
            candidate = deepcopy(data)
            if mutation == 'unmapped': candidate['modules']['top']['cells']['a']['type'] = '$and'
            elif mutation == 'zero_area': candidate['modules']['sg13cmos5l_comb_test']['attributes']['area'] = '0'
            elif mutation == 'infinite_area': candidate['modules']['sg13cmos5l_comb_test']['attributes']['area'] = 'inf'
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                metrics(candidate, 'top', registers, macro_count=2 if mutation == 'macro_count' else 0)

    def test_alias_or_vector_state_refused(self):
        data, registers = fixture()
        for mutation in ('duplicate_q', 'vector_q', 'constant_q'):
            candidate = deepcopy(data)
            ff = candidate['modules']['top']['cells']['ff']
            if mutation == 'duplicate_q': candidate['modules']['top']['cells']['ff2'] = deepcopy(ff)
            elif mutation == 'vector_q': ff['connections']['Q'] = [3, 6]
            else: ff['connections']['Q'] = ['0']
            with self.subTest(mutation=mutation), self.assertRaises(ValueError): metrics(candidate, 'top', registers)

    def test_combinational_cycle_and_unknown_input_refused(self):
        for source in (5, 9):
            data, registers = fixture()
            data['modules']['top']['cells']['a']['connections']['A'] = [source]
            with self.subTest(source=source), self.assertRaises(ValueError): metrics(data, 'top', registers)

    def test_pruned_source_name_is_explicit_and_not_hidden_in_total_ff(self):
        data, registers = fixture()
        del data['modules']['top']['netnames']['r_q']
        result = metrics(data, 'top', registers)
        self.assertEqual(result['physical_ff_bits'], 1)
        self.assertEqual(result['physical_ff_bits_not_directly_named'], 1)
        self.assertTrue(result['declared_groups']['state']['registers'][0]['source_netname_pruned'])

    def test_width_change_requires_explicit_onehot_recoding(self):
        data, registers = fixture()
        data['modules']['top']['netnames']['r_q']['bits'] = [3, '0']
        with self.assertRaises(ValueError): metrics(data, 'top', registers)
        data['modules']['top']['netnames']['r_q']['attributes'] = dict(onehot='00000000000000000000000000000001')
        result = metrics(data, 'top', registers)
        self.assertTrue(result['declared_groups']['state']['registers'][0]['fsm_onehot_reencoded'])
        self.assertEqual(result['declared_typed_bits'], 1)
        self.assertEqual(result['physical_ff_bits'], 1)

    def test_complete_source_inventory_and_digital_memory_capacity(self):
        desc = dict(registers=[dict(name='r_word0', width=64), dict(name='r_tx_word0', width=32)])
        values = inventory(desc, 'engine.core.', 'streaming-core')
        self.assertEqual(sum(v['width'] for v in values), 96)
        self.assertEqual(values[0]['group'], 'streaming-core.program_words')
        desc['registers'].append(desc['registers'][0])
        with self.assertRaises(ValueError): inventory(desc, '', 'streaming-core')
        memory = digital_memory_inventory()
        self.assertEqual(len(memory), 130)
        self.assertEqual(len({v['name'] for v in memory}), 130)
        self.assertEqual(sum(v['width'] for v in memory), 8320)

    def test_wrong_library_refused_before_output_or_tool_use(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            library = root / 'bad.lib'
            library.write_text('unmatched')
            called = []
            with self.assertRaises(ValueError):
                map_target(lambda *args, **kwargs: called.append(args), root / 'out',
                    label='bad', top='top', sources=[], registers=[], library=library,
                    yosys='unused', abc='unused')
            self.assertEqual(called, [])
            self.assertFalse((root / 'out').exists())
        with self.assertRaises(ValueError): quoted('x\nread_verilog evil')

    def test_complete_matrix_refuses_macro_omission_or_claim_upgrade(self):
        data, registers = fixture()
        row = metrics(data, 'top', registers)
        row['settings'] = dict(liberty_sha256=LIBRARY_SHA256, abc_constraints=CONSTRAINTS,
            abc_delay_target_ps=10000, synth='-flatten -noabc', retiming=False)
        row['abc_liberty_estimate'] = parse_abc_timing(TIMING_LOG)
        row['artifact_sha256'] = timing_artifacts(row['abc_liberty_estimate'])
        row['native_mapping'] = native_fixture()
        row['artifact_sha256'].update({'native-tmp/' + path: value
            for path, value in row['native_mapping']['artifact_sha256'].items()})
        rows = [deepcopy(row) for _ in range(4)]
        names = ['streaming-d2', 'streaming-d4', 'buffered-v1-macro-excluded', 'buffered-v1-full-digital-ff']
        for index, value in enumerate(rows):
            value['label'] = names[index]
            if index < 2:
                value['declared_groups'] = {'streaming-core.' + name: dict(declared_bits=bits)
                    for name, bits in dict(program_words=4096, tx_fifo_words_and_valid_counts=76 * (index + 1),
                        rx_fifo_words_and_valid_counts=76 * (index + 1), current_cell=64).items()}
                value['declared_groups']['streaming-frontend.all'] = dict(declared_bits=1403)
        rows[2]['excluded_macro_cells'] = 2
        rows[3]['declared_groups'] = {'digital-memory.array_cells': dict(directly_named_ff_bits=8192),
            'digital-memory.synchronous_q': dict(directly_named_ff_bits=128)}
        result = dict(rows=rows, liberty_sha256=LIBRARY_SHA256, emission_inputs_unchanged=True,
            matched_settings=True, mapped_equivalence_proved=False, timing_qualified=False)
        check_comparison(result)
        for field in ('mapped_equivalence_proved', 'timing_qualified'):
            bad = deepcopy(result)
            bad[field] = True
            with self.subTest(field=field), self.assertRaises(ValueError): check_comparison(bad)
        for key in ('array_cells', 'synchronous_q'):
            bad = deepcopy(result)
            bad['rows'][3]['declared_groups']['digital-memory.' + key]['directly_named_ff_bits'] = 0
            with self.subTest(storage=key), self.assertRaises(ValueError): check_comparison(bad)
        bad = deepcopy(result)
        bad['rows'][0]['settings']['abc_constraints'] = 'different load'
        with self.assertRaises(ValueError): check_comparison(bad)
        bad = deepcopy(result)
        del bad['rows'][0]['abc_liberty_estimate']
        with self.assertRaises(ValueError): check_comparison(bad)


if __name__ == '__main__': unittest.main()
