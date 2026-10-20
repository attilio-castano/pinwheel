"""Ready cost emission, backend-contract preservation and freshness refusals."""
import ast
from copy import deepcopy
import inspect
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import streaming_cost as base
import streaming_ready_cost as ready
from test_streaming_cost import fixture, native_fixture, TIMING_LOG, timing_artifacts


def comparison():
    data, registers = fixture()
    row = base.metrics(data, 'top', registers)
    row['settings'] = dict(liberty_sha256=base.LIBRARY_SHA256, abc_constraints=base.CONSTRAINTS,
        abc_delay_target_ps=10000, synth='-flatten -noabc', retiming=False)
    row['abc_liberty_estimate'] = base.parse_abc_timing(TIMING_LOG)
    row['artifact_sha256'] = timing_artifacts(row['abc_liberty_estimate'])
    row['native_mapping'] = native_fixture()
    row['artifact_sha256'].update({'native-tmp/' + path: value
        for path, value in row['native_mapping']['artifact_sha256'].items()})
    rows = [deepcopy(row) for _ in range(4)]
    for index, value in enumerate(rows):
        value.update(label=ready.LABELS[index], boundary=ready.BOUNDARY)
        if index < 2:
            value['declared_groups'] = {'streaming-core.' + name: dict(declared_bits=bits)
                for name, bits in dict(program_words=4096,
                    tx_fifo_words_and_valid_counts=76 * (index + 1),
                    rx_fifo_words_and_valid_counts=76 * (index + 1), current_cell=64).items()}
            value['declared_groups']['streaming-frontend.all'] = dict(declared_bits=1403)
    rows[2]['excluded_macro_cells'] = 2
    rows[3]['declared_groups'] = {'digital-memory.array_cells': dict(directly_named_ff_bits=8192),
        'digital-memory.synchronous_q': dict(directly_named_ff_bits=128)}
    return dict(schema=ready.SCHEMA, boundary=ready.BOUNDARY, rows=rows,
        liberty_sha256=base.LIBRARY_SHA256, emission_inputs_unchanged=True,
        matched_settings=True, mapped_equivalence_proved=False, timing_qualified=False)


class ReadyCostTests(unittest.TestCase):
    def test_ready_identity_normalization_preserves_all_backend_checks_without_mutation(self):
        result = comparison()
        before = deepcopy(result)
        with patch('streaming_ready_cost.base.check_comparison', wraps=base.check_comparison) as check:
            ready.check_comparison(result)
        normalized = check.call_args.args[0]
        self.assertEqual(normalized['schema'], 'pinwheel.streaming-matched-cost.v1')
        self.assertEqual([row['label'] for row in normalized['rows'][:2]], ['streaming-d2', 'streaming-d4'])
        self.assertEqual(result, before)
        self.assertNotIn('facilities absent', ready.BOUNDARY)
        self.assertIn('guarded stream and drive-wait', ready.BOUNDARY)
        self.assertIn('no guaranteed Fmax', ready.BOUNDARY)

    def test_wrong_schema_old_labels_missing_or_reordered_rows_refuse(self):
        for mode in ('old-schema', 'missing-schema', 'old-label', 'reorder', 'missing-row', 'extra-row', 'not-row'):
            result = comparison()
            if mode == 'old-schema': result['schema'] = 'pinwheel.streaming-matched-cost.v1'
            elif mode == 'missing-schema': del result['schema']
            elif mode == 'old-label': result['rows'][0]['label'] = 'streaming-d2'
            elif mode == 'reorder': result['rows'][0], result['rows'][1] = result['rows'][1], result['rows'][0]
            elif mode == 'missing-row': result['rows'].pop()
            elif mode == 'extra-row': result['rows'].append(deepcopy(result['rows'][0]))
            else: result['rows'][0] = None
            with self.subTest(mode=mode), self.assertRaises(ValueError): ready.check_comparison(result)

    def test_program_fifo_cell_frontend_and_both_old_memory_groups_remain_required(self):
        omissions = [(0, 'streaming-core.' + name, 'declared_bits') for name in
            ('program_words', 'tx_fifo_words_and_valid_counts', 'rx_fifo_words_and_valid_counts', 'current_cell')]
        omissions += [(1, 'streaming-frontend.all', 'declared_bits'),
            (3, 'digital-memory.array_cells', 'directly_named_ff_bits'),
            (3, 'digital-memory.synchronous_q', 'directly_named_ff_bits')]
        for row, group, field in omissions:
            result = comparison()
            result['rows'][row]['declared_groups'][group][field] -= 1
            with self.subTest(group=group), self.assertRaises(ValueError): ready.check_comparison(result)

    def test_unmatched_timing_native_cache_hash_or_claim_upgrade_still_refuse(self):
        for mode in ('constraints', 'delay', 'path-hash', 'global-cache', 'native-hash', 'macro-count',
                'timing-upgrade', 'equivalence-upgrade', 'area'):
            result = comparison()
            row = result['rows'][0]
            if mode == 'constraints': row['settings']['abc_constraints'] = 'set_load 1\n'
            elif mode == 'delay': row['abc_liberty_estimate']['delay_ps'] += 1
            elif mode == 'path-hash': row['artifact_sha256']['abc-critical-path.txt'] = '0' * 64
            elif mode == 'global-cache': row['native_mapping']['global_cache_consumed'] = True
            elif mode == 'native-hash': row['artifact_sha256']['native-tmp/abc/input.blif'] = '0' * 64
            elif mode == 'macro-count': result['rows'][2]['excluded_macro_cells'] = 0
            elif mode == 'timing-upgrade': result['timing_qualified'] = True
            elif mode == 'equivalence-upgrade': result['mapped_equivalence_proved'] = True
            else: row['standard_cell_area_um2'] += 1
            with self.subTest(mode=mode), self.assertRaises(ValueError): ready.check_comparison(result)

    def test_fresh_ready_emission_keeps_old_baseline_ports_storage_and_commands(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'physical').mkdir()
            for name in ('buffered_sram_serial_wrapper.sv', 'buffered_sram_memory.sv', 'tt_um_pinwheel_buffered.sv'):
                (root / 'physical' / name).write_text('// exact fixture ' + name + '\n')
            calls = []
            def run(argv, label):
                calls.append((argv, label))
                if '--run' not in argv: return '// independently lowered fixture\n'
                index = argv.index('--run')
                target = argv[index + 1]
                output = Path(argv[index + 3] if target.endswith('BufferedSramSerialExport.lean') else argv[index + 2])
                output.mkdir(parents=True)
                description = dict(registers=[dict(name='r_word0', width=64)])
                if target.endswith('StreamingReadyArtifactEmit.lean'):
                    for name in ('core.mlir', 'frontend.mlir'): (output / name).write_text('fresh ' + name)
                    for name in ('assembly.json', 'frontend-assembly.json'):
                        (output / name).write_text(json.dumps(description))
                else:
                    (output / ('frontend.mlir' if 'SerialExport' in target else 'core.mlir')).write_text('fresh baseline')
                    (output / 'assembly.json').write_text(json.dumps(description))
                return ''
            with patch('streaming_ready_wrapper.package_source', return_value='// Ready package\n'), \
                    patch('streaming_ready_wrapper.tt_source', side_effect=lambda depth: '// Ready TT ' + str(depth) + '\n'):
                targets, frozen = ready.emit_sources(run, root / 'emitted', root=root, circt='circt', lake='lake')
            self.assertEqual([target['label'] for target in targets], list(ready.LABELS))
            self.assertEqual([target['top'] for target in targets[:2]],
                ['tt_um_pinwheel_streaming_ready_d2', 'tt_um_pinwheel_streaming_ready_d4'])
            lean_calls = [argv for argv, _ in calls if '--run' in argv]
            self.assertEqual([argv[5] for argv in lean_calls], ['test/StreamingReadyArtifactEmit.lean'] * 2 +
                ['test/BufferedSramSerialExport.lean', 'test/SramArtifactEmit.lean'])
            self.assertEqual([argv[-1] for argv in lean_calls[:2]], ['1', '2'])
            self.assertEqual(len({label for _, label in calls}), len(calls))
            model = next(node.value.value for node in ast.walk(ast.parse(inspect.getsource(base.emit_sources)))
                if isinstance(node, ast.Assign) and any(isinstance(target, ast.Name) and target.id == 'model'
                    for target in node.targets))
            self.assertEqual((root / 'emitted/old-v1/digital-memory.sv').read_text(), model)
            self.assertEqual((root / 'emitted/old-v1/excluded-macro.sv').read_text(),
                '(* blackbox *) ' + model.split(');', 1)[0] + ');\nendmodule\n')
            self.assertEqual(sum(value['width'] for value in targets[3]['registers']) -
                sum(value['width'] for value in targets[2]['registers']), 8320)
            self.assertTrue(all(base.sha(path) == value for path, value in frozen.items()))
            self.assertTrue(all(str(path) in frozen for target in targets for path in target['sources']))

    def test_unmatched_library_refuses_before_creating_output_or_calling_tools(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            library = root / 'wrong.lib'
            library.write_text('unmatched')
            called = []
            with self.assertRaises(ValueError):
                ready.compare(lambda *args: called.append(args), root / 'out', root=root,
                    library=library, yosys='unused', abc='unused', circt='unused', lake='unused')
            self.assertEqual(called, [])
            self.assertFalse((root / 'out').exists())

    def mocked_compare(self, root, mutation=None):
        library, emitted = root / 'library.lib', root / 'emitted.sv'
        library.write_text('fixture library')
        emitted.write_text('fixture emitted source')
        targets = [dict(label=label) for label in ready.LABELS]
        expected = base.sha(emitted)
        rows, count = comparison()['rows'], []
        real_sha = base.sha
        def sha(path):
            if Path(path) == library and library.read_text() == 'fixture library': return base.LIBRARY_SHA256
            return real_sha(path)
        def emit(*args, **kwargs): return targets, {str(emitted): expected}
        def mapping(*args, **kwargs):
            index = len(count)
            count.append(kwargs['label'])
            row = deepcopy(rows[index])
            row['boundary'] = base.BOUNDARY
            if mutation: mutation(index, library, emitted)
            return row
        with patch('streaming_ready_cost.base.sha', side_effect=sha), \
                patch('streaming_ready_cost.emit_sources', side_effect=emit), \
                patch('streaming_ready_cost.base.map_target', side_effect=mapping):
            return ready.compare(lambda *args: None, root / 'result', root=root,
                library=library, yosys='unused', abc='unused', circt='unused', lake='unused'), count

    def test_compare_uses_backend_and_saves_new_schema_boundary_without_changing_base(self):
        with tempfile.TemporaryDirectory() as temporary:
            result, calls = self.mocked_compare(Path(temporary))
            self.assertEqual(calls, list(ready.LABELS))
            self.assertEqual(result['schema'], ready.SCHEMA)
            self.assertEqual(result['boundary'], ready.BOUNDARY)
            self.assertTrue(all(row['boundary'] == ready.BOUNDARY for row in result['rows']))
            self.assertIn('facilities absent', base.BOUNDARY)
            self.assertEqual(json.loads((Path(temporary) / 'result/report.json').read_text()), result)

    def test_changed_emission_refuses_before_next_mapping_and_at_closeout(self):
        for at in (0, 3):
            with self.subTest(after_mapping=at), tempfile.TemporaryDirectory() as temporary:
                def mutation(index, library, emitted):
                    if index == at: emitted.write_text('changed after frozen emission')
                with self.assertRaisesRegex(RuntimeError, 'input changed'):
                    self.mocked_compare(Path(temporary), mutation)
                self.assertFalse((Path(temporary) / 'result/report.json').exists())

    def test_library_changed_during_mapping_refuses_at_closeout(self):
        with tempfile.TemporaryDirectory() as temporary:
            def mutation(index, library, emitted):
                if index == 0: library.write_text('changed library')
            with self.assertRaisesRegex(RuntimeError, 'library input changed'):
                self.mocked_compare(Path(temporary), mutation)
            self.assertFalse((Path(temporary) / 'result/report.json').exists())


if __name__ == '__main__': unittest.main()
