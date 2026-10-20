"""Physical acceptance must refuse missing, substituted or skipped checks."""
from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_tt_signoff as S


class OfficialSignoffTests(unittest.TestCase):
    def test_check_inventory_comes_from_actual_source_and_tech(self):
        source = """
def main():
    checks = [
        {'name': 'Both', 'check': lambda: unknown()},
        {'name': 'Other tech', 'techs': ['other'], 'check': lambda: unknown()},
        {'name': 'CMOS5L', 'techs': ['ihp-sg13cmos5l'], 'check': lambda: unknown()}]
"""
        self.assertEqual(S.selected_checks(source, 'ihp-sg13cmos5l'), ['Both', 'CMOS5L'])
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            S.selected_checks(source.replace("'CMOS5L'", "'Both'"), 'ihp-sg13cmos5l')
        with self.assertRaisesRegex(ValueError, 'inventory'):
            S.selected_checks(source.replace('checks = [', 'something_else = ['), 'ihp-sg13cmos5l')

    def report(self, root, names=('A', 'B')):
        xml = ET.Element('testsuites')
        suite = ET.SubElement(xml, 'testsuite', name='Tiny Tapeout Prechecks')
        for name in names:
            ET.SubElement(suite, 'testcase', name=name, time='0.01')
        path = root / 'results.xml'
        ET.ElementTree(xml).write(path)
        return path, xml, suite

    def test_missing_duplicated_reordered_or_skipped_checks_cannot_pass(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path, xml, suite = self.report(root)
            self.assertTrue(S.precheck_result(path, ['A', 'B'], 0)['passed'])
            for names in [('A',), ('A', 'A'), ('B', 'A'), ('A', 'B', 'C')]:
                path, _, _ = self.report(root, names)
                with self.subTest(names=names), self.assertRaisesRegex(ValueError, 'checks'):
                    S.precheck_result(path, ['A', 'B'], 0)
            path, xml, suite = self.report(root)
            ET.SubElement(suite[0], 'skipped')
            ET.ElementTree(xml).write(path)
            with self.assertRaisesRegex(ValueError, 'skipped'):
                S.precheck_result(path, ['A', 'B'], 0)

    def test_native_exit_and_actual_error_nodes_must_agree(self):
        with tempfile.TemporaryDirectory() as tmp:
            path, xml, suite = self.report(Path(tmp))
            with self.assertRaisesRegex(ValueError, 'disagreement'):
                S.precheck_result(path, ['A', 'B'], 1)
            ET.SubElement(suite[1], 'error', message='real layout short').text = 'Native DRC details'
            ET.ElementTree(xml).write(path)
            with self.assertRaisesRegex(ValueError, 'disagreement'):
                S.precheck_result(path, ['A', 'B'], 0)
            result = S.precheck_result(path, ['A', 'B'], 1)
            self.assertFalse(result['passed'])
            self.assertEqual(result['failures'][0]['check'], 'B')
            self.assertEqual(result['failures'][0]['message'], 'real layout short')

    def test_nonfinite_duration_json_and_unsupported_report_shapes_refuse(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for value in ['nan', 'inf', '-1']:
                path, xml, suite = self.report(root)
                suite[0].set('time', value); ET.ElementTree(xml).write(path)
                with self.subTest(value=value), self.assertRaisesRegex(ValueError, 'duration'):
                    S.precheck_result(path, ['A', 'B'], 0)
            path = root / 'bad.json'
            for text in ['{"passed":true,"passed":false}', '{"value":NaN}', '{"value":Infinity}']:
                path.write_text(text)
                with self.assertRaises(ValueError): S.read(path)
            path, xml, suite = self.report(root)
            ET.SubElement(xml, 'testsuite', name='Second')
            ET.ElementTree(xml).write(path)
            with self.assertRaisesRegex(ValueError, 'shape'):
                S.precheck_result(path, ['A', 'B'], 0)

    def test_source_hash_receipt_cannot_replace_pinned_git_blob(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); path = root / 'precheck.py'; data = b'official input'
            path.write_bytes(data)
            blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
            lock = dict(support_files={'precheck.py': dict(git_blob=blob, sha256=S.sha(path))})
            S.verify_support(root, lock)
            path.write_bytes(b'changed source'); changed = deepcopy(lock)
            changed['support_files']['precheck.py']['sha256'] = S.sha(path)
            with self.assertRaisesRegex(ValueError, 'source differs'):
                S.verify_support(root, changed)
            changed = dict(support_files={'../escape': dict(git_blob=blob, sha256='unused')})
            with self.assertRaisesRegex(ValueError, 'Escaping'):
                S.verify_support(root, changed)

    def test_input_mutation_and_alias_refuse(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); source = root / 'input.gds'; source.write_bytes(b'input')
            frozen = {str(source): S.sha(source)}; S.unchanged(frozen)
            source.write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError, 'changed'):
                S.unchanged(frozen)
            alias = root / 'alias'; alias.symlink_to(source)
            with self.assertRaisesRegex(ValueError, 'aliased'):
                S.regular(alias)

    def test_runtime_alias_retarget_refuses_even_when_payload_bytes_match(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name in ['first', 'second']:
                (root / name).write_bytes(b'identical payload')
            link = root / 'alias'; link.symlink_to('first')
            aliases = {}
            payload = S.inventory(root, aliases=aliases)
            S.unchanged(payload); S.unchanged_aliases(aliases)
            link.unlink(); link.symlink_to('second')
            S.unchanged(payload)
            with self.assertRaisesRegex(ValueError, 'alias changed'):
                S.unchanged_aliases(aliases)

    def test_preexisting_bytecode_is_frozen_and_inherited_python_options_are_removed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); cache = root / '__pycache__'; cache.mkdir()
            bytecode = cache / 'official.cpython-312.pyc'; bytecode.write_bytes(b'compiled input')
            payload = S.inventory(root)
            self.assertIn(str(bytecode.resolve()), payload)
            bytecode.write_bytes(b'changed compiled input')
            with self.assertRaisesRegex(ValueError, 'changed'): S.unchanged(payload)
        cleaned = S.python_environment(dict(PATH='/bin', PYTHONHOME='wrong', PYTHONOPTIMIZE='2',
            PYTHONPATH='/unreviewed', __PYVENV_LAUNCHER__='wrong', PRIVATE_TOKEN='retained but never serialized'))
        self.assertNotIn('PYTHONHOME', cleaned); self.assertNotIn('PYTHONOPTIMIZE', cleaned)
        self.assertNotIn('__PYVENV_LAUNCHER__', cleaned)
        self.assertEqual(cleaned['PYTHONPATH'], ''); self.assertEqual(cleaned['PYTHONNOUSERSITE'], '1')

    def test_missing_or_unclosed_native_precheck_processes_refuse(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); path = root / 'native.jsonl'
            for events in ([], [dict(event='intent', identity='unfinished', argv=[])]):
                path.write_text(''.join(json.dumps(event)+'\n' for event in events))
                with self.assertRaisesRegex(ValueError, 'native official'):
                    S.native_journal(path, out=root, pdk=root/'pdk', owner='owner', image_id='image', gds=root/'in.gds')

    def native_fixture(self, root):
        root = root.resolve(); cwd = root / 'tt/precheck'; (cwd / 'reports').mkdir(parents=True)
        pdk = root / 'pdk'; gds = root / 'input.gds'; gds.write_bytes(b'frozen GDS')
        config = dict(out=str(root), pdk=str(pdk), owner='owner', image_id='sha256:'+'a'*64,
            container_name=S.container_name(root))
        config_path = root / 'native-config.json'; S.write(config_path, config)
        checks = ('pin_label_purposes_overlapping_drawing', 'sg13cmos5l', 'zero_area')
        scripts = ('tech-files/pin_label_purposes_overlapping_drawing.rb.drc',
            str(pdk / 'ihp-sg13cmos5l/libs.tech/klayout/tech/drc/ihp-sg13cmos5l.drc'),
            'tech-files/zeroarea.rb.drc')
        commands = []
        def native(command):
            commands.append(command)
            Path(command[-1].removeprefix('report_file=')).write_bytes(b'native DRC report')
            return S.subprocess.CompletedProcess(command, 0)
        with patch.object(S.Path, 'cwd', return_value=cwd), patch.object(S.subprocess, 'run', side_effect=native):
            for check, script in zip(checks, scripts):
                report = cwd / 'reports' / ('drc_' + check + '.xml')
                arguments = ['-b', '-r', script, '-rd', check+'=true', '-rd', 'input='+str(gds),
                    '-rd', 'thr=1', '-rd', 'report='+str(report), '-rd', 'report_file='+str(report)]
                self.assertEqual(S.native_klayout(config_path, arguments), 0)
        return config, config_path, commands, gds

    def test_three_official_calls_use_one_exact_name_and_disabled_swap(self):
        with tempfile.TemporaryDirectory(prefix='signoff-') as tmp:
            root = Path(tmp).resolve(); config, _, commands, gds = self.native_fixture(root)
            self.assertEqual(len(commands), 3)
            for command in commands:
                for flag, value in [('--name', S.container_name(root)), ('--memory', '2g'),
                        ('--memory-swap', '2g'), ('--cpus', '1'), ('--network', 'none')]:
                    self.assertEqual(command.count(flag), 1)
                    self.assertEqual(command[command.index(flag)+1], value)
            closed = S.native_journal(root/'native-klayout.jsonl', out=root, pdk=Path(config['pdk']),
                owner=config['owner'], image_id=config['image_id'], gds=gds)
            self.assertTrue(closed['passed']); self.assertEqual(closed['closed_processes'], 3)

    def test_journal_refuses_unbounded_swap_or_unowned_container(self):
        with tempfile.TemporaryDirectory(prefix='signoff-') as tmp:
            root = Path(tmp).resolve(); config, _, _, gds = self.native_fixture(root)
            path = root / 'native-klayout.jsonl'
            original = [json.loads(line) for line in path.read_text().splitlines()]
            for flag, value in [('--memory-swap', None), ('--memory-swap', '4g'),
                    ('--name', None), ('--name', 'pinwheel-signoff-other')]:
                events = deepcopy(original); argv = events[0]['argv']; index = argv.index(flag)
                if value is None: del argv[index:index+2]
                else: argv[index+1] = value
                path.write_text(''.join(json.dumps(event)+'\n' for event in events))
                with self.subTest(flag=flag, value=value), self.assertRaisesRegex(ValueError, 'arguments/report differ'):
                    S.native_journal(path, out=root, pdk=Path(config['pdk']), owner=config['owner'],
                        image_id=config['image_id'], gds=gds)

    def test_mismatched_container_config_refuses_before_native_intent(self):
        with tempfile.TemporaryDirectory(prefix='signoff-') as tmp:
            root = Path(tmp).resolve(); config = root / 'config.json'
            S.write(config, dict(out=str(root), pdk=str(root/'pdk'), owner='owner', image_id='image',
                container_name='pinwheel-signoff-other'))
            with patch.object(S.Path, 'cwd', return_value=root), patch.object(S.subprocess, 'run') as native:
                with self.assertRaisesRegex(ValueError, 'container name differs'):
                    S.native_klayout(config, [])
                native.assert_not_called()
            self.assertFalse((root/'native-klayout.jsonl').exists())


if __name__ == '__main__':
    unittest.main()
