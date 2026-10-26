"""Controls for the new scoped coordinator; no containers or Native tools run."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_8x4_final_connectivity as C


class ConnectivityTests(unittest.TestCase):
    def test_command_keeps_exact_readonly_target_offline_bounds_and_no_init(self):
        argv = C.command(Path('/new-output'), 'sha256:' + 'a' * 64, 'pinwheel-final-test',
                         '12345678-1234-1234-1234-123456789abc')
        for key, value in [('--cpus', '1'), ('--memory', '2048m'), ('--memory-swap', '2048m'),
                           ('--network', 'none'), ('--pull', 'never'), ('--cap-drop', 'ALL')]:
            self.assertEqual(argv[argv.index(key) + 1], value)
        self.assertIn('type=bind,source=/new-output/inputs,target=/inputs,readonly', argv)
        self.assertIn('--read-only', argv)
        self.assertEqual(argv[-5:], ['openroad', '-no_init', '-exit', '-python', '/inputs/launch.py'])
        with self.assertRaises(ValueError): C.command(Path('/new'), 'latest', 'pinwheel-test', '123')

    def fixture(self, temporary):
        output = Path(temporary); directory = output / 'native/export'; directory.mkdir(parents=True)
        (directory / 'connectivity.json').write_text('{"fixture":"actual connectivity"}')
        (directory / 'inventory.json').write_text('{"fixture":"complete inventory"}')
        request = dict(target=dict(actual_odb=dict(sha256='a' * 64)))
        receipt = dict(schema='pinwheel.streaming-tt-odb-export.v1', read_only_database=True, top=C.T.TOP,
            database_sha256='a' * 64, reference_sha256=C.T.FLAT_REFERENCE_SHA256,
            source_sha256=C.T.NATIVE_EXPORTER_SHA256,
            artifacts_sha256={name: C.sha(directory / name) for name in ('connectivity.json', 'inventory.json')})
        path = directory / 'receipt.json'; path.write_text(json.dumps(receipt))
        return output, dict(request=request), path, receipt

    def test_native_closeout_binds_target_reference_exporter_and_complete_artifacts(self):
        with tempfile.TemporaryDirectory() as temporary:
            output, packet, path, original = self.fixture(temporary)
            self.assertEqual(C.validate_native(output, packet)['database_sha256'], 'a' * 64)
            for key, value in [('database_sha256', 'b' * 64), ('reference_sha256', 'c' * 64),
                               ('source_sha256', 'd' * 64), ('read_only_database', False), ('top', 'another_top')]:
                changed = copy.deepcopy(original); changed[key] = value; path.write_text(json.dumps(changed))
                with self.subTest(key=key), self.assertRaises(ValueError): C.validate_native(output, packet)
            path.write_text(json.dumps(original))
            (output / 'native/export/connectivity.json').write_text('changed after native use')
            with self.assertRaisesRegex(ValueError, 'output changed'): C.validate_native(output, packet)


if __name__ == '__main__': unittest.main()
