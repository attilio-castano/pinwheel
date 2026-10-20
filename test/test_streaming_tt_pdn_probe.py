"""The cheap native geometry probe must stay bounded and reject stale inputs."""
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_tt_pdn_probe as P


class ProbeTests(unittest.TestCase):
    def test_container_is_offline_swapless_and_readonly_inputs_and_pdk(self):
        command = P.container_command(Path('/tmp/pdn-probe'), 'exact-image', 'pinwheel-pdn-test')
        for flag, value in [('--memory', '6g'), ('--memory-swap', '6g'), ('--cpus', '4'), ('--network', 'none')]:
            self.assertEqual(command[command.index(flag) + 1], value)
        self.assertTrue(any('target=/probe/inputs,readonly' in value for value in command))
        self.assertTrue(any('target=/work/pdk,readonly' in value for value in command))
        self.assertNotIn('pull', command)
        for name in ('', 'foreign', 'pinwheel-bad/name', 'pinwheel-bad name'):
            with self.subTest(name=name), self.assertRaises(ValueError):
                P.container_command(Path('/tmp/probe'), 'image', name)

    def test_input_inventory_rejects_symlink_membership(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); (root / 'file').write_text('bytes')
            before = P.inventory(root)
            (root / 'extra').write_text('bytes')
            self.assertNotEqual(P.inventory(root), before)
            (root / 'alias').symlink_to(root / 'file')
            with self.assertRaisesRegex(ValueError, 'Aliased'): P.inventory(root)

    def test_pdk_directory_alias_is_bound_and_escape_refused(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); (root / 'inside').mkdir(); (root / 'inside/file').write_text('one')
            (root / 'alias').symlink_to('inside', target_is_directory=True)
            before = P.inventory_pdk(root)
            self.assertTrue(before['alias']['directory'])
            (root / 'inside/file').write_text('two')
            self.assertNotEqual(P.inventory_pdk(root), before)
            (root / 'escape').symlink_to(root.parent, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, 'Escaping'): P.inventory_pdk(root)


if __name__ == '__main__': unittest.main()
