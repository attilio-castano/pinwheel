"""HOST runtime authority rejects stale pins and narrowed/mislabelled receipts."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_8x4_final_runtime as R


class RuntimeTests(unittest.TestCase):
    def test_assembly_pins_existing_host_tools_and_requires_all_nine(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); host = {}
            for name in ('python', 'lean', 'lake'):
                path = root / name; path.write_text(name); host[name] = str(path)
            pins = {name: R.digest(path) for name, path in host.items()}
            assembly = dict(schema='pinwheel.streaming-8x4-common-cad-runtime.v1', executable_launched=False,
                qualified=False, tools={name: str(root / name) for name in ('circt', 'yosys', 'abc', 'solver', 'iverilog', 'vvp')})
            path = root / 'assembly.json'; path.write_text(json.dumps(assembly))
            with patch.object(R, 'HOST_TOOLS', host), patch.object(R, 'HOST_PINS', pins):
                self.assertEqual(len(R.tools_from_assembly(path)), 9)
                (root / 'lean').write_text('changed executable')
                with self.assertRaisesRegex(ValueError, 'host executable changed'): R.tools_from_assembly(path)
                (root / 'lean').write_text('lean')
                del assembly['tools']['solver']; path.write_text(json.dumps(assembly))
                with self.assertRaisesRegex(ValueError, 'nine'): R.tools_from_assembly(path)

    def test_closed_audit_never_substitutes_native_or_broad_membership_claims(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); request = root / 'request.json'; request.write_text('{}')
            config = dict(producer_commit='a' * 40, producer_sha256={'selected.py': 'b' * 64}, tools={'native': '/pinned'})
            original = dict(schema='pinwheel.streaming-8x4-final-runtime-audit.v1', passed=True, qualified=False,
                executable_launched=False, native_versions_checked=False, tool_identity_unchanged=True,
                tool_identity_before={'selected': 'exact'}, tool_identity_after={'selected': 'exact'},
                cad_runtime_archive_membership={'cad_selected_archive_membership_verified': True},
                request={'path': str(request), 'sha256': R.digest(request)}, **config)
            path = root / 'report.json'; path.write_text(json.dumps(original))
            with patch.object(R, 'verify_request', return_value=config):
                self.assertEqual(R.closed_report(path), original)
                for key, value in [('native_versions_checked', True), ('executable_launched', True), ('qualified', True),
                                   ('tool_identity_after', {'selected': 'changed'}), ('cad_runtime_archive_membership', {})]:
                    changed = copy.deepcopy(original); changed[key] = value; path.write_text(json.dumps(changed))
                    with self.subTest(key=key), self.assertRaises(ValueError): R.closed_report(path)
                path.write_text(json.dumps(original)); request.write_text('{"changed":true}')
                with self.assertRaisesRegex(ValueError, 'request changed'): R.closed_report(path)

    def test_nonfinite_or_duplicate_authority_json_is_refused(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'report.json'
            for payload in ('{"passed":true,"passed":false}', '{"time":Infinity}'):
                path.write_text(payload)
                with self.assertRaises(ValueError): R.read(path)


if __name__ == '__main__': unittest.main()
