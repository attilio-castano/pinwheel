"""Historical proof reuse rejects incomplete builds and unrelated controls."""
import copy
import io
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import streaming_8x4_foundation as P


class FoundationTests(unittest.TestCase):
    def record(self):
        return dict(passed=True, modules=649, serial_build=True,
            committed_input_membership_verified=True, inherited_override_guard_checked=True,
            exit_code=0, lean_resource_limits=['-M4096', '-j1', '-DElab.async=false'],
            executable_suites=65, kernel_suites=8, untrusted_axiom_rejected=True,
            unused_private_axiom_rejected=True, audited_declarations=44383,
            audited_theorems=25323, retained_snapshot=str(P.OLD / P.FOUNDATION / 'snapshot'),
            retained_library=str(P.OLD / P.FOUNDATION / 'snapshot/.lake/build/lib/lean'))

    def test_incomplete_or_redirected_foundation_cannot_be_reused(self):
        original = self.record()
        P.check_foundation(original)
        for key, value in [('passed', False), ('modules', 648), ('exit_code', True),
                           ('unused_private_axiom_rejected', False), ('retained_library', '/other')]:
            changed = dict(original, **{key: value})
            with self.subTest(key=key), self.assertRaises(ValueError):
                P.check_foundation(changed)

    def commands(self):
        record = self.record()
        record['commands'] = [dict(label='build-Pinwheel.A', exit_code=0),
            dict(label='build-Pinwheel', exit_code=0), dict(label='axioms', exit_code=0),
            dict(label='reject-untrusted-axiom', exit_code=1),
            dict(label='reject-unused-private-axiom', exit_code=1)]
        logs = {'axioms': 'Pinwheel audit: 44383 declarations, 25323 theorems; standard axioms only.',
            'reject-untrusted-axiom': 'Unapproved axioms in Pinwheel.CI.untrusted',
            'reject-unused-private-axiom': 'Unapproved axioms in _private.Pinwheel.CI.FoundationPrivateControl.0.forbiddenUnused'}
        return record, logs

    def test_build_membership_and_unrelated_control_failures_are_rejected(self):
        original, logs = self.commands()
        modules = ['Pinwheel.A', 'Pinwheel']
        P.check_commands(original, modules, logs)
        for mutate in ('missing', 'reordered', 'failed_positive', 'missing_rejection', 'unrelated'):
            record, output = copy.deepcopy(original), dict(logs)
            if mutate == 'missing': record['commands'].pop(0)
            if mutate == 'reordered': record['commands'][:2] = reversed(record['commands'][:2])
            if mutate == 'failed_positive': record['commands'][0]['exit_code'] = 1
            if mutate == 'missing_rejection': record['commands'][-1]['exit_code'] = 0
            if mutate == 'unrelated': output['reject-unused-private-axiom'] = 'compiler allocation failed'
            with self.subTest(mutate=mutate), self.assertRaises(ValueError):
                P.check_commands(record, modules, output)

    def test_source_bridge_requires_actual_and_committed_bytes_and_exact_membership(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            (root / 'source.lean').write_bytes(b'import Lean\n')
            projection = {'source.lean': P.R.digest(root / 'source.lean')}
            def archive(names):
                data = io.BytesIO()
                with tarfile.open(fileobj=data, mode='w') as stream:
                    for name, payload in names:
                        member = tarfile.TarInfo(name); member.size = len(payload)
                        stream.addfile(member, io.BytesIO(payload))
                return subprocess.CompletedProcess([], 0, data.getvalue(), b'')
            with patch.object(P, 'ROOT', root):
                for rows in ([('source.lean', b'import Lean\n')],
                             [('source.lean', b'import Wrong\n')],
                             [('source.lean', b'import Lean\n'), ('extra.lean', b'')]):
                    with patch.object(P.subprocess, 'run', return_value=archive(rows)):
                        if len(rows) == 1 and rows[0][1] == b'import Lean\n':
                            P.committed_projection('a' * 40, projection)
                        else:
                            with self.assertRaises(ValueError): P.committed_projection('a' * 40, projection)
                (root / 'source.lean').write_bytes(b'changed working bytes')
                with self.assertRaisesRegex(ValueError, 'Current foundation/runtime input changed'):
                    P.committed_projection('a' * 40, projection)


if __name__ == '__main__': unittest.main()
