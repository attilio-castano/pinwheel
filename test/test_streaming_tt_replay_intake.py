"""Closed native replay journals must match intent, results and actual bytes."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from streaming_tt_replay_intake import journal_matches,sha


class ReplayJournalTests(unittest.TestCase):
    def fixture(self,root):
        compiler=root/'lean';source=root/'Proof.lean';log=root/'Proof.log'
        compiler.write_bytes(b'compiler');source.write_text('theorem checked : True := True.intro\n');log.write_text('')
        command=dict(argv=[str(compiler),str(source)],compiler_sha256_before=sha(compiler),
            compiler_sha256_after=sha(compiler),source_sha256_before=sha(source),source_sha256_after=sha(source),
            exit_code=0,log=str(log),log_sha256=sha(log),module='Proof')
        intent={key:value for key,value in command.items() if key in ('argv','compiler_sha256_before','source_sha256_before','module')}
        rows=[dict(event='intent',**intent),dict(event='result',**command)]
        path=root/'journal.jsonl';return path,command,rows

    def test_exact_closed_operation_accepted(self):
        with tempfile.TemporaryDirectory() as tmp:
            path,command,rows=self.fixture(Path(tmp));path.write_text(''.join(json.dumps(row)+'\n' for row in rows))
            self.assertEqual(journal_matches(path,[command]),rows)

    def test_missing_extra_reordered_and_forged_intent_refuse(self):
        with tempfile.TemporaryDirectory() as tmp:
            path,command,rows=self.fixture(Path(tmp));forged=deepcopy(rows);forged[0]['argv']=['other-compiler','other-source']
            for values in (rows[:1],rows+rows,list(reversed(rows)),forged):
                path.write_text(''.join(json.dumps(row)+'\n' for row in values))
                with self.subTest(values=values),self.assertRaises(ValueError):journal_matches(path,[command])

    def test_changed_actual_log_or_source_rejects_matching_receipt_rows(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);path,command,rows=self.fixture(root);path.write_text(''.join(json.dumps(row)+'\n' for row in rows))
            (root/'Proof.log').write_text('unrecorded failure')
            with self.assertRaisesRegex(ValueError,'source/compiler/log changed'):journal_matches(path,[command])


if __name__=='__main__':unittest.main()
