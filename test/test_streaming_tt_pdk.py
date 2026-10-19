"""Missing public-deck dependencies cannot replace existing PDK identities."""
from copy import deepcopy
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_tt_pdk as P


def fixture(root):
    entries = []; hashes = {}
    for name, data in [('base.drc',b'unchanged deck'), *[(name,b'{"drc_rules":{}}') for name in sorted(P.EXTRAS)]]:
        path = root/name; path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes(data)
        hashes[name] = dict(git_blob=P.blob(data),sha256=P.sha(path))
        entries.append(dict(path=name,mode='100644',sha=P.blob(data)))
    (root/'alias').symlink_to('base.drc')
    entries.append(dict(path='alias',mode='120000',sha=P.blob(b'base.drc')))
    tree = root.parent/'pdk-tree.json'; tree.write_text(json.dumps(dict(truncated=False,tree=entries)))
    lock = dict(pdk_revision='pinned',pdk_tree_sha256=P.sha(tree))
    (root/'installed.json').write_text(json.dumps(dict(revision='pinned',tree_sha256=P.sha(tree),
        files_sha256={'base.drc':hashes['base.drc']['sha256']},symlinks={'alias':'base.drc'})))
    completion = dict(pdk_completion_revision='pinned',pdk_extra_files={name:hashes[name] for name in P.EXTRAS})
    return lock,completion,tree


class PDKCompletionTests(unittest.TestCase):
    def test_exact_same_commit_additions_and_all_original_entries(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'pdk';root.mkdir();lock,completion,tree=fixture(root)
            result=P.verify_complete_pdk(root,lock,completion,tree_path=tree)
            self.assertEqual(result['regular_files'],4);self.assertEqual(result['symlinks'],1)
            self.assertFalse(result['rule_or_deck_edits']);self.assertFalse(result['native_checker_pass'])

    def test_missing_extra_and_unrecorded_payload_refuse(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'pdk';root.mkdir();lock,completion,tree=fixture(root)
            path=root/'unrecorded.drc';path.write_bytes(b'unrecorded rule override')
            with self.assertRaisesRegex(ValueError,'membership'): P.verify_complete_pdk(root,lock,completion,tree_path=tree)
            path.unlink();(root/next(iter(P.EXTRAS))).unlink()
            with self.assertRaisesRegex(ValueError,'completion file'): P.verify_complete_pdk(root,lock,completion,tree_path=tree)

    def test_changed_sha_receipt_cannot_override_original_git_blob(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'pdk';root.mkdir();lock,completion,tree=fixture(root)
            name=next(iter(P.EXTRAS));path=root/name;path.write_bytes(b'{"drc_rules":{"weakened":true}}')
            completion['pdk_extra_files'][name]['sha256']=P.sha(path)
            completion['pdk_extra_files'][name]['git_blob']=P.blob(path.read_bytes())
            with self.assertRaisesRegex(ValueError,'pinned Git blob'): P.verify_complete_pdk(root,lock,completion,tree_path=tree)

    def test_old_file_mutation_and_alias_retarget_refuse(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'pdk';root.mkdir();lock,completion,tree=fixture(root)
            original=(root/'base.drc').read_bytes();(root/'base.drc').write_bytes(b'edited deck')
            with self.assertRaisesRegex(ValueError,'changed'): P.verify_complete_pdk(root,lock,completion,tree_path=tree)
            (root/'base.drc').write_bytes(original)
            (root/'alias').unlink();(root/'alias').symlink_to(next(iter(P.EXTRAS)))
            with self.assertRaisesRegex(ValueError,'symlink'): P.verify_complete_pdk(root,lock,completion,tree_path=tree)

    def test_extra_scope_and_revision_cannot_expand(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'pdk';root.mkdir();lock,completion,tree=fixture(root)
            for bad in (dict(completion,pdk_completion_revision='other'),
                    dict(completion,pdk_extra_files={**completion['pdk_extra_files'],'other':{}})):
                with self.assertRaisesRegex(ValueError,'scope'):P.verify_complete_pdk(root,lock,bad,tree_path=tree)


if __name__=='__main__':unittest.main()
