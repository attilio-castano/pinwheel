from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import streaming_8x4_rc_protocol as P
import streaming_8x4_rc_batch as B


class BlockSelectionTests(unittest.TestCase):
    def setUp(self):
        self.plan = {'protocol': P.frozen_protocol(), 'cases': [{'name': 'U'}, {'name': 'heldout'}]}
        self.ladder = self.plan['protocol']['manual_solver']['mesh_ladder']

    def test_explicit_contiguous_continuation_is_preserved(self):
        self.assertEqual(B.selection(self.plan, ['U'], self.ladder[1:]),
                         [('U', mesh) for mesh in self.ladder[1:]])

    def test_duplicate_unknown_skipped_and_reordered_requests_fail(self):
        for cases, meshes in [(['U', 'U'], self.ladder), (['unknown'], self.ladder),
                              (['U'], [self.ladder[0], self.ladder[2]]),
                              (['U'], list(reversed(self.ladder))),
                              (['U'], [self.ladder[0], self.ladder[0]])]:
            with self.assertRaises(ValueError): B.selection(self.plan, cases, meshes)


if __name__ == '__main__': unittest.main()
