"""HOST adaptation controls; unchanged strict CAP parser is covered by C1 tests."""
import inspect
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import streaming_8x4_rc_consumer_cap as C
import streaming_8x4_rc_consumer_cap_v2 as V
import streaming_8x4_rc_consumer_cap_readback as R
import streaming_8x4_rc_consumer_cap_v2_readback as S


class VersionControls(unittest.TestCase):
    def test_only_one_extraction_Tcl_token_changes(self):
        old = C.tcl(); new = V.version2_tcl(old)
        self.assertEqual(new.replace('-version 2.0', '-version 1.0'), old)
        self.assertEqual(new.count('-version 2.0'), 1)
        with self.assertRaises(ValueError): V.version2_tcl(old.replace('-coupling_threshold 0', '-coupling_threshold .1'))

    def test_every_geometry_parser_and_physics_function_is_frozen_C1(self):
        self.assertEqual(V.JOBS, C.JOBS)
        for name in ('definition', 'parse_leaf', 'measurements', 'vector', 'relative', 'cgroups'):
            self.assertIs(getattr(V, name), getattr(C, name))
        for job in V.JOBS:
            self.assertEqual(C.fixture(V.definition(job)), C.fixture(C.definition(job)))
        self.assertEqual(V.protocol()['extractor_version'], '2.0')
        old, new = C.protocol(), V.protocol()
        del old['extractor_version'], new['extractor_version'], old['qualification_scope'], new['qualification_scope']
        self.assertEqual(old, new)

    def test_worker_body_only_typed_schema_adaptation(self):
        actual = inspect.getsource(V.run).replace('pinwheel.streaming-8x4-rc-consumer-cap-version2-execution.v1',
                                                'pinwheel.streaming-8x4-rc-consumer-cap-execution.v1')
        self.assertEqual(actual, inspect.getsource(C.run))

    def test_reader_only_module_and_typed_schema_adaptation(self):
        actual = Path(S.__file__).read_text().replace('import streaming_8x4_rc_consumer_cap_v2 as W',
                                                    'import streaming_8x4_rc_consumer_cap as W')
        actual = actual.replace('pinwheel.streaming-8x4-rc-consumer-cap-version2-execution.v1',
                                'pinwheel.streaming-8x4-rc-consumer-cap-execution.v1')
        actual = actual.replace('pinwheel.streaming-8x4-rc-consumer-cap-version2-independent-readback.v1',
                                'pinwheel.streaming-8x4-rc-consumer-cap-independent-readback.v1')
        self.assertEqual(actual, Path(R.__file__).read_text())
        self.assertEqual(S.accuracy(None, None, None, None)['accuracy_status'], 'unmeasured')


if __name__ == '__main__': unittest.main()
