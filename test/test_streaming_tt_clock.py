"""The checked CTS network retains physical cells instead of erasing buffers."""
from copy import deepcopy
from hashlib import sha256
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from streaming_tt_certificate import parse_graph,read_library
from streaming_tt_clock import model,generate
from test_streaming_tt_certificate import LIB,TYPES,fixture,cell


class ActualClockDAG(unittest.TestCase):
    def setUp(self):
        temporary=tempfile.TemporaryDirectory();self.addCleanup(temporary.cleanup)
        path=Path(temporary.name)/'cells.lib';path.write_text(LIB)
        self.library=read_library(path,TYPES,expected_sha256=sha256(LIB.encode()).hexdigest())

    def test_all_connected_inverters_buffer_and_reset_driver_remain(self):
        graph=parse_graph(fixture(),'top',self.library);order=tuple(ff.name for ff in graph.flipflops)
        actual,record=model(graph,state_order=order)
        self.assertEqual(len(actual['nodes']),4)
        self.assertEqual(set(record['actual_cone_cells']),{gate.name for gate in graph.gates})
        self.assertEqual(record['ff_order'],order)
        modules,metadata=generate(graph,state_order=order,prefix='ClockTest',namespace='ClockTest',
            clock_certificate={'module':'ClockCertificate','namespace':'ClockCertificate'})
        self.assertEqual(metadata['actual_cone_cells'],record['actual_cone_cells'])
        self.assertIn('theorem actual_positive',modules['ClockTestProof'])
        self.assertIn('theorem actual_inactive',modules['ClockTestProof'])
        self.assertIn('ClockTestTransportProof',modules)

    def test_unused_clock_load_branch_still_has_a_checked_cell(self):
        doc=fixture();doc['modules']['top']['cells']['unusedCTS']=cell('buf_4',dict(A=2,X=9),'X')
        graph=parse_graph(doc,'top',self.library)
        actual,record=model(graph,state_order=tuple(ff.name for ff in graph.flipflops))
        self.assertEqual(len(actual['nodes']),5)
        unused=next(gate.name for gate in graph.gates if 'unusedCTS' in gate.name)
        self.assertIn(unused,record['actual_cone_cells'])
        self.assertIn(unused,record['actual_clock_cells'])

    def test_missing_duplicate_and_unknown_physical_state_roots_refuse(self):
        graph=parse_graph(fixture(),'top',self.library);name=graph.flipflops[0].name
        for order in ((),(name,name),('unknown',)):
            with self.subTest(order=order),self.assertRaisesRegex(ValueError,'cover every physical FF'):
                model(graph,state_order=order)

    def test_negative_clock_or_live_reset_cannot_be_certified(self):
        for field,value in [('CLK',6),('RESET_B','0')]:
            doc=deepcopy(fixture());doc['modules']['top']['cells']['ff']['connections'][field]=[value]
            graph=parse_graph(doc,'top',self.library)
            with self.subTest(field=field),self.assertRaises(ValueError):
                generate(graph,state_order=tuple(ff.name for ff in graph.flipflops),prefix='BadClock',
                    namespace='BadClock',clock_certificate={'module':'ClockCertificate','namespace':'ClockCertificate'})


if __name__=='__main__':unittest.main()
