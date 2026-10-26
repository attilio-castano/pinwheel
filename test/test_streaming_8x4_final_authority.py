"""Exercise real complete-state parser/bijection and new export admission."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_8x4_final_authority as A

DFF = '''library(test){cell(sg13cmos5l_inv_1){pin(A){direction:"input";}
pin(Y){direction:"output";function:"!A";}}cell(sg13cmos5l_dfrbpq_1){
pin(Q){direction:"output";function:"IQ";}pin(CLK){clock:true;direction:"input";}
pin(D){direction:"input";}pin(RESET_B){direction:"input";}
ff(IQ,IQN){clear:"!RESET_B";clocked_on:"CLK";next_state:"D";}}}'''


class AuthorityTests(unittest.TestCase):
    def test_authority_reopener_refuses_promoted_status_or_changed_frozen_input(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);source=root/'physical-report.json';source.write_text('exact original')
            record=dict(schema='pinwheel.streaming-8x4-final-authority.v1',passed=True,qualified=False,
                native_executed=False,final_public_wire_passed=False,final_correspondence_proved=False,
                physical_acceptance=False,actual_state_bits=6039,input_sha256={str(source):A.sha(source)})
            path=root/'preparation.json';source.write_text('changed after staging')
            path.write_text(json.dumps(record))
            with self.assertRaisesRegex(ValueError,'input changed'):A.verify(path)
            for key,value in [('native_executed',True),('final_public_wire_passed',True),('passed',False),
                              ('final_correspondence_proved',True),('physical_acceptance',True),('actual_state_bits',6038)]:
                changed=copy.deepcopy(record);changed[key]=value;path.write_text(json.dumps(changed))
                with self.subTest(key=key),self.assertRaisesRegex(ValueError,'authority required'):A.verify(path)

    def fixture(self, root):
        library = root / 'cells.lib'; library.write_text(DFF)
        cells, source, flat = {}, [], []
        for index in range(6039):
            name = 'ff' + str(index); q = 100 + index
            cells[name] = dict(type='sg13cmos5l_dfrbpq_1', parameters={},
                connections=dict(CLK=[2], D=[5], RESET_B=[4], Q=[q]),
                port_directions=dict(CLK='input', D='input', RESET_B='input', Q='output'))
            common = dict(component='core-d2', register='r_state', index=index)
            source.append(dict(common, candidate_ff=name, candidate_q=q, candidate_d=5,
                               candidate_clock=2, candidate_cell='sg13cmos5l_dfrbpq_1'))
            flat.append(dict(common, ff=name, q=q, d=5, clock=2, cell='sg13cmos5l_dfrbpq_1'))
        cells['actualLogic'] = dict(type='sg13cmos5l_inv_1', parameters={}, connections={'A':[3],'Y':[5]},
                                    port_directions={'A':'input','Y':'output'})
        document = dict(modules={A.C.T.TOP:dict(ports=dict(clk=dict(direction='input', bits=[2]),
            data=dict(direction='input', bits=[3]), reset=dict(direction='input', bits=[4]),
            output=dict(direction='output', bits=[100])), netnames={}, cells=cells)})
        paths = []
        for name, value in [('candidate', document), ('source-map', {'rows':source}),
                            ('flat', document), ('flat-map', {'rows':flat}), ('actual', document)]:
            path = root / (name + '.json'); path.write_text(json.dumps(value)); paths.append(path)
        return paths, library, document

    def test_full6039_real_graph_map_and_wrong_source_pin_or_actual_inventory_refuse(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); paths, library, document = self.fixture(root)
            with patch.dict(A.LIBRARIES, typ=('fixture', hashlib.sha256(DFF.encode()).hexdigest())):
                rows, resized = A.map_all_state(*paths, library)
                self.assertEqual(len(rows), 6039); self.assertEqual(resized, [])
                original = json.loads(paths[1].read_text())
                changed = copy.deepcopy(original); changed['rows'][0]['candidate_q'] += 1
                paths[1].write_text(json.dumps(changed))
                with self.assertRaisesRegex(ValueError, 'Q/D/clock/master'): A.map_all_state(*paths, library)
                paths[1].write_text(json.dumps(original))
                del document['modules'][A.C.T.TOP]['cells']['ff6038']; paths[4].write_text(json.dumps(document))
                with self.assertRaisesRegex(ValueError, 'exact full semantic bijection'): A.map_all_state(*paths, library)

    def test_fresh_export_must_close_native_and_complete_artifact_membership(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); native = root / 'native/export'; native.mkdir(parents=True)
            (native / 'receipt.json').write_text('{}'); (root / 'native.log').write_text('actual log fixture')
            prep = root / 'preparation.json'; prep.write_text('{}')
            packet = dict(request={'target':{'actual_odb':{'sha256':'a'*64}},
                'physical_candidate':{'schema':'pinwheel.streaming-8x4-physical-candidate.v1','kind':'original-8x4'}},
                producer_sha256={}, producer_commit='b'*40)
            report = dict(schema='pinwheel.streaming-8x4-final-connectivity-run.v1', passed=True, status='exported', exit_code=0,
                inputs_runtime_unchanged=True, container_termination={'status':'absent'}, qualified=False,
                physical_acceptance=False, final_correspondence_proved=False, preparation=A.bind(prep),
                target=packet['request']['target'], source_sha256={}, producer_commit='b'*40, native_binding={'exact':True},
                physical_candidate=packet['request']['physical_candidate'],
                artifact_sha256={'native/export/receipt.json':A.sha(native/'receipt.json')}, native_log_sha256=A.sha(root/'native.log'))
            path = root / 'report.json'; path.write_text(json.dumps(report))
            with patch.object(A.C, 'verify', return_value=packet), patch.object(A.C, 'validate_native', return_value={'exact':True}):
                self.assertEqual(A.closed_export(path,A.sha(path))[0],report)
                for key, value in [('status','timed_out'), ('exit_code',False), ('final_correspondence_proved',True),
                                   ('inputs_runtime_unchanged',False), ('passed',False),
                                   ('physical_candidate',{'kind':'unselected-repair'})]:
                    changed = copy.deepcopy(report); changed[key] = value; path.write_text(json.dumps(changed))
                    with self.subTest(key=key), self.assertRaises(ValueError): A.closed_export(path,A.sha(path))
                path.write_text(json.dumps(report)); (native/'unrecorded-output').write_text('extra')
                with self.assertRaisesRegex(ValueError,'artifact membership'): A.closed_export(path,A.sha(path))


if __name__ == '__main__': unittest.main()
