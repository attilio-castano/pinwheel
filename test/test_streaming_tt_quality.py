"""Missing wire annotation and logical rail defects cannot become passes."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from streaming_tt_quality import logical_power,timing_quality,check_receipts
from streaming_tt_rc import CORNERS
from streaming_tt_signoff import sha


def fixture():
    terminals={pin:dict(direction=direction,signal_type=kind,net=net) for pin,direction,kind,net in
        [('A','INPUT','SIGNAL','a'),('X','OUTPUT','SIGNAL','z'),('VDD','INOUT','POWER','VPWR'),('VSS','INOUT','GROUND','VGND')]}
    return dict(schema='pinwheel.streaming-tt-odb-inventory.v1',
        nets={name:dict(wire=index,signal_type=kind) for index,(name,kind) in enumerate(
            [('a','SIGNAL'),('z','SIGNAL'),('VPWR','POWER'),('VGND','GROUND')],2)},
        masters={'buf':{pin:{key:row[key] for key in ('direction','signal_type')} for pin,row in terminals.items()}},
        instances={'buffer':dict(master='buf',terminals=terminals)},unconnected_signal_outputs={},
        public_bterms={'a':{'net':'a','direction':'input'},'z':{'net':'z','direction':'output'}},
        power_bterms={name:dict(net=name,direction='INOUT',signal_type=kind) for name,kind in [('VPWR','POWER'),('VGND','GROUND')]})


class PhysicalQualityTests(unittest.TestCase):
    def test_closed_receipt_composition_creates_output_and_rejects_mismatched_odb(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary).resolve();native=root/'native';native.mkdir();export=root/'export';export.mkdir()
            database=root/'actual.odb';database.write_bytes(b'actual routed db')
            constraint=root/'actual.sdc';constraint.write_text('create_clock -period 20')
            inventory=export/'inventory.json';inventory.write_text(json.dumps(fixture()))
            exported=export/'receipt.json';packet=dict(schema='pinwheel.streaming-tt-odb-export.v1',
                read_only_database=True,database_sha256=sha(database),artifacts_sha256={'inventory.json':sha(inventory)})
            exported.write_text(json.dumps(packet))
            corners={}
            for corner in CORNERS:
                directory=native/corner;directory.mkdir();checks=directory/'checks.rpt';log=directory/'openroad-stamidpnr.log'
                checks.write_text('Found 0 unannotated drivers.\nFound 0 partially unannotated drivers.\n')
                log.write_text('PINWHEEL_PROPAGATED_CLOCK 1\n')
                corners[corner]=dict(artifacts_sha256={'checks.rpt':sha(checks),'openroad-stamidpnr.log':sha(log)},
                    metrics={'design__max_fanout_violation__count__corner:'+corner:0})
            native_report=native/'report.json';native_report.write_text(json.dumps(dict(
                schema='pinwheel.streaming-tt-fresh-sta.v1',measurements_completed=True,inputs_unchanged=True,
                mode='nominal',corners=corners,assessment={'status':'passed'})))
            host=root/'report.json';host.write_text(json.dumps(dict(schema='pinwheel.streaming-tt-fresh-sta-host.v1',
                status='completed',exit_code=0,inputs_unchanged=True,owned_container_absent=True,mode='nominal',
                closed_constraint_sha256={str(constraint):sha(constraint)},native_report_sha256=sha(native_report),
                input_sha256={str(database):sha(database)})))
            out=root/'fresh/nested/report.json'
            with patch('subprocess.check_output',return_value='committed\n'):
                result=check_receipts(host,exported,out)
            self.assertTrue(out.is_file());self.assertTrue(result['annotation_complete_for_consumed_nets'])
            packet['database_sha256']='0'*64;exported.write_text(json.dumps(packet))
            with self.assertRaisesRegex(ValueError,'different actual ODBs'):
                check_receipts(host,exported,root/'other/report.json')

    def test_logical_rails_pass_but_missing_pin_or_public_rail_rejects(self):
        source=fixture();self.assertTrue(logical_power(source)['passed'])
        changed=deepcopy(source);changed['instances']['buffer']['terminals']['VDD']['net']=None
        self.assertFalse(logical_power(changed)['passed'])
        changed=deepcopy(source);del changed['power_bterms']['VPWR']
        self.assertFalse(logical_power(changed)['passed'])

    def test_consumed_unannotated_output_cannot_be_treated_as_unused(self):
        text='Found 0 unannotated drivers.\n\nFound 0 partially unannotated drivers.\n'
        self.assertTrue(timing_quality(fixture(),text)['annotation_complete_for_consumed_nets'])
        text='Found 1 unannotated drivers.\nbuffer/X\nFound 0 partially unannotated drivers.\n'
        result=timing_quality(fixture(),text)
        self.assertFalse(result['annotation_complete_for_consumed_nets'])
        self.assertEqual(result['wire_annotation']['consumed_unannotated'],[{'driver':'buffer/X','net':'z','loads':1}])

    def test_aliased_rail_and_signal_pin_or_unknown_annotation_refuses(self):
        changed=fixture();changed['instances']['buffer']['terminals']['VDD']['net']='VGND'
        with self.assertRaisesRegex(ValueError,'power/signal boundary'):logical_power(changed)
        with self.assertRaisesRegex(ValueError,'Unresolved unannotated'):
            timing_quality(fixture(),'Found 1 unannotated drivers.\nunknown/X\nFound 0 partially unannotated drivers.\n')

    def test_consumed_floating_net_refuses_even_if_sta_annotation_reports_zero_missing(self):
        changed=fixture();changed['instances']['buffer']['terminals']['A']['net']='floating'
        changed['nets']['floating']=dict(wire=6,signal_type='SIGNAL')
        with self.assertRaisesRegex(ValueError,'lacks exactly one driver'):
            timing_quality(changed,'Found 0 unannotated drivers.\n\nFound 0 partially unannotated drivers.\n')


if __name__=='__main__':unittest.main()
