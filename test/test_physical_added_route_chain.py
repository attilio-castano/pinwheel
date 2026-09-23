"""A repaired parent needs both cumulative and immediate edit checks."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import test_physical_added_route as baseline
from physical_buffer_repair import compare_buffer_repair
from physical_route_intake import validate_repair_route
from validation_run import sha


class ChainedRoute(unittest.TestCase):
    def fixture(self,root):
        args=baseline.AddedRoute().fixture(root)
        def read(name):return json.loads((root/name).read_text())
        def write(name,data):
            p=root/name;p.parent.mkdir(parents=True,exist_ok=True)
            p.write_text(data if isinstance(data,str) else json.dumps(data));return p
        def ref(p):return dict(path=str(p.relative_to(root)),sha256=sha(p))
        original=read('functional/before.json')['modules']['chip']
        source=read('functional/after.json')['modules']['chip']
        after=deepcopy(source)
        after['cells']['data']=dict(type='sg13cmos5l_buf_8',parameters={},
            port_directions={'A':'input','X':'output'},connections={'A':[3],'X':[7]})
        after['cells']['q']['connections']['D']=[7]
        source_json=write('functional/source.json',{'modules':{'chip':source}})
        write('functional/after.json',{'modules':{'chip':after}})
        source_export=write('reference/source.v','the repaired parent export')
        source_context=read('measure/context.json')
        write('reference/context.json',source_context)
        candidate_context=deepcopy(source_context)
        candidate_context['instances']['data']=dict(cell='sg13cmos5l_buf_8',macro=False,bbox=[5,5,6,6])
        for net,pin in [('VPWR','VDD'),('VGND','VSS')]:
            candidate_context['nets'][net]['terminals'].append(dict(instance='data',pin=pin,direction='INOUT'))
        write('measure/context.json',candidate_context)
        reference=read('reference/report.json')
        reference.update(netlist=str(source_export.relative_to(root)),netlist_sha256=sha(source_export))
        reference['artifacts_sha256'].update({'context.json':sha(root/'reference/context.json'),'source.v':sha(source_export)})
        write('reference/report.json',reference)
        immediate=compare_buffer_repair(source,after)
        cumulative=compare_buffer_repair(original,after,allow_resizing=True)
        functional=read('functional/report.json')
        functional.update(source=dict(export=ref(source_export),readback=ref(source_json)),
            source_connectivity=immediate,connectivity=cumulative)
        functional['artifacts_sha256'].update({'source.json':sha(source_json),'after.json':sha(root/'functional/after.json')})
        write('functional/report.json',functional)
        identity=write('validation/identity.json',dict(status='passed',exact_plan_implemented=True,proof=immediate))
        validation=read('validation/report.json')
        stage=validation.pop('stages')['selected']
        validation.update(stage,decision='retain-local-signal-repair-require-whole-chip-qualification',
            local_electrical_pass=True,functional={'identity':ref(identity)})
        write('validation/report.json',validation)
        self.edit(args,'selected.json',lambda d:None)
        return args

    def edit(self,args,name,change):
        baseline.AddedRoute().edit(args,name,change)

    def test_accepts_parent_and_immediate_buffer_identity(self):
        with tempfile.TemporaryDirectory() as folder:
            result=validate_repair_route(**self.fixture(Path(folder)))
            self.assertEqual((result['added_buffers'],result['prior_added_buffers'],
                              result['total_added_buffers'],result['prior_resized_buffers']),(1,1,2,1))
            self.assertIn('local_identity',result['evidence'])

    def test_requires_both_source_link_and_immediate_proof(self):
        for field in ['source','source_connectivity']:
            with self.subTest(field=field),tempfile.TemporaryDirectory() as folder:
                args=self.fixture(Path(folder))
                self.edit(args,'functional/report.json',lambda d:d.pop(field))
                with self.assertRaisesRegex(ValueError,'Incomplete repaired-source'):
                    validate_repair_route(**args)

    def test_rejects_source_export_unlinked_from_measured_parent(self):
        with tempfile.TemporaryDirectory() as folder:
            args=self.fixture(Path(folder))
            self.edit(args,'reference/report.json',lambda d:d.update(netlist='unrelated.v'))
            with self.assertRaisesRegex(ValueError,'Unlinked repaired-source'):
                validate_repair_route(**args)

    def test_rejects_corrupted_ancestor_even_with_updated_hashes(self):
        with tempfile.TemporaryDirectory() as folder:
            args=self.fixture(Path(folder))
            self.edit(args,'functional/source.json',lambda d:d['modules']['chip']['cells']['repeat']['connections'].update(A=[3]))
            with self.assertRaisesRegex(ValueError,'Changed connectivity'):
                validate_repair_route(**args)

    def test_rejects_changes_to_previous_buffers_in_the_new_edit(self):
        with tempfile.TemporaryDirectory() as folder:
            args=self.fixture(Path(folder));root=args['root']
            self.edit(args,'functional/after.json',lambda d:d['modules']['chip']['cells']['repeat'].update(type='sg13cmos5l_buf_4'))
            original=json.loads((root/'functional/before.json').read_text())['modules']['chip']
            after=json.loads((root/'functional/after.json').read_text())['modules']['chip']
            # The cumulative proof still passes; the immediate contract must fail.
            cumulative=compare_buffer_repair(original,after,allow_resizing=True)
            self.edit(args,'functional/report.json',lambda d:d.update(connectivity=cumulative))
            with self.assertRaisesRegex(ValueError,'Changed original cell: repeat'):
                validate_repair_route(**args)

    def test_rejects_false_local_proof_and_unbound_previous_buffer(self):
        changes=[('validation/identity.json',lambda d:d['proof'].update(added_instances=['repeat','data'])),
                 ('validation/identity.json',lambda d:d.update(exact_plan_implemented=False)),
                 ('measure/context.json',lambda d:d['nets']['VPWR']['terminals'].pop(2))]
        for name,change in changes:
            with self.subTest(name=name),tempfile.TemporaryDirectory() as folder:
                args=self.fixture(Path(folder));self.edit(args,name,change)
                with self.assertRaises(ValueError):validate_repair_route(**args)


if __name__=='__main__':unittest.main()
