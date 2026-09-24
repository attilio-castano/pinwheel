"""Added clock/data buffers require functional, geometry and coarse timing evidence."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import test_physical_route_intake as existing
from physical_buffer_repair import compare_buffer_repair
from physical_route_intake import validate_repair_route
from validation_run import sha


class AddedRoute(unittest.TestCase):
    def fixture(self, root):
        args = existing.RouteIntake().fixture(root)
        root = args['root']

        def write(name, data):
            p = root / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(data if isinstance(data, str) else json.dumps(data))
            return p

        def ref(p):
            return dict(path=str(p.relative_to(root)), sha256=sha(p))

        corners = ['fast', 'slow', 'typ']
        resolved = write('build/physical/design/runs/control/resolved.json',
                         dict(STA_CORNERS=corners, LAYERS_RC=args['overrides']['LAYERS_RC']))
        source = write('build/physical/design/source.odb', 'original database')
        parent = write('parent.json', dict(odb='/work/core/source.odb', metrics={}))
        inv = root / 'build/physical/control-invocation.json'
        data = json.loads(inv.read_text()); data.update(exit_code=0, overrides=args['overrides'])
        write(str(inv.relative_to(root)), data)
        physical = write('control.json', dict(tag='control', invocation_sha256=sha(inv),
            state_sha256=sha(parent), artifact_sha256={str(source.relative_to(root)):sha(source)}))
        odb, netlist = root/'repair/repaired.odb', root/'measure/implemented.v'
        probe = write('repair/report.json', dict(status='passed', source_unchanged=True, physical_tag='control',
            containers={'probe':'absent'}, source_database=str(source.relative_to(root)),
            source_database_sha256=sha(source), artifacts_sha256={'repaired.odb':sha(odb)}))

        def buffer(size, a, x):
            return dict(type='sg13cmos5l_buf_'+size, parameters={}, port_directions={'A':'input','X':'output'},
                        connections={'A':[a],'X':[x]})

        original = dict(ports={'clk':dict(direction='input',bits=[2]), 'i':dict(direction='input',bits=[3]),
                               'o':dict(direction='output',bits=[4])}, cells={
            'clock':buffer('1',2,5), 'q':dict(type='sg13cmos5l_dfrbpq_1',parameters={},
                port_directions={'CLK':'input','D':'input','Q':'output'},connections={'CLK':[5],'D':[3],'Q':[4]})})
        candidate = deepcopy(original)
        candidate['cells']['clock']['type'] = 'sg13cmos5l_buf_4'
        candidate['cells']['repeat'] = buffer('8',5,6)
        candidate['cells']['q']['connections']['CLK'] = [6]
        before = write('functional/before.json', {'modules':{'chip':original}})
        after = write('functional/after.json', {'modules':{'chip':candidate}})
        reference_export = write('reference/implemented.v', 'oracle original export')
        oracle = write('oracle.json', dict(status='passed', edges=12, mutants_rejected=1,
                       input_sha256={str(reference_export):sha(reference_export)}))
        proof = compare_buffer_repair(original, candidate, allow_resizing=True)
        functional = write('functional/report.json', dict(status='passed', module='chip', oracle=ref(oracle),
            exports={'before':ref(reference_export),'after':ref(netlist)},
            readbacks={'before':ref(before),'after':ref(after)}, connectivity=proof,
            inputs_sha256={str(reference_export.relative_to(root)):sha(reference_export)},
            artifacts_sha256={'before.json':sha(before),'after.json':sha(after)}))
        context = dict(instances={
            'clock':dict(cell='sg13cmos5l_buf_4', macro=False,bbox=[1,1,2,2]),
            'q':dict(cell='sg13cmos5l_dfrbpq_1',macro=False,bbox=[3,1,4,2])},
            nets={}, ports={}, rows=[], placement_blockages=[], power_shapes=[], routing_obstructions=[],
            macro_obstructions=[], die=[0,0,10,10], layers=[], exclusions={'clear':True},
            macro_pins=[dict(instance='macro',pin='D',net='old',bbox=[5,1,5.2,1.2])])
        for net,pin,kind in [('VPWR','VDD','POWER'),('VGND','VSS','GROUND')]:
            context['nets'][net] = dict(type=kind,ports=[],terminals=[dict(instance=n,pin=pin,direction='INOUT')
                                                                   for n in context['instances']])
        reference_context = write('reference/context.json', context)
        context['instances']['repeat'] = dict(cell='sg13cmos5l_buf_8',macro=False,bbox=[2,2,3,3])
        context['macro_pins'][0]['net'] = 'buffered'
        for net,pin in [('VPWR','VDD'),('VGND','VSS')]:
            context['nets'][net]['terminals'].append(dict(instance='repeat',pin=pin,direction='INOUT'))
        selected_context = write('measure/context.json',context)
        reference = write('reference/report.json',dict(status='passed',containers={'reference':'absent'},
            source_database_sha256=sha(source),target={'state_flip_flops':1},target_path_expected={'clock':True},
            artifacts_sha256={'context.json':sha(reference_context)}))
        timing = dict(timing__setup__ws=.08,timing__hold__ws=.07,timing__setup_vio__count=0,timing__hold_vio__count=0,
            design__max_fanout_violation__count=0,design__max_slew_violation__count=0,design__max_cap_violation__count=0)
        quality = dict(wire_annotation=dict(complete_for_consumed_nets=True,partially_unannotated=0,consumed_unannotated=[]))
        measure = write('measure/report.json',dict(status='passed',containers={'measure':'absent'},
            source_database=str(odb.relative_to(root)),source_database_sha256=sha(odb),netlist=str(netlist.relative_to(root)),
            netlist_sha256=sha(netlist),repair_probe=ref(probe),inputs_sha256={str(resolved.relative_to(root)):sha(resolved)},
            corridor_clear=True,nominal_layer_rc_verified=True,target=dict(database_sha256=sha(odb),state_flip_flops=1),
            target_path_expected={'clock':True},estimation_modes={c:'global_routing' for c in corners},
            fresh_timing={c:deepcopy(timing) for c in corners},measurement_quality={c:deepcopy(quality) for c in corners},
            artifacts_sha256={'context.json':sha(selected_context),'implemented.v':sha(netlist)}))
        report = write('validation/report.json',dict(status='passed',local_estimated_timing_pass=True,
            decision='retain-local-repair-require-fresh-whole-chip-coarse-route-and-pin-access',
            stages={'selected':dict(producer=ref(probe),measurement=ref(measure))},
            selected_database=ref(odb),selected_netlist=ref(netlist),functional={'buffer_identity':proof},artifact_sha256={}))
        args['selection_path'].write_text(json.dumps(dict(schema=4,status='passed',
            decision='admit-one-validated-added-buffer-coarse-route',validation=ref(report),candidate='selected',
            reference_measurement=ref(reference),parent_state=ref(parent),parent_physical=ref(physical),functional=ref(functional))))
        return args

    def edit(self,args,name,change):
        """Update hashes after semantic mutations so rejection is not merely stale bytes."""
        root=args['root']; p=root/name; d=json.loads(p.read_text()); change(d); p.write_text(json.dumps(d))
        for name in ['measure/report.json','functional/report.json','validation/report.json','selected.json']:
            p=root/name; d=json.loads(p.read_text())
            def refs(obj):
                if isinstance(obj,dict):
                    if set(obj)=={'path','sha256'}:obj['sha256']=sha(root/obj['path'])
                    for k,v in obj.items():
                        if k=='artifacts_sha256':
                            for file in v:v[file]=sha(p.parent/file)
                        else:refs(v)
                elif isinstance(obj,list):
                    for v in obj:refs(v)
            refs(d);p.write_text(json.dumps(d))

    def test_accepts_added_clock_branch_and_prior_resize(self):
        with tempfile.TemporaryDirectory() as folder:
            r=validate_repair_route(**self.fixture(Path(folder)))
            self.assertEqual((r['added_buffers'],r['prior_resized_buffers'],r['pin_edges_reused']),(1,1,12))
            self.assertEqual(r['timing_admission'],'positive-coarse-margins-complete-wire-estimates')

    def test_rejects_bad_clock_connection_even_with_rehashed_readback(self):
        with tempfile.TemporaryDirectory() as folder:
            args=self.fixture(Path(folder))
            self.edit(args,'functional/after.json',lambda d:d['modules']['chip']['cells']['repeat']['connections'].update(A=[3]))
            with self.assertRaisesRegex(ValueError,'Changed connectivity'):
                validate_repair_route(**args)

    def test_rejects_moved_original_macro_or_unbound_buffer(self):
        changes=[lambda d:d['instances']['q'].update(bbox=[4,1,5,2]),
                 lambda d:d['instances']['clock'].update(cell='sg13cmos5l_buf_8'),
                 lambda d:d['macro_pins'][0].update(bbox=[6,1,6.2,1.2]),
                 lambda d:d['nets']['VPWR']['terminals'].pop(),
                 lambda d:d['nets']['VGND']['terminals'][0].update(pin='VDD'),
                 lambda d:d['exclusions'].update(clear=False)]
        for change in changes:
            with self.subTest(change=change),tempfile.TemporaryDirectory() as folder:
                args=self.fixture(Path(folder));self.edit(args,'measure/context.json',change)
                with self.assertRaises(ValueError):validate_repair_route(**args)

    def test_rejects_incomplete_or_failing_measurements(self):
        changes=[lambda d:d['fresh_timing']['slow'].update(timing__setup__ws=-.01),
                 lambda d:d['fresh_timing']['fast'].update(timing__hold__ws=0),
                 lambda d:d['fresh_timing']['fast'].update(timing__hold__ws=float('nan')),
                 lambda d:d['fresh_timing']['slow'].update(design__max_cap_violation__count=1),
                 lambda d:d['fresh_timing']['slow'].update(timing__setup_vio__count=1),
                 lambda d:d['measurement_quality']['slow']['wire_annotation'].update(partially_unannotated=1),
                 lambda d:d['measurement_quality']['slow']['wire_annotation'].update(consumed_unannotated=['loaded']),
                 lambda d:d['estimation_modes'].update(slow='placement'),
                 lambda d:d.update(nominal_layer_rc_verified=False),
                 lambda d:d['target'].update(state_flip_flops=2),
                 lambda d:d['containers'].update(measure='running')]
        for change in changes:
            with self.subTest(change=change),tempfile.TemporaryDirectory() as folder:
                args=self.fixture(Path(folder));self.edit(args,'measure/report.json',change)
                with self.assertRaises(ValueError):validate_repair_route(**args)

    def test_rejects_stale_candidate_and_changed_stage_or_controls(self):
        for name in ['repair/repaired.odb','measure/implemented.v','functional/before.json','parent.json',
                     'build/physical/design/source.odb','build/physical/design/repaired.odb',
                     'build/physical/design/inputs.json','build/physical/design/runs/control/resolved.json']:
            with self.subTest(name=name),tempfile.TemporaryDirectory() as folder:
                args=self.fixture(Path(folder));(args['root']/name).write_text('changed')
                with self.assertRaises(ValueError):validate_repair_route(**args)
        with tempfile.TemporaryDirectory() as folder:
            args=self.fixture(Path(folder))
            for change in [dict(timeout_seconds=601),dict(stop_step='OpenROAD.DetailedRouting'),
                           dict(from_step='OpenROAD.CTS'),dict(overrides=dict(args['overrides'],RUN_ANTENNA_REPAIR=True)),
                           dict(overrides=dict(args['overrides'],LAYERS_RC={}))]:
                with self.subTest(change=change),self.assertRaises(ValueError):validate_repair_route(**dict(args,**change))
            state=json.loads(args['state_path'].read_text());state['metrics']={'inherited_slack':5}
            args['state_path'].write_text(json.dumps(state))
            with self.assertRaisesRegex(ValueError,'only ODB'):validate_repair_route(**args)

    def test_verifies_shared_pdk_inputs_and_rejects_other_external_roots(self):
        with tempfile.TemporaryDirectory() as folder,tempfile.TemporaryDirectory() as external:
            args=self.fixture(Path(folder))
            # A real setup shares a pinned PDK outside the checkout. Move this
            # fixture's PDK and preserve all of its installed/input identities.
            import shutil
            moved=Path(external)/'pdk'
            shutil.move(args['pdk_root'],moved);args['pdk_root']=moved
            view=moved/'model.v';view.write_text('pinned model')
            self.edit(args,'oracle.json',lambda d:d['input_sha256'].update({str(view):sha(view)}))
            validate_repair_route(**args)
            executable=Path(external)/'simulator';executable.write_text('pinned executable')
            alias=args['root']/'build/tools/simulator';alias.parent.mkdir(parents=True);alias.symlink_to(executable)
            def add_tool(d):
                d['commands']=[{'argv':[str(alias)]}]
                d['input_sha256'][str(executable)]=sha(executable)
            self.edit(args,'oracle.json',add_tool)
            validate_repair_route(**args)
            executable.write_text('changed executable')
            with self.assertRaisesRegex(ValueError,'Changed functional input'):validate_repair_route(**args)
            executable.write_text('pinned executable')
            library=Path(external)/'cells.lib';library.write_text('pinned cell library')
            local_lib=args['root']/'build/tools/cells.lib';local_lib.symlink_to(library)
            self.edit(args,'functional/report.json',lambda d:d['inputs_sha256'].update({str(local_lib):sha(local_lib)}))
            validate_repair_route(**args)
            library.write_text('changed library')
            with self.assertRaisesRegex(ValueError,'Changed functional input'):validate_repair_route(**args)
            library.write_text('pinned cell library')
            view.write_text('changed model')
            with self.assertRaisesRegex(ValueError,'Changed functional input'):validate_repair_route(**args)
            view.write_text('pinned model')
            unrelated=Path(external)/'unrelated.v';unrelated.write_text('outside')
            self.edit(args,'oracle.json',lambda d:d['input_sha256'].update({str(unrelated):sha(unrelated)}))
            with self.assertRaisesRegex(ValueError,'Input outside'):validate_repair_route(**args)


if __name__=='__main__':
    unittest.main()
