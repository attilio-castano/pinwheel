from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from physical_repair_plan import build_explicit_plan, validate_plan, render_tcl
from physical_distribution_route import validate_exact_edit
from physical_distribution_acceptance import qualify_candidate
from test_physical_connections import fixture
import test_physical_distribution_acceptance as acceptance


def explicit_fixture():
    context, _ = fixture()
    geometry = dict(buffer_masters={
        'sg13cmos5l_buf_1':dict(width_dbu=2, height_dbu=4),
        'sg13cmos5l_buf_8':dict(width_dbu=6, height_dbu=4)},
        pins={'d/X':[dict(bbox_dbu=[11,1,12,2])], 'q/D':[dict(bbox_dbu=[20,1,21,2])],
              'memory/A_DIN[0]':[dict(bbox_dbu=[69,10,70,11])]})
    requests = [dict(net='n', mode='receiver', receiver='q/D', cells=['sg13cmos5l_buf_1']*2, purpose='hold'),
                dict(net='u', mode='receiver', receiver='memory/A_DIN[0]', cells=['sg13cmos5l_buf_8'], purpose='electrical')]
    plan = build_explicit_plan(requests, context, geometry, dict(path='source.odb',sha256='frozen'))
    return context, plan, requests, geometry


class PathRepair(unittest.TestCase):
    def test_mixed_sizes_and_endpoint_chain_account_every_stage(self):
        context, plan, _, _ = explicit_fixture()
        result = validate_plan(plan, context, 'frozen')
        self.assertEqual(result['operations'], 2)
        self.assertEqual(result['added_buffers'], 3)
        self.assertEqual(result['added_area_um2'], 40)
        recipe = render_tcl(plan, context, 'frozen')
        self.assertIn('findITerm {q/D}', recipe)
        self.assertIn('findNet {path_0_0_net}', recipe)
        self.assertIn('findNet {path_0_1_net}', recipe)
        self.assertNotIn('repair_timing', recipe)
        self.assertNotIn('detailed_route', recipe)

    def test_control_receiver_is_explicit_not_assumed_to_be_upload_data(self):
        context, _, requests, geometry = explicit_fixture()
        context['nets']['u']['terminals'][1]['pin'] = 'A_REN'
        geometry['pins']['memory/A_REN'] = geometry['pins'].pop('memory/A_DIN[0]')
        requests[1]['receiver'] = 'memory/A_REN'
        plan = build_explicit_plan(requests, context, geometry, dict(sha256='frozen'))
        self.assertEqual(validate_plan(plan, context, 'frozen')['added_buffers'], 3)

    def test_hold_intent_cannot_target_clock_or_macro(self):
        for change in [lambda c,p:p['operations'][1].update(purpose='hold'),
                       lambda c,p:c['nets']['n'].update(type='CLOCK')]:
            c,p,_,_ = explicit_fixture(); change(c,p)
            with self.assertRaises(ValueError):validate_plan(p,c,'frozen')

    def test_stale_driver_and_shared_port_change_fail(self):
        for change in [lambda p:p['operations'][0]['ports'].clear(),
                       lambda p:p['operations'][0].update(driver_cell='sg13cmos5l_buf_8')]:
            c,p,_,_ = explicit_fixture(); change(p)
            with self.assertRaises(ValueError):validate_plan(p,c,'frozen')

    def test_second_stage_cannot_overlap_alias_or_invent_a_cell(self):
        for change in [lambda p:p['operations'][0]['stages'][1].update(footprint_dbu=p['operations'][0]['stages'][0]['footprint_dbu']),
                       lambda p:p['operations'][0]['stages'][1].update(new_net='src'),
                       lambda p:p['operations'][0]['stages'][1].update(cell='inverter'),
                       lambda p:p['buffer_sizes_dbu']['sg13cmos5l_buf_1'].__setitem__(0,3)]:
            c,p,_,_ = explicit_fixture(); change(p)
            with self.assertRaises(ValueError):validate_plan(p,c,'frozen')

    def test_exact_chain_identity_keeps_shared_original_output(self):
        before, plan, _, _ = explicit_fixture()
        after = deepcopy(before)
        for op in plan['operations']:
            for index, stage in enumerate(op['stages']):
                name = stage['instance']; box=stage['footprint_dbu']
                after['instances'][name] = dict(cell=stage['cell'],macro=False,bbox_dbu=box[:],bbox=box[:])
                net = after['nets'][op['net'] if index==0 else op['stages'][index-1]['new_net']]
                receiver = next(t for t in net['terminals'] if t['instance']+'/'+t['pin']==op['receiver'])
                net['terminals'].remove(receiver)
                net['terminals'].append(dict(instance=name,pin='A',direction='INPUT'))
                after['nets'][stage['new_net']] = dict(type='SIGNAL',ports=[],terminals=[
                    dict(instance=name,pin='X',direction='OUTPUT'),receiver])
        proof = dict(added_instances=[s['instance'] for op in plan['operations'] for s in op['stages']])
        validate_exact_edit(plan,before,after,proof)
        self.assertEqual(after['nets']['n']['ports'],['output'])
        after['nets']['path_0_1_net']['terminals'][-1]['pin']='CLK'
        with self.assertRaises(ValueError):validate_exact_edit(plan,before,after,proof)

    def test_quantitative_gate_requires_each_internal_chain_net(self):
        args=acceptance.fixture()
        args[3]['operations'][0] = dict(net='n',stages=[dict(new_net='branch'),dict(new_net='second')])
        with self.assertRaises(ValueError):qualify_candidate(*args)
        record=deepcopy(args[2]['connections'][1]);record['net']='second'
        args[2]['connections'].append(record)
        for corner in args[4]:args[4][corner]['second']=deepcopy(args[4][corner]['branch'])
        self.assertTrue(qualify_candidate(*args)['quantitative_gates_passed'])
        args[4]['slow']['second']['slew'].update(actual=.45,slack=.05)
        self.assertFalse(qualify_candidate(*args)['quantitative_gates_passed'])


if __name__ == '__main__':
    unittest.main()
