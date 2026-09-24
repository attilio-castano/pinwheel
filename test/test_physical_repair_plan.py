from copy import deepcopy
import sys
from pathlib import Path
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from physical_connections import Connectivity
from physical_repair_plan import build_plan,validate_plan,render_tcl
from test_physical_connections import fixture


def plan_fixture():
    c,o=fixture();g=Connectivity(c,o)
    records=[dict(g.record(n,{}),family='test') for n in ['n','u']]
    geometry=dict(buffer_masters={'sg13cmos5l_buf_8':dict(width_dbu=6,height_dbu=4)},
        pins={'d/X':[dict(bbox_dbu=[11,1,12,2])],
              'memory/A_DIN[0]':[dict(bbox_dbu=[69,10,70,11])]})
    return c,build_plan(records,c,geometry,dict(path='source.odb',sha256='frozen'))


class RepairPlan(unittest.TestCase):
    def test_fresh_namespace_preserves_previously_added_buffers(self):
        c,p=plan_fixture()
        c['instances']['prepared_signal_0']=dict(cell='sg13cmos5l_buf_8',macro=False,
            bbox=[92,0,98,4],bbox_dbu=[92,0,98,4])
        geometry=dict(buffer_masters={'sg13cmos5l_buf_8':dict(width_dbu=6,height_dbu=4)},
            pins={'d/X':[dict(bbox_dbu=[11,1,12,2])]})
        row=dict(Connectivity(*fixture()).record('n',{}),family='test')
        with self.assertRaisesRegex(ValueError,'namespace collides'):
            build_plan([row],c,geometry,dict(path='source.odb',sha256='frozen'))
        q=build_plan([row],c,geometry,dict(path='source.odb',sha256='frozen'),namespace='distribution')
        self.assertEqual(q['operations'][0]['instance'],'distribution_signal_0')
        self.assertEqual(validate_plan(q,c,'frozen')['operations'],1)
        for namespace in ['', 'bad;exit', '1bad']:
            with self.assertRaisesRegex(ValueError,'Invalid repair namespace'):
                build_plan([row],c,geometry,dict(path='source.odb',sha256='frozen'),namespace=namespace)

    def test_checked_driver_and_receiver_operations(self):
        c,p=plan_fixture();r=validate_plan(p,c,'frozen')
        self.assertEqual([o['mode'] for o in p['operations']],['driver','receiver'])
        self.assertEqual(r['operations'],2)
        self.assertEqual(r['added_area_um2'],48)
        self.assertEqual(p['invariants']['added_pipeline_cycles'],0)
        self.assertFalse(p['acceptance']['detailed_route_admitted'])

    def test_stale_checkpoint_or_consumers_rejected(self):
        c,p=plan_fixture()
        with self.assertRaises(ValueError):validate_plan(p,c,'changed')
        for change in [lambda p:p['operations'][0]['consumers'].clear(),
                       lambda p:p['operations'][0]['ports'].clear(),
                       lambda p:p['operations'][0].update(driver_cell='sg13cmos5l_buf_8')]:
            q=deepcopy(p);change(q)
            with self.assertRaises(ValueError):validate_plan(q,c,'frozen')

    def test_occupied_or_changed_footprint_rejected(self):
        c,p=plan_fixture()
        for box in [[0,0,6,4],[0,0,1,1],[0,40,6,44],[0.,4,6,8]]:
            q=deepcopy(p);q['operations'][0]['footprint_dbu']=box
            with self.assertRaises(ValueError):validate_plan(q,c,'frozen')

    def test_state_clock_policy_and_gate_relaxation_rejected(self):
        c,p=plan_fixture()
        for change in [lambda p:p['invariants'].update(added_pipeline_cycles=1),
                       lambda p:p['acceptance'].update(all_corner_electrical_zero=False),
                       lambda p:p['routing_policy'].update(capacity_adjustment=.5),
                       lambda p:p['operations'].clear()]:
            q=deepcopy(p);change(q)
            with self.assertRaises(ValueError):validate_plan(q,c,'frozen')

    def test_collision_unknown_operation_and_bad_receiver_rejected(self):
        c,p=plan_fixture()
        for change in [dict(instance='d'),dict(new_net='src'),dict(cell='inverter'),
                       dict(mode='resize'),dict(receiver='q/D'),dict(net='n}; exit')]:
            q=deepcopy(p);q['operations'][1].update(change)
            with self.assertRaises(ValueError):validate_plan(q,c,'frozen')
        q=deepcopy(p);q['operations'].append(deepcopy(q['operations'][0]))
        with self.assertRaises(ValueError):validate_plan(q,c,'frozen')

    def test_compiled_recipe_preserves_existing_cells_and_checks_all_consumers(self):
        c,p=plan_fixture();t=render_tcl(p,c,'frozen')
        self.assertIn('Changed consumer set',t)
        self.assertIn('Changed package consumers',t)
        self.assertIn('[$inst findITerm A] connect $wire',t)
        self.assertIn('[$inst findITerm A] connect $branch',t)
        self.assertIn('$inst setPlacementStatus FIRM',t)
        self.assertNotIn('destroy',t)
        self.assertNotIn('detailed_route',t)


if __name__=='__main__':unittest.main()
