"""Physical policy failures must be rejected before spending a routing run."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from physical_organization_edits import validate_plan, measurement_plan
from physical_buffer_repair import compare_buffer_repair
from physical_route_intake import validate_repair_route
from validation_run import sha
import test_physical_organization as organization
import test_physical_added_route as added_route


def fixture():
    context = organization.fixture()[0]
    for inst in context['instances'].values():
        inst['orientation'] = 'R0'
    policy = dict(schema=1,source_database_sha256='frozen',protected_instances=['s'],
        resize_cells=['sg13cmos5l_buf_2'],receiver_cells=['sg13cmos5l_buf_1'],
        receiver_pins=[],site_pitch_dbu=1,relocations={
            'a':dict(cell='sg13cmos5l_buf_2',max_displacement_sites=2,row='same',orientation='same')})
    plan = dict(schema=1,source_database=dict(path='source.odb',sha256='frozen'),added_area_um2=2,
        operations=[dict(kind='resize_buffer',instance='a',before=deepcopy(context['instances']['a']),
            cell='sg13cmos5l_buf_2',footprint_dbu=[0,4,3,6],net='left')])
    return plan,context,policy


def exchanges():
    return dict(kind='regroup_consumers',branches=[
        dict(net='left',driver='a/X',before=['x/A','y/A'],after=['u/A','v/A']),
        dict(net='right',driver='b/X',before=['u/A','v/A'],after=['x/A','y/A'])])


class DeclaredEdits(unittest.TestCase):
    def test_single_resize_needs_no_experiment_specific_count_or_receiver(self):
        plan,context,policy=fixture()
        self.assertEqual(validate_plan(plan,context,policy),dict(resized_buffers=1,
            added_buffers=0,regrouped_branches=0,added_area_um2=2))
        self.assertEqual([o['net'] for o in measurement_plan(plan,context)['operations']],['left','root'])

    def test_regrouping_is_independent_of_added_buffers(self):
        plan,context,policy=fixture();plan.update(operations=[exchanges()],added_area_um2=0)
        self.assertEqual(validate_plan(plan,context,policy)['regrouped_branches'],2)
        self.assertEqual([o['net'] for o in measurement_plan(plan,context)['operations']],['left','right'])

    def test_move_is_bounded_and_incident_parent_is_included(self):
        plan,context,policy=fixture();op=plan['operations'][0]
        op.update(kind='move_resize_buffer',footprint_dbu=[1,4,4,6])
        self.assertEqual(validate_plan(plan,context,policy)['resized_buffers'],1)
        self.assertEqual({o['net'] for o in measurement_plan(plan,context)['operations']},{'left','root'})
        for box in ([3,4,6,6],[1,6,4,8],[1.5,4,4.5,6]):
            bad=deepcopy(plan);bad['operations'][0]['footprint_dbu']=box
            with self.subTest(box=box),self.assertRaises(ValueError):validate_plan(bad,context,policy)

    def test_wrong_source_protected_cell_and_undeclared_move_fail(self):
        for edit in ('source','protected','move','duplicate','unknown'):
            p,c,r=fixture()
            if edit=='source':p['source_database']['sha256']='other'
            if edit=='protected':r['protected_instances'].append('a')
            if edit=='move':p['operations'][0]['footprint_dbu']=[1,4,4,6]
            if edit=='duplicate':p['operations']*=2
            if edit=='unknown':p['operations'][0]['kind']='arbitrary_logic'
            with self.subTest(edit=edit),self.assertRaises(ValueError):validate_plan(p,c,r)

    def test_supply_clock_package_and_occupied_footprints_fail(self):
        for edit in ('clock','power','package','collision'):
            p,c,r=fixture()
            if edit=='clock':c['nets']['root']['type']='CLOCK'
            if edit=='power':c['nets']['root']['type']='POWER';c['nets']['left']['type']='POWER'
            if edit=='package':c['nets']['root']['ports']=['input']
            if edit=='collision':c['instances']['obstacle']=dict(cell='leaf',macro=False,bbox_dbu=[2,4,4,6])
            with self.subTest(edit=edit),self.assertRaises(ValueError):validate_plan(p,c,r)

    def test_area_cannot_be_underreported_or_nonfinite(self):
        for area in (0,1,float('nan'),float('inf'),True):
            p,c,r=fixture();p['added_area_um2']=area
            with self.subTest(area=area),self.assertRaises(ValueError):validate_plan(p,c,r)

    def test_regrouping_rejects_lost_duplicate_protected_or_cross_source_leaves(self):
        for edit in ('lost','duplicate','protected','cross_source','mixed_size'):
            p,c,r=fixture();p.update(operations=[exchanges()],added_area_um2=0)
            branches=p['operations'][0]['branches']
            if edit=='lost':branches[0]['after'].pop()
            if edit=='duplicate':branches[0]['after']=['u/A','u/A']
            if edit=='protected':r['protected_instances'].append('x')
            if edit=='mixed_size':c['instances']['b']['cell']='sg13cmos5l_buf_2'
            if edit=='cross_source':
                c['nets']['root']['terminals']=[t for t in c['nets']['root']['terminals'] if t['instance']!='b']
                c['instances']['other']=dict(cell='source',macro=False)
                c['nets']['other']=dict(type='SIGNAL',ports=[],terminals=[
                    dict(instance='other',pin='Q',direction='OUTPUT'),dict(instance='b',pin='A',direction='INPUT')])
            with self.subTest(edit=edit),self.assertRaises(ValueError):validate_plan(p,c,r)

    def test_multiple_receivers_are_legal_but_duplicate_pins_and_wrong_rails_fail(self):
        p,c,r=fixture();p['operations']=[];p['added_area_um2']=8
        c['instances']['memory']=dict(cell='memory',macro=True,bbox_dbu=[80,24,84,28])
        for i in range(2):
            pin=f'memory/A_DIN[{i}]';r['receiver_pins'].append(pin)
            c['nets']['root']['terminals'].append(dict(instance='memory',pin=f'A_DIN[{i}]',direction='INPUT'))
            p['operations'].append(dict(kind='insert_receiver',net='root',receiver=pin,
                instance=f'receiver_{i}',new_net=f'received_{i}',cell='sg13cmos5l_buf_1',
                footprint_dbu=[50+4*i,8,52+4*i,10],orientation='R0'))
        self.assertEqual(validate_plan(p,c,r)['added_buffers'],2)
        self.assertEqual(len(measurement_plan(p,c)['operations'][0]['stages']),2)
        for edit in ('duplicate','orientation','unauthorized'):
            bad=deepcopy(p)
            if edit=='duplicate':bad['operations'][1]['receiver']=bad['operations'][0]['receiver']
            if edit=='orientation':bad['operations'][0]['orientation']='MX'
            if edit=='unauthorized':r=deepcopy(r);r['receiver_pins']=[]
            with self.subTest(edit=edit),self.assertRaises(ValueError):validate_plan(bad,c,r)

    def test_pure_regroup_identity_requires_opt_in_and_rejects_wrong_source(self):
        buffer=lambda a,x:dict(type='sg13cmos5l_buf_1',parameters={},
            port_directions={'A':'input','X':'output'},connections={'A':[a],'X':[x]})
        leaf=lambda bit:dict(type='leaf',parameters={},port_directions={'A':'input'},connections={'A':[bit]})
        before=dict(ports={'in':dict(direction='input',bits=[2]),'other':dict(direction='input',bits=[3])},
            cells={'a':buffer(2,4),'b':buffer(2,5),'x':leaf(4),'y':leaf(5)})
        after=deepcopy(before);after['cells']['x']['connections']['A']=[5];after['cells']['y']['connections']['A']=[4]
        with self.assertRaises(ValueError):compare_buffer_repair(before,after,allow_resizing=True)
        self.assertTrue(compare_buffer_repair(before,after,allow_resizing=True,allow_rewiring=True)['buffer_contracted_connectivity'])
        with self.assertRaises(ValueError):compare_buffer_repair(before,before,allow_rewiring=True)
        after['cells']['b']['connections']['A']=[3]
        with self.assertRaises(ValueError):compare_buffer_repair(before,after,allow_rewiring=True)


class OrganizationAdmission(unittest.TestCase):
    def test_organization_cannot_enter_the_older_add_only_gate(self):
        with tempfile.TemporaryDirectory() as folder:
            args=added_route.AddedRoute().fixture(Path(folder));p=args['root']/'validation/report.json'
            report=json.loads(p.read_text());report['decision']='retain-locally-qualified-organization-repair-extend-shared-intake-before-whole-chip-route';p.write_text(json.dumps(report))
            s=args['selection_path'];selection=json.loads(s.read_text());selection['validation']['sha256']=sha(p);s.write_text(json.dumps(selection))
            with self.assertRaisesRegex(ValueError,'declared-edit admission gate'):validate_repair_route(**args)

    def test_new_schema_does_not_admit_an_old_receipt_as_organization(self):
        with tempfile.TemporaryDirectory() as folder:
            args=added_route.AddedRoute().fixture(Path(folder));s=args['selection_path']
            selection=json.loads(s.read_text());selection.update(schema=5,decision='admit-one-validated-organization-coarse-route');s.write_text(json.dumps(selection))
            with self.assertRaisesRegex(ValueError,'declared-edit admission gate'):validate_repair_route(**args)


if __name__=='__main__':unittest.main()
