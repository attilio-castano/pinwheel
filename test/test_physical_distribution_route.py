from copy import deepcopy
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from physical_distribution_route import validate_exact_edit
from physical_route_intake import validate_repair_route
from test_physical_repair_plan import plan_fixture
import test_physical_added_route_chain as chain


def applied():
    before,plan=plan_fixture();after=deepcopy(before)
    def net(driver,consumers,ports):
        terms=[(*driver.rsplit('/',1),'OUTPUT')]+[(*p.rsplit('/',1),'INPUT') for p in consumers]
        return dict(type='SIGNAL',ports=ports[:],terminals=[dict(instance=i,pin=p,direction=d) for i,p,d in terms])
    for op in plan['operations']:
        i=op['instance'];box=op['footprint_dbu']
        after['instances'][i]=dict(cell=op['cell'],macro=False,bbox=box[:],bbox_dbu=box[:])
        if op['mode']=='driver':
            after['nets'][op['net']]=net(i+'/X',op['consumers'],op['ports'])
            after['nets'][op['new_net']]=net(op['driver'],[i+'/A'],[])
        else:
            after['nets'][op['net']]=net(op['driver'],[p for p in op['consumers'] if p!=op['receiver']]+[i+'/A'],op['ports'])
            after['nets'][op['new_net']]=net(i+'/X',[op['receiver']],[])
    proof=dict(added_instances=[op['instance'] for op in plan['operations']])
    return plan,before,after,proof


class DistributionRoute(unittest.TestCase):
    def test_exact_driver_and_receiver_edit(self):
        validate_exact_edit(*applied())

    def test_wrong_buffer_or_independent_proof_fails(self):
        for mutate in [lambda a:a[3]['added_instances'].pop(),
                       lambda a:a[2]['instances'][a[0]['operations'][0]['instance']].update(cell='sg13cmos5l_buf_1')]:
            a=list(applied());mutate(a)
            with self.assertRaises(ValueError):validate_exact_edit(*a)

    def test_changed_unrelated_clock_or_signal_fails(self):
        a=list(applied());a[2]['nets']['src']['ports']=['different']
        with self.assertRaisesRegex(ValueError,'unrelated'):validate_exact_edit(*a)

    def test_illegal_placement_is_not_a_plan_hint(self):
        for box in [[0,0,6,4],[0,42,6,46]]:
            a=list(applied());a[2]['instances'][a[0]['operations'][0]['instance']]['bbox_dbu']=box
            with self.assertRaisesRegex(ValueError,'footprint'):validate_exact_edit(*a)

    def test_wrong_consumer_and_missing_port_fail(self):
        for mutate in [lambda a:a[2]['nets']['n']['terminals'].pop(),lambda a:a[2]['nets']['n']['ports'].clear()]:
            a=list(applied());mutate(a)
            with self.assertRaisesRegex(ValueError,'consumers'):validate_exact_edit(*a)

    def test_new_receipt_type_cannot_skip_distribution_gate(self):
        with tempfile.TemporaryDirectory() as folder:
            fixture=chain.ChainedRoute();args=fixture.fixture(Path(folder))
            fixture.edit(args,'validation/report.json',lambda d:d.update(
                decision='retain-qualified-local-distribution-repair-diagnose-congestion-before-route-intake',
                local_distribution_contract_pass=False))
            with self.assertRaisesRegex(ValueError,'local contract pass'):validate_repair_route(**args)


if __name__=='__main__':unittest.main()
