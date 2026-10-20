#!/usr/bin/env python3
import json,tempfile,unittest,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from streaming_tt_cdl_context import compose,modules

class ContextTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.root=Path(self.tmp.name)
        self.top=self.root/'top.cdl';self.lib=self.root/'master.cdl';self.inv=self.root/'inventory.json'
        self.top.write_text('.SUBCKT top a y VPWR VGND\nXcell y a VPWR VGND buf\n.ENDS top\n')
        self.lib.write_text('.SUBCKT buf Y A VDD VSS\nM0 Y A VSS VSS nmos w=1u l=1u\n.ENDS\n')
        self.inventory=dict(top='top',public_bterms={'a':{'net':'a'},'y':{'net':'y'}},
            power_bterms={'VPWR':{'net':'VPWR'},'VGND':{'net':'VGND'}},instances={'cell':dict(master='buf',terminals={
            'A':{'net':'a'},'Y':{'net':'y'},'VDD':{'net':'VPWR'},'VSS':{'net':'VGND'}})})
        self.inv.write_text(json.dumps(self.inventory))
    def compose(self):return compose(self.top,[self.lib],self.inv,top='top')
    def test_exact_bytes_and_independent_pin_bindings(self):
        data,report=self.compose();self.assertEqual(data,self.lib.read_bytes()+b'\n'+self.top.read_bytes()+b'\n')
        self.assertEqual(report['actual_instances'],1);self.assertEqual(report['actual_terminals'],4)
        self.assertTrue(report['actual_odb_pin_order_and_net_binding_verified'])
    def test_swapped_top_pins_rejected(self):
        self.top.write_text(self.top.read_text().replace('Xcell y a','Xcell a y'))
        with self.assertRaisesRegex(ValueError,'pin order'):self.compose()
    def test_missing_actual_instance_rejected(self):
        self.inventory['instances']['extra']=self.inventory['instances']['cell'];self.inv.write_text(json.dumps(self.inventory))
        with self.assertRaisesRegex(ValueError,'omitted'):self.compose()
    def test_missing_master_rejected(self):
        self.lib.write_text(self.lib.read_text().replace('buf','other'))
        with self.assertRaisesRegex(ValueError,'master'):self.compose()
    def test_case_insensitive_duplicate_master_rejected(self):
        self.lib.write_text(self.lib.read_text()+self.lib.read_text().replace('buf','BUF'))
        with self.assertRaisesRegex(ValueError,'Duplicate'):self.compose()
    def test_external_include_refused(self):
        self.lib.write_text('.include other.cdl\n'+self.lib.read_text())
        with self.assertRaisesRegex(ValueError,'Unresolved'):self.compose()
    def test_continuation_and_ends_binding(self):
        self.assertEqual(modules('.SUBCKT m a\n+ b\n.ENDS m\n')['M']['pins'],['a','b'])
        with self.assertRaisesRegex(ValueError,'Misbound'):modules('.SUBCKT m a\n.ENDS other\n')
    def test_only_actual_public_bterm_alias_allowed(self):
        self.inventory['public_bterms']['y']['net']='net5003'
        self.inventory['instances']['cell']['terminals']['Y']['net']='net5003';self.inv.write_text(json.dumps(self.inventory))
        self.compose()
        self.top.write_text(self.top.read_text().replace('Xcell y a','Xcell invented a'))
        with self.assertRaisesRegex(ValueError,'pin order'):self.compose()
    def test_isolated_actual_unconnected_terminal(self):
        self.inventory['instances']['cell']['terminals']['Y']['net']=None;self.inv.write_text(json.dumps(self.inventory))
        self.top.write_text(self.top.read_text().replace('Xcell y a','Xcell _unconnected_0 a'))
        self.assertEqual(self.compose()[1]['isolated_unconnected_terminals'],1)
        self.top.write_text(self.top.read_text().replace('_unconnected_0','a'))
        with self.assertRaisesRegex(ValueError,'joined/reused'):self.compose()
    def test_unknown_used_child_rejected(self):
        self.lib.write_text(self.lib.read_text().replace('M0 Y A VSS VSS nmos w=1u l=1u','Xchild Y A VDD VSS missing'))
        with self.assertRaisesRegex(ValueError,'Unresolved used child'):self.compose()
    def test_wrong_used_child_arity_rejected(self):
        self.lib.write_text(self.lib.read_text().replace('M0 Y A VSS VSS nmos w=1u l=1u','Xchild Y / child')+
            '.SUBCKT child Y A\nM0 Y A Y Y nmos w=1u l=1u\n.ENDS\n')
        with self.assertRaisesRegex(ValueError,'arity'):self.compose()
    def test_unused_mos_does_not_qualify_empty_used_master(self):
        self.lib.write_text('.SUBCKT buf Y A VDD VSS\n.ENDS\n.SUBCKT unused Y A\nM0 Y A Y Y nmos\n.ENDS\n')
        with self.assertRaisesRegex(ValueError,'Used reachable'):self.compose()
    def test_used_master_cycle_rejected(self):
        self.lib.write_text(self.lib.read_text().replace('M0 Y A VSS VSS nmos w=1u l=1u','Xchild Y A VDD VSS buf'))
        with self.assertRaisesRegex(ValueError,'Cycle'):self.compose()
    def test_casefold_net_collision_rejected(self):
        self.inventory['instances']['cell']['terminals']['Y']['net']='A';self.inv.write_text(json.dumps(self.inventory))
        with self.assertRaisesRegex(ValueError,'net collision'):self.compose()
    def test_public_power_key_overlap_rejected(self):
        self.inventory['power_bterms']['a']={'net':'VGND'};self.inv.write_text(json.dumps(self.inventory))
        with self.assertRaisesRegex(ValueError,'BTerm key overlap'):self.compose()
    def test_unconnected_casefold_alias_collision_rejected(self):
        self.inventory['instances']['cell']['terminals']['Y']['net']=None
        self.inventory['instances']['cell']['terminals']['A']['net']='_UNCONNECTED_0'
        self.inventory['public_bterms']['a']['net']='_UNCONNECTED_0';self.inv.write_text(json.dumps(self.inventory))
        self.top.write_text(self.top.read_text().replace('Xcell y a','Xcell _unconnected_0 a'))
        with self.assertRaisesRegex(ValueError,'joined/reused'):self.compose()

if __name__=='__main__':unittest.main()
