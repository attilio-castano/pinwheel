"""A physical copy must preserve state, exact gate inputs and all other wiring."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'scripts'))
from physical_decoder_replication import compare_readback, validate_plan, verify_context, render_tcl
from physical_organization_edits import FIXED


def mapped():
    def cell(kind, directions, **connections):
        return dict(type=kind, parameters={}, port_directions=directions,
                    connections={p:[b] for p,b in connections.items()})
    before = dict(ports={'a':dict(direction='input',bits=[2]), 'b':dict(direction='input',bits=[3]),
                         'out':dict(direction='output',bits=[6,7])}, cells={
        'gate':cell('sg13cmos5l_xor2_1', {'A':'input','B':'input','X':'output'}, A=2,B=3,X=4),
        'first':cell('ff', {'D':'input','CLK':'input','Q':'output'}, D=4,CLK=2,Q=6),
        'second':cell('ff', {'D':'input','CLK':'input','Q':'output'}, D=4,CLK=2,Q=7)})
    after = deepcopy(before)
    after['cells']['copy'] = deepcopy(after['cells']['gate'])
    after['cells']['copy']['connections']['X'] = [8]
    after['cells']['second']['connections']['D'] = [8]
    return before,after,[dict(instance='copy',source='gate')]


def physical():
    c = dict(database_sha256='frozen', dbu_per_micron=1, instances={}, nets={}, macro_pins=[])
    c.update({k:[] for k in FIXED})
    for n,x in [('gate',0),('parent_a',5),('parent_b',10),('first',15),('second',20)]:
        c['instances'][n] = dict(cell='sg13cmos5l_xor2_1' if n=='gate' else 'other',
            macro=False, bbox_dbu=[x,0,x+2,2], bbox=[x,0,x+2,2], orientation='R0')
    term = lambda n,p,d:dict(instance=n,pin=p,direction=d)
    c['nets'] = {
        'a':dict(type='SIGNAL',ports=[],terminals=[term('parent_a','Q','OUTPUT'),term('gate','A','INPUT')]),
        'b':dict(type='SIGNAL',ports=[],terminals=[term('parent_b','Q','OUTPUT'),term('gate','B','INPUT')]),
        'result':dict(type='SIGNAL',ports=[],terminals=[term('gate','X','OUTPUT'),term('first','D','INPUT'),term('second','D','INPUT')]),
        'VPWR':dict(type='POWER',ports=[],terminals=[]), 'VGND':dict(type='GROUND',ports=[],terminals=[])}
    c['rows'] = [dict(bbox_dbu=[0,0,100,2])]
    p = dict(schema=1,source_database_sha256='frozen',site_pitch_dbu=1,added_area_um2=4,
        copies=[dict(source='gate',instance='copy',new_net='regional',consumers=['second/D'],
                     footprint_dbu=[30,0,32,2],orientation='R0')])
    a = deepcopy(c)
    a['instances']['copy'] = dict(cell='sg13cmos5l_xor2_1',macro=False,bbox_dbu=[30,0,32,2],bbox=[30,0,32,2],orientation='R0')
    for n,pin in [('a','A'),('b','B')]: a['nets'][n]['terminals'].append(term('copy',pin,'INPUT'))
    a['nets']['result']['terminals'].pop()
    a['nets']['regional'] = dict(type='SIGNAL',ports=[],terminals=[term('copy','X','OUTPUT'),term('second','D','INPUT')])
    for n,pin in [('VPWR','VDD'),('VGND','VSS')]: a['nets'][n]['terminals'].append(term('copy',pin,'INOUT'))
    return p,c,a


class DecoderReadback(unittest.TestCase):
    def test_same_function_with_disjoint_consumers(self):
        b,a,c=mapped()
        self.assertTrue(compare_readback(b,a,c)['exact_folded_connectivity'])

    def test_serialization_bit_numbers_are_irrelevant(self):
        b,a,c=mapped()
        for port in a['ports'].values(): port['bits']=[v+100 for v in port['bits']]
        for cell in a['cells'].values():
            cell['connections']={p:[v+100 for v in bits] for p,bits in cell['connections'].items()}
        self.assertTrue(compare_readback(b,a,c)['exact_folded_connectivity'])

    def test_input_change_or_swapping_cannot_hide_in_copy(self):
        for pin,value in [('A',3),('B',2),('A','x')]:
            b,a,c=mapped();a['cells']['copy']['connections'][pin]=[value]
            with self.subTest(pin=pin,value=value),self.assertRaises(ValueError):compare_readback(b,a,c)

    def test_state_clock_package_and_original_parameters_are_retained(self):
        for kind in ('clock','data','package','parameter','type','missing'):
            b,a,c=mapped()
            if kind=='clock':a['cells']['first']['connections']['CLK']=[3]
            if kind=='data':a['cells']['first']['connections']['D']=[3]
            if kind=='package':a['ports']['out']['bits'].reverse()
            if kind=='parameter':a['cells']['first']['parameters']['INIT']='1'
            if kind=='type':a['cells']['first']['type']='other_ff'
            if kind=='missing':del a['cells']['first']
            with self.subTest(kind=kind),self.assertRaises(ValueError):compare_readback(b,a,c)

    def test_shorted_output_and_extra_driver_fail(self):
        for bit in (2,4,6):
            b,a,c=mapped();a['cells']['copy']['connections']['X']=[bit]
            with self.subTest(bit=bit),self.assertRaises(ValueError):compare_readback(b,a,c)

    def test_noncombinational_or_wrong_function_copy_fails(self):
        for kind in ('ff','sg13cmos5l_nor2_1','sg13cmos5l_buf_1'):
            b,a,c=mapped();a['cells']['copy']['type']=kind
            with self.subTest(kind=kind),self.assertRaises(ValueError):compare_readback(b,a,c)

    def test_missing_copy_and_floating_original_fail(self):
        b,a,c=mapped()
        with self.assertRaises(ValueError):compare_readback(b,b,c)
        a['cells']['first']['connections']['D']=[99]
        with self.assertRaises(ValueError):compare_readback(b,a,c)

    def test_shared_input_buffer_preserves_behavior(self):
        b,a,c=mapped()
        a['cells']['branch']=dict(type='sg13cmos5l_buf_1',parameters={},
            port_directions={'A':'input','X':'output'},connections={'A':[2],'X':[9]})
        for name in ('gate','copy'):a['cells'][name]['connections']['A']=[9]
        buffers=[dict(instance='branch',cell='sg13cmos5l_buf_1')]
        result=compare_readback(b,a,c,buffers)
        self.assertTrue(result['input_distribution']['buffer_contracted_connectivity'])
        for error in ('wrong_parent','cycle','wrong_copy','unlisted'):
            bad=deepcopy(a)
            if error=='wrong_parent':bad['cells']['branch']['connections']['A']=[3]
            if error=='cycle':bad['cells']['branch']['connections']['A']=[9]
            if error=='wrong_copy':bad['cells']['copy']['connections']['A']=[2]
            if error=='unlisted':bad['cells']['extra']=deepcopy(bad['cells']['branch'])
            with self.subTest(error=error),self.assertRaises(ValueError):compare_readback(b,bad,c,buffers)


class DecoderPhysical(unittest.TestCase):
    def test_exact_plan_and_context(self):
        p,b,a=physical()
        self.assertEqual(validate_plan(p,b)['added_area_um2'],4)
        self.assertTrue(verify_context(p,b,a)['clock_connections_unchanged'])
        render_tcl(p,b,'/probe/local')

    def test_complete_partition_and_unique_membership(self):
        for consumers in ([],['first/D','second/D'],['second/D','second/D'],['missing/D']):
            p,b,a=physical();p['copies'][0]['consumers']=consumers
            with self.subTest(consumers=consumers),self.assertRaises(ValueError):validate_plan(p,b)

    def test_geometry_area_and_provenance_rejections(self):
        for kind in ('source','area','nan','overlap','size','off_row','rail','injection','state'):
            p,b,a=physical();op=p['copies'][0]
            if kind=='source':p['source_database_sha256']='other'
            if kind=='area':p['added_area_um2']=0
            if kind=='nan':p['added_area_um2']=float('nan')
            if kind=='overlap':op['footprint_dbu']=[0,0,2,2]
            if kind=='size':op['footprint_dbu']=[30,0,34,2]
            if kind=='off_row':op['footprint_dbu']=[30,1,32,3]
            if kind=='rail':op['orientation']='MX'
            if kind=='injection':op['instance']='a;exit'
            if kind=='state':b['instances']['gate']['cell']='ff'
            with self.subTest(kind=kind),self.assertRaises(ValueError):validate_plan(p,b)

    def test_signal_and_power_changes_in_actual_database_fail(self):
        for kind in ('upstream','clock','power','placement','geometry','extra'):
            p,b,a=physical()
            if kind=='upstream':a['nets']['a']['terminals'][-1]['pin']='B'
            if kind=='clock':a['nets']['b']['type']='CLOCK'
            if kind=='power':a['nets']['VPWR']['terminals']=[]
            if kind=='placement':a['instances']['gate']['orientation']='MX'
            if kind=='geometry':a['rows']=[]
            if kind=='extra':a['instances']['unexpected']=deepcopy(a['instances']['gate'])
            with self.subTest(kind=kind),self.assertRaises(ValueError):verify_context(p,b,a)

    def test_source_clocks_ports_and_supply_are_not_editable(self):
        for kind in ('clock','port','power','feedback'):
            p,b,a=physical()
            if kind=='clock':b['nets']['a']['type']='CLOCK'
            if kind=='power':b['nets']['a']['type']='POWER'
            if kind=='port':b['nets']['a']['ports']=['input']
            if kind=='feedback':
                b['nets']['result']['terminals'].append(b['nets']['a']['terminals'].pop())
            with self.subTest(kind=kind),self.assertRaises(ValueError):validate_plan(p,b)

    def test_input_buffer_targets_both_gate_inputs_and_keeps_original_sites(self):
        p,b,a=physical()
        existing=dict(cell='sg13cmos5l_buf_1',macro=False,bbox_dbu=[40,0,42,2],bbox=[40,0,42,2],orientation='R0')
        b['instances']['existing']=deepcopy(existing);a['instances']['existing']=deepcopy(existing)
        op=dict(source='gate',pin='A',parent='a',instance='branch',new_net='shared',
            cell='sg13cmos5l_buf_1',footprint_dbu=[35,0,37,2],orientation='R0')
        p['input_buffers']=[op];p['added_area_um2']=8
        a['instances']['branch']=dict(existing,bbox_dbu=[35,0,37,2],bbox=[35,0,37,2])
        term=lambda n,p,d:dict(instance=n,pin=p,direction=d)
        a['nets']['a']['terminals']=[term('parent_a','Q','OUTPUT'),term('branch','A','INPUT')]
        a['nets']['shared']=dict(type='SIGNAL',ports=[],terminals=[term('branch','X','OUTPUT'),term('gate','A','INPUT'),term('copy','A','INPUT')])
        for n,pin in [('VPWR','VDD'),('VGND','VSS')]:a['nets'][n]['terminals'].append(term('branch',pin,'INOUT'))
        self.assertEqual(verify_context(p,b,a)['input_buffers'],1)
        render_tcl(p,b,'/probe/buffered')
        for error in ('wrong_parent','duplicate','overlap','unknown_gate','wrong_cell','output'):
            bad=deepcopy(p);change=bad['input_buffers'][0]
            if error=='wrong_parent':change['parent']='b'
            if error=='duplicate':bad['input_buffers']*=2
            if error=='overlap':change['footprint_dbu']=[30,0,32,2]
            if error=='unknown_gate':change['source']='first'
            if error=='wrong_cell':change['cell']='sg13cmos5l_xor2_1'
            if error=='output':change['pin']='X'
            with self.subTest(error=error),self.assertRaises(ValueError):validate_plan(bad,b)
        a['nets']['shared']['terminals'].pop()
        with self.assertRaises(ValueError):verify_context(p,b,a)


if __name__ == '__main__': unittest.main()
